use rand::thread_rng;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use crate::toolbox::{SchnorrCS, TranscriptProtocol, IsSigmaProtocol};
use crate::{BatchableProof, CompactProof, Transcript, ProofError};
use crate::toolbox::shamir_secrets::SecretShare;
use std::iter;
use std::str;
use log::{trace, debug, info, warn};

/// Used to create proofs.
///
/// To use a [`Prover`], first construct one using [`Prover::new()`],
/// supplying a domain separation label, as well as the transcript to
/// operate on.
///
/// Then, allocate and assign secret ([`Prover::allocate_scalar`]) and
/// public ([`Prover::allocate_point`]) variables, and use those
/// variables to define the proof statements.
///
/// Finally, use [`Prover::prove_compact`] or
/// [`Prover::prove_batchable`] to consume the prover and produce a
/// proof.
pub struct Prover<'a> {
    transcript: &'a mut Transcript,
    scalars: Vec<Option<Scalar>>,
    points: Vec<RistrettoPoint>,
    point_labels: Vec<&'static [u8]>,
    constraints: Vec<(usize, PointVar, Vec<(ScalarVar, PointVar)>)>,
    subroutines: Vec<Prover<'a>>,

    proof: BatchableProof,

    //internals
    commitments: Vec<CompressedRistretto>,
    blindings: Vec<Option<Scalar>>,
    fake_responses: Vec<Option<Scalar>>,
    known_chal_shares: Vec<Option<Scalar>>,
    nr_clauses: usize,
    challenge: Scalar,
}

/// A secret variable used during proving.
#[derive(Copy, Clone, Debug)]
pub struct ScalarVar(usize);

/// A public variable used during proving.
#[derive(Copy, Clone, Debug)]
pub struct PointVar(usize);

impl<'a> Prover<'a> {
    /// Construct a new prover.  The `proof_label` disambiguates proof
    /// statements.
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript) -> Self {
        transcript.domain_sep(proof_label);
        Prover {
            transcript,
            scalars: Vec::default(),
            points: Vec::default(),
            point_labels: Vec::default(),
            constraints: Vec::default(),
            subroutines: Vec::default(),
            proof: BatchableProof::default(),
            commitments: Vec::default(),
            blindings: Vec::default(),
            fake_responses: Vec::default(),
            known_chal_shares: Vec::default(),
            nr_clauses: 0,
            challenge: Default::default()
        }
    }

    /// Allocate and assign a secret variable with the given `label`.  It returns the index of this new ScalarVar in the scalars Vector.
    pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: Option<Scalar>) -> ScalarVar {
        trace!("Allocating scalar {}", str::from_utf8(label).unwrap());
        self.transcript.append_scalar_var(label);
        self.scalars.push(assignment);
        ScalarVar(self.scalars.len() - 1)
    }

    /// Allocate and assign a public variable with the given `label`.
    ///
    /// The point is compressed to be appended to the transcript, and
    /// the compressed point is returned to allow reusing the result
    /// of that computation; it can be safely discarded.
    pub fn allocate_point(
        &mut self,
        label: &'static [u8],
        assignment: RistrettoPoint,
    ) -> (PointVar, CompressedRistretto) {
        trace!("Allocating point {}", str::from_utf8(label).unwrap());
        let compressed = self.transcript.append_point_var(label, &assignment);
        self.points.push(assignment);
        self.point_labels.push(label);
        (PointVar(self.points.len() - 1), compressed)
    }

    /// The compact and batchable proofs differ only by which data they store.
    fn prove_impl(mut self) -> Result<BatchableProof, ProofError> {
        self.nr_clauses = match self.constraints.last() {
            None => 0,
            Some(x) => x.0,
        };
        let result = self.commit();
        if result.is_err() {
            return Err(result.err().unwrap());
        };

        // Obtain a scalar challenge and compute responses
        self.challenge();
        self.response();
        Ok(self.proof)
    }

    /// Consume this prover to produce a compact proof.
    pub fn prove_compact(self) -> Result<CompactProof, ProofError> {
        let result = self.prove_impl();
        let proof = match result.is_ok() {
            true => result.unwrap(),
            false => return Err(result.err().unwrap())
        };

        Ok(CompactProof {
            challenges: proof.challenges,
            responses: proof.responses,
        })
    }

    /// Consume this prover to produce a batchable proof.
    pub fn prove_batchable(self) -> Result<BatchableProof, ProofError> {
        let result = self.prove_impl();
        let proof = match result.is_ok() {
            true => result.unwrap(),
            false => return Err(result.err().unwrap())
        };

        Ok(proof)
    }
}

impl<'a> IsSigmaProtocol for Prover<'a> {
    type Proof = BatchableProof;

    fn commit(&mut self) -> Result<(), ProofError> {
        // Construct a TranscriptRng
        let mut rng_builder = self.transcript.build_rng();
        for scalar in &self.scalars {
            if scalar.is_some() {
                rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.unwrap().as_bytes());
            }
        }
        let mut transcript_rng = rng_builder.finalize(&mut thread_rng());

        // Generate a blinding factor for each secret variable
        let blindings = self
            .scalars
            .iter()
            .map(|scalar| {
                return match scalar.is_some() {
                    true => Some(Scalar::random(&mut transcript_rng)),
                    false => None
                };
            })
            .collect::<Vec<Option<Scalar>>>();

        // Commit to each blinded LHS
        let mut commitments = Vec::with_capacity(self.constraints.len());
        let mut fake_responses = Vec::with_capacity(self.constraints.iter().map(|cs| &cs.1).count());
        let mut shares = Vec::with_capacity(self.constraints.len());
        let mut clause_tracker = vec![None; self.nr_clauses+1];
        // let mut prev_clause_nr = 0;
        for (clause_nr, lhs_var, rhs_lin_combo) in &self.constraints {
            let lc = rhs_lin_combo.iter().map(|(scal, pt)| format!("{} ^ {:?}", str::from_utf8(self.point_labels[pt.0]).unwrap(), scal.0) ).collect::<Vec<String>>().join(" * ");
            debug!("Constraint clause {}: {} = {}",
                clause_nr,
                str::from_utf8(self.point_labels[lhs_var.0]).unwrap(),
                lc);

            // The first [0] picks the first entry in the linear combination.  We can test against only this one because we
            // know that all entries in a compound && clause (represented by a single constraint) MUST either be all known, or
            // all unknown.  Though, we should have a way of checking this in the code before execution reaches this point.
            // The second .0 pulls out the ScalarVar which the PointVar is to be raised to.  The third .0 selects the single entry
            // of the ScalarVar tuple, which is a usize representing the index of the ScalarVar's value in self.scalars and self.blindings.
            let sv_index = (rhs_lin_combo[0].0).0;
            let commitment = match blindings[sv_index].is_some() {
                true => {               // if we have a blinding, that means we have a secret value for this variable
                    match clause_tracker[*clause_nr] {
                        // this is the first time we've worked with this clause, initialize the tracker
                        None => clause_tracker[*clause_nr] = Some(true),

                        // Check to make sure the fact we have a blinding is consistent with other parts of this clause
                        Some(isProving) => {
                            if !isProving {
                                return Err(ProofError::KeysMismatch)
                            }
                        }
                    }

                    shares.push(None);
                    RistrettoPoint::multiscalar_mul(
                        rhs_lin_combo.iter().map(|(sc_var, _pt_var)| {
                            fake_responses.push(None);
                            blindings[sc_var.0].unwrap()
                        }),
                        rhs_lin_combo.iter().map(|(_sc_var, pt_var)| {
                            self.points[pt_var.0]
                        }),
                    )
                }
                false => {              // if we don't have a blinding, we don't have a secret value and will be faking one
                    match clause_tracker[*clause_nr] {
                        // this is the first time we've worked with this clause, initialize the tracker
                        None => clause_tracker[*clause_nr] = Some(false),

                        // Check to make sure the fact we're faking it is consistent with other parts of this clause
                        Some(isProving) => {
                            if isProving {
                                return Err(ProofError::KeysMismatch)
                            }
                        },
                    }

                    let challenge = Scalar::random(&mut transcript_rng);
                    shares.push(Some(challenge));
                    RistrettoPoint::multiscalar_mul(
                        rhs_lin_combo.iter()
                            .map(|(_sc_var, _pt_var)| {
                                let response = Scalar::random(&mut transcript_rng);
                                fake_responses.push(Some(response));
                                response
                            })
                            .chain(iter::once(-&challenge)),
                        rhs_lin_combo.iter()
                            .map(|(_sc_var, pt_var)| self.points[pt_var.0])
                            .chain(iter::once(self.points[lhs_var.0])),
                    )
                }
            };

            let encoding = self
                .transcript
                .append_blinding_commitment(self.point_labels[lhs_var.0], &commitment);

            commitments.push(encoding);
        }
        self.blindings = blindings;
        self.commitments = commitments;
        self.fake_responses = fake_responses;
        self.known_chal_shares = shares;
        Ok(())
    }

    fn challenge(&mut self) {
        self.challenge = self.transcript.get_challenge(b"chal");
    }

    fn response(&mut self) {
        // Construct a TranscriptRng
        let mut rng_builder = self.transcript.build_rng();
        for scalar in &self.scalars {
            if scalar.is_some() {
                rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.unwrap().as_bytes());
            }
        }
        let mut transcript_rng = rng_builder.finalize(&mut thread_rng());

        // threshold is the number of fake_responses which are Some(), plus one to account for the secret itself
        let threshold = 1 + self.known_chal_shares.iter().filter(|r| r.is_some()).count();
        let challenges = SecretShare::complete(self.challenge, threshold, &mut self.known_chal_shares, &mut transcript_rng).unwrap();
        let blindings = &self.blindings;
        let fake_responses = &self.fake_responses;
        let responses = self.scalars.iter().zip(blindings)
            .zip(fake_responses)
            .zip(&challenges.shares)
            .map(| (((scalar, blinding), fake_response), challenge) | {
                match fake_response.is_some() {
                    true => fake_response.unwrap(),
                    false => scalar.unwrap() * challenge.unwrap() + blinding.unwrap(),
                }
            })
            .collect::<Vec<Scalar>>();

        let out_shares = challenges.shares.iter().map(|s| s.unwrap()).collect();
        let commitments = self.commitments.clone();
        self.proof = BatchableProof{
            challenges: out_shares,
            responses,
            commitments,
        };
    }
}

impl<'a> SchnorrCS for Prover<'a> {
    type ScalarVar = ScalarVar;
    type PointVar = PointVar;
    type SubroutineVar = Prover<'a>;

    fn constrain(&mut self, clause_nr: usize, lhs: PointVar, linear_combination: Vec<(ScalarVar, PointVar)>) {
        self.constraints.push((clause_nr, lhs, linear_combination));
    }

    fn add_subroutine(&mut self, subroutine: Prover<'a>) {
        self.subroutines.push(subroutine);
    }
}
