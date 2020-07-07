use rand::thread_rng;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use crate::toolbox::{SchnorrCS, TranscriptProtocol, IsSigmaProtocol, ProofType};
use crate::{BatchableProof, CompactProof, Transcript, ProofError};
use crate::toolbox::shamir::Shamir;
use crate::toolbox::xor::Xor;
use crate::toolbox::secrets::SecretSharing;
use std::iter;
use std::str;
use log::{trace, debug};

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
    proof_type: ProofType,
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
            challenge: Default::default(),
            proof_type: ProofType::Unknown,
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

        // TODO decide which type of secret sharing we're going to use
        self.proof_type = ProofType::Xor;

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

        match self.proof_type {
            ProofType::Shamir => {
                for (clause_nr, lhs_var, rhs_lin_combo) in &self.constraints {
                    debug!("Constraint clause {}: {} = {}",
                        clause_nr,
                        str::from_utf8(self.point_labels[lhs_var.0]).unwrap(),
                        rhs_lin_combo.iter().map(
                            |(scal, pt)| format!("{} ^ {:?}", str::from_utf8(self.point_labels[pt.0]).unwrap(), scal.0)
                        ).collect::<Vec<String>>().join(" * ")
                    );
        
                    // The first [0] picks the first entry in the linear combination.  We can test against only this one because we
                    // know that all entries in a compound && clause (represented by a single constraint) MUST either be all known, or
                    // all unknown.  Though, we should have a way of checking this in the code before execution reaches this point.
                    // The second .0 pulls out the ScalarVar which the PointVar is to be raised to.  The third .0 selects the single entry
                    // of the ScalarVar tuple, which is a usize representing the index of the ScalarVar's value in self.scalars and self.blindings.
                    let sv_index = (rhs_lin_combo[0].0).0;
                    let commitment = match blindings[sv_index].is_some() {
                        true => {               // if we have a blinding, that means we have a secret value for this variable
                            clause_tracker[*clause_nr] = match clause_tracker[*clause_nr] {
                                // this is the first time we've worked with this clause, initialize the tracker
                                None => Some((1, 1)),
        
                                // We're adding a new known value, so increment the tracker
                                Some((terms, filled_in)) => Some((terms+1, filled_in+1)),
                            };
        
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
                            clause_tracker[*clause_nr] = match clause_tracker[*clause_nr] {
                                // this is the first time we've worked with this clause, initialize the tracker
                                None => Some((1, 0)),
        
                                // we've added no new information here, so just count a new clause
                                Some((terms, filled_in)) => Some((terms+1, filled_in)),
                            };
        
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

                    trace!("Appending blinding {:?}", encoding);
        
                    commitments.push(encoding);
                }
                // Now that we know all the clauses, make sure at least one is full
                let mut have_one = false;
                for (i, clause) in clause_tracker.iter().enumerate() {
                    match clause {
                        Some((terms, filled_in)) => {
                            debug!("Clause {} has {} terms and we know {} keys", i, terms, filled_in);
                            if terms == filled_in { have_one = true; break; }
                        },
                        None => (),
                    }
                }
                if !have_one {
                    return Err(ProofError::InsufficientKeys)
                }
            },
            ProofType::Xor => {
                // General approach: we're going to have C clauses, each of which will have D constraints, each of which might have E terms
                // We've already generated a blinding for each possible E term
                // We need to track the D constraints so we can calculate completeness of each C
                // We should only have one fully-complete C, for which the c_i value can be calculated
                // For all other Cs except 1, we can randomize the c_i value

                // do ClauseTracker logic first, so we can trigger on it later on
                for (clause_nr, lhs_var, rhs_lin_combo) in &self.constraints {
                    debug!("Constraint clause {}: {} = {}",
                        clause_nr,
                        str::from_utf8(self.point_labels[lhs_var.0]).unwrap(),
                        rhs_lin_combo.iter().map(
                            |(scal, pt)| format!("{} ^ {:?}", str::from_utf8(self.point_labels[pt.0]).unwrap(), scal.0)
                        ).collect::<Vec<String>>().join(" * ")
                    );

                    let sv_index = (rhs_lin_combo[0].0).0;
                    match blindings[sv_index].is_some() {
                        true => {               // if we have a blinding, that means we have a secret value for this variable
                            clause_tracker[*clause_nr] = match clause_tracker[*clause_nr] {
                                // this is the first time we've worked with this clause, initialize the tracker
                                None => Some((1, 1)),
        
                                // We're adding a new known value, so increment the tracker
                                Some((terms, filled_in)) => Some((terms+1, filled_in+1)),
                            };
                        },
                        false => {
                            clause_tracker[*clause_nr] = match clause_tracker[*clause_nr] {
                                // this is the first time we've worked with this clause, initialize the tracker
                                None => Some((1, 0)),
        
                                // we've added no new information here, so just count a new clause
                                Some((terms, filled_in)) => Some((terms+1, filled_in)),
                            };
                        }
                    };
                };

                // Now that we know all the clauses, make sure at least one is full, and generate one challenge share
                // per clause (NOT per constraint!)
                let mut have_one = false;
                for (i, clause) in clause_tracker.iter().enumerate() {
                    match clause {
                        Some((terms, filled_in)) => {
                            debug!("Clause {} has {} terms and we know {} keys", i, terms, filled_in);
                            if terms == filled_in {
                                // this is a fully-known clause, so we'll be able to calculate the challenge later on
                                have_one = true;
                                shares.push(None);
                            } else {
                                // this is a faked clause, so we need to randomize a challenge for it
                                shares.push(Some(Scalar::random(&mut transcript_rng)));
                            };
                        },
                        None => (),
                    }
                }
                if !have_one {
                    return Err(ProofError::InsufficientKeys)
                }

                // Using the shares, calculate our commitments
                for (clause_nr, lhs_var, rhs_lin_combo) in &self.constraints {
                    let sv_index = (rhs_lin_combo[0].0).0;
                    let commitment = match blindings[sv_index].is_some() {
                        true => {               // if we have a blinding, that means we have a secret value for this variable        
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
                            let challenge = shares[*clause_nr - 1].unwrap();
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
                    
                    trace!("Appending blinding {:?}", encoding);
        
                    commitments.push(encoding);
                }
            },
            _ => {
                panic!("This isn't implemented yet!");
            }
        }

        debug!("Prover generated shares {:?}", shares);
        
        self.blindings = blindings;
        self.commitments = commitments;
        self.fake_responses = fake_responses;
        self.known_chal_shares = shares;
        Ok(())
    }

    fn challenge(&mut self) {
        // trace!("Prover's transcript is {:?}", self.transcript);
        self.challenge = self.transcript.get_challenge(b"chal");
        trace!("Prover's transcript challenge is {:?}", self.challenge);
    }

    fn response(&mut self) {
        let blindings = &self.blindings;
        let fake_responses = &self.fake_responses;
        let responses: Vec<Scalar>;

        // Construct a TranscriptRng
        let mut rng_builder = self.transcript.build_rng();
        for scalar in &self.scalars {
            if scalar.is_some() {
                rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.unwrap().as_bytes());
            }
        }
        let mut rng = rng_builder.finalize(&mut thread_rng());
        // let mut rng = rand::thread_rng();
        let challenges: Vec<Scalar>;

        match self.proof_type {
            ProofType::Xor => {
                let mut xor = Xor::new(&mut rng);
                let unique_challenges = xor.complete(&self.challenge, &self.known_chal_shares).unwrap();
                trace!("Unique challenges: {:?}", unique_challenges);
                challenges = self.constraints.iter().map(|(clause_nr, _, _)| {
                    unique_challenges[*clause_nr - 1]
                }).collect();

                responses = self.scalars.iter().zip(blindings)
                    .zip(fake_responses)
                    .zip(&challenges)
                    .map(| (((scalar, blinding), fake_response), challenge) | {
                        match fake_response.is_some() {
                            true => fake_response.unwrap(),
                            false => scalar.unwrap() * challenge + blinding.unwrap(),
                        }
                    })
                    .collect::<Vec<Scalar>>();
            },
            ProofType::Shamir => {
                let threshold = 1 + self.known_chal_shares.iter().filter(|r| r.is_some()).count();
                let mut sham = Shamir::new(threshold, &mut rng);
                challenges = sham.complete(&self.challenge, &self.known_chal_shares).unwrap();
                responses = self.scalars.iter().zip(blindings)
                    .zip(fake_responses)
                    .zip(&challenges)
                    .map(| (((scalar, blinding), fake_response), challenge) | {
                        match fake_response.is_some() {
                            true => fake_response.unwrap(),
                            false => scalar.unwrap() * challenge + blinding.unwrap(),
                        }
                    })
                    .collect::<Vec<Scalar>>();
            },
            _ => {
                panic!("This isn't implemented yet!");
            }
        };

        let out_shares = challenges;
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
