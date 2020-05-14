use rand::thread_rng;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use crate::toolbox::{SchnorrCS, TranscriptProtocol};
use crate::{BatchableProof, CompactProof, Transcript, ProofError};
use crate::toolbox::shamir_secrets::SecretShare;
use std::iter;

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
}

/// A secret variable used during proving.
#[derive(Copy, Clone)]
pub struct ScalarVar(usize);

/// A public variable used during proving.
#[derive(Copy, Clone)]
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
        }
    }

    /// Allocate and assign a secret variable with the given `label`.
    pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: Option<Scalar>) -> ScalarVar {
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
        let compressed = self.transcript.append_point_var(label, &assignment);
        self.points.push(assignment);
        self.point_labels.push(label);
        (PointVar(self.points.len() - 1), compressed)
    }

    /// The compact and batchable proofs differ only by which data they store.
    fn prove_impl(self) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<CompressedRistretto>), ProofError> {
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
        let mut fakeResponses = Vec::with_capacity(self.constraints.iter().map(|cs| &cs.1).count());
        let mut shares = Vec::with_capacity(self.constraints.len());
        let mut prev_clause_nr = 0;
        for (clause_nr, lhs_var, rhs_lc) in &self.constraints {
            let commitment = match blindings[(rhs_lc[0].0).0].is_some() {
                true => {
                    if prev_clause_nr == 0 {
                        prev_clause_nr = *clause_nr;
                    }
                    if prev_clause_nr != *clause_nr {
                        return Err(ProofError::InputMismatch);
                    }
                    shares.push(None);
                    RistrettoPoint::multiscalar_mul(
                        rhs_lc.iter().map(|(sc_var, _pt_var)| {
                            fakeResponses.push(None);
                            blindings[sc_var.0].unwrap()
                        }),
                        rhs_lc.iter().map(|(_sc_var, pt_var)| self.points[pt_var.0]),
                    )
                }
                false => {
                    let challenge = Scalar::random(&mut transcript_rng);
                    shares.push(Some(challenge));
                    RistrettoPoint::multiscalar_mul(
                        rhs_lc.iter()
                            .map(|(_sc_var, _pt_var)| {
                                let response = Scalar::random(&mut transcript_rng);
                                fakeResponses.push(Some(response));
                                response
                            })
                            .chain(iter::once(-&challenge)),
                        rhs_lc.iter()
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

        // Obtain a scalar challenge and compute responses
        let challenge = self.transcript.get_challenge(b"chal");
        let challenges = SecretShare::complete(challenge, &mut shares).unwrap();
        let responses = self.scalars.iter().zip(blindings)
            .zip(fakeResponses)
            .zip(&challenges.shares[1..])
            .map(|(scBlResp, ch)| {
                match scBlResp.1.is_some() {
                    true => scBlResp.1.unwrap(),
                    false => (scBlResp.0).0.unwrap() * ch + (scBlResp.0).1.unwrap()
                }
            })
            .collect::<Vec<Scalar>>();
        Ok((challenges.shares, responses, commitments))
    }

    /// Consume this prover to produce a compact proof.
    pub fn prove_compact(self) -> Result<CompactProof, ProofError> {
        let result = self.prove_impl();
        let (challenges, responses, _) = match result.is_ok() {
            true => result.unwrap(),
            false => return Err(result.err().unwrap())
        };

        Ok(CompactProof {
            challenges,
            responses,
        })
    }

    /// Consume this prover to produce a batchable proof.
    pub fn prove_batchable(self) -> Result<BatchableProof, ProofError> {
        let result = self.prove_impl();
        let (_, responses, commitments) = match result.is_ok() {
            true => result.unwrap(),
            false => return Err(result.err().unwrap())
        };

        Ok(BatchableProof {
            commitments,
            responses,
        })
    }
}

impl<'a> SchnorrCS for Prover<'a> {
    type ScalarVar = ScalarVar;
    type PointVar = PointVar;

    fn constrain(&mut self, clause_nr: usize, lhs: PointVar, linear_combination: Vec<(ScalarVar, PointVar)>) {
        self.constraints.push((clause_nr, lhs, linear_combination));
    }
}
