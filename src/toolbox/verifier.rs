use rand::{thread_rng, Rng};

use std::collections::HashMap;
use std::{iter, str};

use log::{trace, debug};

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};

use crate::toolbox::{SchnorrCS, TranscriptProtocol, ProofType};
use crate::{BatchableProof, CompactProof, ProofError, Transcript};
use crate::toolbox::shamir::Shamir;
use crate::toolbox::xor::Xor;
use crate::toolbox::secrets::SecretSharing;

/// Used to produce verification results.
///
/// To use a [`Verifier`], first construct one using [`Verifier::new()`],
/// supplying a domain separation label, as well as the transcript to
/// operate on.
///
/// Then, allocate secret ([`Verifier::allocate_scalar`]) variables
/// and allocate and assign public ([`Verifier::allocate_point`])
/// variables, and use those variables to define the proof statements.
/// Note that no assignments to secret variables are assigned, since
/// the verifier doesn't know the secrets.
///
/// Finally, use [`Verifier::verify_compact`] or
/// [`Verifier::verify_batchable`] to consume the verifier and produce
/// a verification result.
pub struct Verifier<'a> {
    transcript: &'a mut Transcript,
    num_scalars: usize,
    points: Vec<CompressedRistretto>,
    point_labels: Vec<&'static [u8]>,
    constraints: Vec<(usize, PointVar, Vec<(ScalarVar, PointVar)>)>,
    subroutines: Vec<Verifier<'a>>,
}

/// A secret variable used during verification.
///
/// Note that this variable is only a placeholder; it has no
/// assignment, because the verifier doesn't know the secrets.
#[derive(Copy, Clone)]
pub struct ScalarVar(usize);
/// A public variable used during verification.
#[derive(Copy, Clone)]
pub struct PointVar(usize);

impl<'a> Verifier<'a> {
    /// Construct a verifier for the proof statement with the given
    /// `proof_label`, operating on the given `transcript`.
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript) -> Self {
        transcript.domain_sep(proof_label);
        Verifier {
            transcript,
            num_scalars: 0,
            points: Vec::default(),
            point_labels: Vec::default(),
            constraints: Vec::default(),
            subroutines: Vec::default(),
        }
    }

    /// Allocate a placeholder scalar variable, without an assignment.
    pub fn allocate_scalar(&mut self, label: &'static [u8]) -> ScalarVar {
        trace!("Allocating scalar {}", str::from_utf8(label).unwrap());
        self.transcript.append_scalar_var(label);
        self.num_scalars += 1;
        ScalarVar(self.num_scalars - 1)
    }

    /// Attempt to allocate a point variable, or fail verification if
    /// the assignment is invalid.
    pub fn allocate_point(
        &mut self,
        label: &'static [u8],
        assignment: CompressedRistretto,
    ) -> Result<PointVar, ProofError> {
        trace!("Allocating point {}", str::from_utf8(label).unwrap());
        self.transcript
            .validate_and_append_point_var(label, &assignment)?;
        self.points.push(assignment);
        self.point_labels.push(label);
        Ok(PointVar(self.points.len() - 1))
    }

    /// Consume the verifier to produce a verification of a [`CompactProof`].
    pub fn verify_compact(self, proof: &CompactProof) -> Result<(), ProofError> {
        // Check that there are as many responses as secret variables
        if proof.responses.len() != self.num_scalars {
            return Err(ProofError::IncorrectResponseNumber);
        }

        // TODO have to decide what type of proof this is
        let proof_type = ProofType::Xor;

        // Decompress all parameters or fail verification.
        let points = self
            .points
            .iter()
            .map(|pt| pt.decompress())
            .collect::<Option<Vec<RistrettoPoint>>>()
            .ok_or(ProofError::DecompressionError)?;

        // NOTE: this is only used for the XOR-type sharing
        let mut clause_challenges: HashMap<usize, Scalar> = HashMap::new();

        for (index, (clause_nr, lhs_var, rhs_lc)) in self.constraints.iter().enumerate() {
            let c = proof.challenges[index];
            trace!("Verifier challenge for index {} is  {:?}", index, c);
            match proof_type {
                ProofType::Xor => {
                    match clause_challenges.get(clause_nr) {
                        Some(cc) => {
                            // check to make sure this challenge meets what we expect for this clause
                            if *cc != c {
                                return Err(ProofError::VerificationFailure);
                            }
                        },
                        None => {
                            clause_challenges.insert(*clause_nr, c);
                        }
                    }
                },
                _ => {}
            }

            let minus_c = -c;
            let commitment = RistrettoPoint::vartime_multiscalar_mul(
                rhs_lc
                    .iter()
                    .map(|(sc_var, _pt_var)| {
                        proof.responses[sc_var.0]
                    })
                    .chain(iter::once(minus_c)),
                rhs_lc
                    .iter()
                    .map(|(_sc_var, pt_var)| points[pt_var.0])
                    .chain(iter::once(points[lhs_var.0])),
            );
            let encoding = self.transcript
                .append_blinding_commitment(self.point_labels[lhs_var.0], &commitment);
            trace!("Appending blinding {:?}", encoding);
        }

        let rec_challenge = match proof_type {
            ProofType::Shamir => {
                let threshold = (self.constraints.len() - 1) * self.constraints[0].2.len() + 1;
                let mut sham = Shamir::new_without_rng(threshold);
                sham.reconstruct(&proof.challenges)
            },
            ProofType::Xor => {
                let mut xor = Xor::new_without_rng();
                // we only have a challenge per clause, not constraint, so we have to find only the unique challenges
                let challenges = clause_challenges.values().map(|s| *s).collect();
                xor.reconstruct(&challenges)
            },
            _ => {
                panic!("This isn't implemented yet!");
            }
        };

        let challenge = self.transcript.get_challenge(b"chal");
        debug!("Verifier's transcript challenge is {:?}", challenge);

        if rec_challenge.is_ok() && challenge == rec_challenge.unwrap() {
            Ok(())
        } else {
            Err(ProofError::VerificationFailure)
        }
    }

    /// Consume the verifier to produce a verification of a [`BatchableProof`].
    pub fn verify_batchable(self, proof: &BatchableProof) -> Result<(), ProofError> {
        // Check that there are as many responses as secret variables
        if proof.responses.len() != self.num_scalars {
            return Err(ProofError::IncorrectResponseNumber);
        }
        // Check that there are as many commitments as constraints
        if proof.commitments.len() != self.constraints.len() {
            return Err(ProofError::VerificationFailure);
        }

        // TODO automatic decision of what proof type to verify
        let proof_type = ProofType::Xor;

        // NOTE: this is only used for XOR-style sharing
        let mut clause_challenges: HashMap<usize, Scalar> = HashMap::new();
        for (i, commitment) in proof.commitments.iter().enumerate() {
            let (ref clause_nr, ref lhs_var, ref _rhs_lc) = self.constraints[i];
            self.transcript.validate_and_append_blinding_commitment(
                self.point_labels[lhs_var.0],
                &commitment,
            )?;

            match proof_type {
                ProofType::Xor => {
                    let c = proof.challenges[i];
                    match clause_challenges.get(clause_nr) {
                        Some(cc) => {
                            // check to make sure this challenge meets what we expect for this clause
                            if *cc != c {
                                return Err(ProofError::VerificationFailure);
                            }
                        },
                        None => {
                            clause_challenges.insert(*clause_nr, c);
                        }
                    }
                },
                _ => {}
            };
        }

        let rec_challenge = match proof_type {
            ProofType::Shamir => {
                // threshold is the number of public keys NOT in the known signature group, plus at least one in the known signature group
                let threshold = (self.constraints.len() - 1) * self.constraints[0].2.len() + 1;
                let mut sham = Shamir::new_without_rng(threshold);
                sham.reconstruct(&proof.challenges)
            },
            ProofType::Xor => {
                let challenges = clause_challenges.values().map(|s| *s).collect();
                let mut xor = Xor::new_without_rng();
                xor.reconstruct(&challenges)
            },
            _ => {
                panic!("This isn't implemented yet!");
            }
        };

        let challenge = self.transcript.get_challenge(b"chal");

        if rec_challenge.is_ok() && challenge != rec_challenge.unwrap() {
            return Err(ProofError::VerificationFailure);
        }

        let commitments_offset = self.points.len();
        let combined_points = self.points.iter().chain(proof.commitments.iter());

        let mut coeffs = vec![Scalar::zero(); self.points.len() + proof.commitments.len()];
        // For each constraint of the form Q = sum(P_i, x_i),
        // we want to ensure Q_com = sum(P_i, resp_i) - c * Q,
        // so add the check rand*( sum(P_i, resp_i) - c * Q - Q_com ) == 0
        for i in 0..self.constraints.len() {
            let (_, ref lhs_var, ref rhs_lc) = self.constraints[i];
            let random_factor = Scalar::from(thread_rng().gen::<u128>());
            let minus_c = -proof.challenges[i];

            coeffs[commitments_offset + i] += -random_factor;
            coeffs[lhs_var.0] += random_factor * minus_c;
            for (sc_var, pt_var) in rhs_lc {
                coeffs[pt_var.0] += random_factor * proof.responses[sc_var.0];
            }
        }

        let check = RistrettoPoint::optional_multiscalar_mul(
            &coeffs,
            combined_points.map(|pt| pt.decompress()),
        )
        .ok_or(ProofError::VerificationFailure)?;

        if check.is_identity() {
            Ok(())
        } else {
            Err(ProofError::VerificationFailure)
        }
    }
}

impl<'a> SchnorrCS for Verifier<'a> {
    type ScalarVar = ScalarVar;
    type PointVar = PointVar;
    type SubroutineVar = Verifier<'a>;

    fn constrain(&mut self, clause_nr: usize, lhs: PointVar, linear_combination: Vec<(ScalarVar, PointVar)>) {
        self.constraints.push((clause_nr, lhs, linear_combination));
    }

    fn add_subroutine(&mut self, subroutine: Verifier<'a>) {
        self.subroutines.push(subroutine);
    }
}
