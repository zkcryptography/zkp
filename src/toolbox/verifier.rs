use rand::{thread_rng, Rng};
use std::iter;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};

use crate::{ProofError, Transcript, CompactProof, BatchableProof};
use toolbox::{SchnorrCS, TranscriptProtocol};

pub struct Verifier<'a> {
    transcript: &'a mut Transcript,
    num_scalars: usize,
    points: Vec<CompressedRistretto>,
    point_labels: Vec<&'static [u8]>,
    constraints: Vec<(PointVar, Vec<(ScalarVar, PointVar)>)>,
}

#[derive(Copy, Clone)]
pub struct ScalarVar(usize);
#[derive(Copy, Clone)]
pub struct PointVar(usize);

impl<'a> Verifier<'a> {
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript) -> Self {
        transcript.domain_sep(proof_label);
        Verifier {
            transcript,
            num_scalars: 0,
            points: Vec::default(),
            point_labels: Vec::default(),
            constraints: Vec::default(),
        }
    }

    pub fn allocate_scalar(&mut self, label: &'static [u8]) -> ScalarVar {
        self.transcript.append_scalar_var(label);
        self.num_scalars += 1;
        ScalarVar(self.num_scalars - 1)
    }

    pub fn allocate_point(
        &mut self,
        label: &'static [u8],
        assignment: CompressedRistretto,
    ) -> Result<PointVar, ProofError> {
        self.transcript
            .validate_and_append_point_var(label, &assignment)?;
        self.points.push(assignment);
        self.point_labels.push(label);
        Ok(PointVar(self.points.len() - 1))
    }

    pub fn verify_compact(self, proof: &CompactProof) -> Result<(), ProofError> {
        // Check that there are as many responses as secret variables
        if proof.responses.len() != self.num_scalars {
            return Err(ProofError::VerificationFailure);
        }

        // Decompress all parameters or fail verification.
        let points = self
            .points
            .iter()
            .map(|pt| pt.decompress())
            .collect::<Option<Vec<RistrettoPoint>>>()
            .ok_or(ProofError::VerificationFailure)?;

        // Recompute the prover's commitments based on their claimed challenge value:
        let minus_c = -proof.challenge;
        for (lhs_var, rhs_lc) in &self.constraints {
            let commitment = RistrettoPoint::vartime_multiscalar_mul(
                rhs_lc
                    .iter()
                    .map(|(sc_var, _pt_var)| proof.responses[sc_var.0])
                    .chain(iter::once(minus_c)),
                rhs_lc
                    .iter()
                    .map(|(_sc_var, pt_var)| points[pt_var.0])
                    .chain(iter::once(points[lhs_var.0])),
            );

            self.transcript
                .append_blinding_commitment(self.point_labels[lhs_var.0], &commitment);
        }

        // Recompute the challenge and check if it's the claimed one
        let challenge = self.transcript.get_challenge(b"chal");

        if challenge == proof.challenge {
            Ok(())
        } else {
            Err(ProofError::VerificationFailure)
        }
    }

    pub fn verify_batchable(self, proof: &BatchableProof) -> Result<(), ProofError> {
        // Check that there are as many responses as secret variables
        if proof.responses.len() != self.num_scalars {
            return Err(ProofError::VerificationFailure);
        }
        // Check that there are as many commitments as constraints
        if proof.commitments.len() != self.constraints.len() {
            return Err(ProofError::VerificationFailure);
        }

        // Feed the prover's commitments into the transcript:
        for (i, commitment) in proof.commitments.iter().enumerate() {
            let (ref lhs_var, ref _rhs_lc) = self.constraints[i];
            self.transcript.validate_and_append_blinding_commitment(
                self.point_labels[lhs_var.0],
                &commitment,
            )?;
        }

        let minus_c = -self.transcript.get_challenge(b"chal");

        let commitments_offset = self.points.len();
        let combined_points = self.points.iter().chain(proof.commitments.iter());

        let mut coeffs = vec![Scalar::zero(); self.points.len() + proof.commitments.len()];
        // For each constraint of the form Q = sum(P_i, x_i),
        // we want to ensure Q_com = sum(P_i, resp_i) - c * Q,
        // so add the check rand*( sum(P_i, resp_i) - c * Q - Q_com ) == 0
        for i in 0..self.constraints.len() {
            let (ref lhs_var, ref rhs_lc) = self.constraints[i];
            let random_factor = Scalar::from(thread_rng().gen::<u128>());

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

    fn constrain(&mut self, lhs: PointVar, linear_combination: Vec<(ScalarVar, PointVar)>) {
        self.constraints.push((lhs, linear_combination));
    }
}