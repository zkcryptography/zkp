use rand::thread_rng;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use crate::toolbox::{SchnorrCS, TranscriptProtocol, IsSigmaProtocol, HasProofData, Proooof, IsProverAssignments, ProofType};
use crate::{BatchableProof, Transcript, ProofError};
use crate::toolbox::shamir::Shamir;
use crate::toolbox::xor::Xor;
use crate::toolbox::secrets::SecretSharing;
use crate::toolbox::util::random_scalar;
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
pub struct Prover<'a, Q> {
    transcript: &'a mut Transcript,
    prot: dyn Proooof<Q>,
    proof_type: ProofType,
}

/// A secret variable used during proving.
#[derive(Copy, Clone, Debug)]
pub struct ScalarVar(usize);

/// A public variable used during proving.
#[derive(Copy, Clone, Debug)]
pub struct PointVar(usize);

impl<'a, Q> Prover<'a, Q> {
    /// Construct a new prover.  The `proof_label` disambiguates proof
    /// statements.
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript, prot: Box<dyn Proooof<Q>>) -> Self {
        transcript.domain_sep(proof_label);
        Prover {
            transcript,
            prot: *prot,
            proof_type: ProofType::Xor,     // TODO eventually this should be autodiscovered somehow
        }
    }

    /// Allocate and assign a secret variable with the given `label`.  It returns the index of this new ScalarVar in the scalars Vector.
    pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: Option<Scalar>) -> ScalarVar {
        trace!("Allocating scalar {}", str::from_utf8(label).unwrap());
        self.transcript.append_scalar_var(label);
        self.prot.push_scalar(assignment);
        ScalarVar(self.prot.get_scalars().len() - 1)
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
        self.prot.push_point(assignment);
        self.prot.push_point_label(label);
        (PointVar(self.prot.get_points().len() - 1), compressed)
    }
}

impl<'a, Q> SchnorrCS for Prover<'a, Q> {
    type ScalarVar = ScalarVar;
    type PointVar = PointVar;
    type SubroutineVar = Prover<'a, Q>;

    fn constrain(&mut self, clause_nr: usize, lhs: PointVar, linear_combination: Vec<(ScalarVar, PointVar)>) {
        self.constraints.push((clause_nr, lhs, linear_combination));
    }

    fn add_subroutine(&mut self, subroutine: Prover<'a, Q>) {
        self.subroutines.push(subroutine);
    }
}
