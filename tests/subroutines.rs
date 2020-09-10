#![allow(non_snake_case)]

extern crate rand;

extern crate curve25519_dalek;
use curve25519_dalek::constants as dalek_constants;
use curve25519_dalek::scalar::Scalar;

use env_logger;
// use zkp::errors::ProofError;

#[macro_use]
extern crate zkp;
pub use zkp::Transcript;

define_proof! {BasicAndClause, "basic_and_clause", (x), (A), (G) : A = (G ^ x)}
define_proof! {RenamedAndClause, "renamed_and_clause", (m), (N), (V) : N = (V ^ m)}
define_proof! {SubroutineClause, "subroutine_clause", (x, y), (A, B), (G): (BasicAndClause, x, A) && B = (G^y)}
define_proof! {RenamedSubroutineClause, "renamed_subroutine_clause", (x, y), (A, B), (G): (RenamedAndClause, (x), (A)) && B = (G^y)}

fn init() {
    let _ = env_logger::builder().is_test(true).try_init();
}

#[test]
fn subroutine_test_basic() {
    init();
    // Prover's scope
    let (proof, points) = {
        let x = Scalar::from(89327492234u64).invert();
        let y = Scalar::from(8675309u64);
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let B = &y * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"Subroutines Test");
        SubroutineClause::new().prove_compact(
            &mut transcript,
            SubroutineClause::ProveAssignments {
                x: &Some(x),
                y: &Some(y),
                A: &A,
                B: &B,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        ).unwrap()
    };

    // Serialize and parse bincode representation
    let proof_bytes = bincode::serialize(&proof).unwrap();
    let parsed_proof: SubroutineClause::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"And Clause Test");
    let ver = SubroutineClause::new().verify_compact(
        &parsed_proof,
        &mut transcript,
        SubroutineClause::VerifyAssignments {
            A: &points.A,
            B: &points.B,
            G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
        });
    assert!(ver.is_ok(), format!("Couldn't verify: {}", ver.unwrap_err()));
}

#[test]
fn subroutine_test_renamed() {
    init();
    // Prover's scope
    let (proof, points) = {
        let x = Scalar::from(89327492234u64).invert();
        let y = Scalar::from(8675309u64);
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let B = &y * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"Subroutines Test");
        RenamedSubroutineClause::new().prove_compact(
            &mut transcript,
            RenamedSubroutineClause::ProveAssignments {
                x: &Some(x),
                y: &Some(y),
                A: &A,
                B: &B,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        ).unwrap()
    };

    // Serialize and parse bincode representation
    let proof_bytes = bincode::serialize(&proof).unwrap();
    let parsed_proof: RenamedSubroutineClause::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"And Clause Test");
    let ver = RenamedSubroutineClause::new().verify_compact(
        &parsed_proof,
        &mut transcript,
        RenamedSubroutineClause::VerifyAssignments {
            A: &points.A,
            B: &points.B,
            G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
        });
    assert!(ver.is_ok(), format!("Couldn't verify: {}", ver.unwrap_err()));
}