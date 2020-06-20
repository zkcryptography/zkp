#![allow(non_snake_case)]

extern crate rand;

extern crate curve25519_dalek;
use curve25519_dalek::constants as dalek_constants;
use curve25519_dalek::scalar::Scalar;

#[macro_use]
extern crate zkp;
pub use zkp::Transcript;

define_proof! {basic_and_clause, "basic_and_clause", (x,y), (A, B, G), () : A = (G ^ x) && B = (G ^ y)}
define_proof! {complex_and_clause, "complex_and_clause", (x, y, z, a), (A, B, C, D, G), (): A = (G^x) && B = (G^y) && C = (G^z) && D = (G^a)}

#[test]
fn and_test_basic() {
    // Prover's scope
    let (proof, points) = {
        let x = Scalar::from(89327492234u64).invert();
        let y = Scalar::from(8675309u64);
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let B = &y * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"And Clause Test");
        basic_and_clause::prove_compact(
            &mut transcript,
            basic_and_clause::ProveAssignments {
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
    let parsed_proof: basic_and_clause::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"And Clause Test");
    assert!(basic_and_clause::verify_compact(
        &parsed_proof,
        &mut transcript,
        basic_and_clause::VerifyAssignments {
            A: &points.A,
            B: &points.B,
            G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
        },
    )
    .is_ok());
}

#[test]
fn and_test_complex() {
    // Prover's scope
    let res = {
        let x = Scalar::from(89327492234u64).invert();
        let y = Scalar::from(8675309u32);
        let z = Scalar::from(1600u32);
        let a = Scalar::from(11001001u32);
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let B = &y * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let C = &z * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let D = &a * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"And Clause Test");
        complex_and_clause::prove_compact(
            &mut transcript,
            complex_and_clause::ProveAssignments {
                x: &Some(x),
                y: &Some(y),
                z: &Some(z),
                a: &Some(a),
                A: &A,
                B: &B,
                C: &C,
                D: &D,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        )
    };
    match res {
        Err(e) => assert!(false, format!("Error building proof: {}", e)),
        Ok((proof, points)) => {
            // Serialize and parse bincode representation
            let proof_bytes = bincode::serialize(&proof).unwrap();
            let parsed_proof: complex_and_clause::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

            // Verifier logic
            let mut transcript = Transcript::new(b"And Clause Test");
            let ver = complex_and_clause::verify_compact(
                &parsed_proof,
                &mut transcript,
                complex_and_clause::VerifyAssignments {
                    A: &points.A,
                    B: &points.B,
                    C: &points.C,
                    D: &points.D,
                    G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
                },
            );
            match ver {
                Err(e) => assert!(false, format!("Error verifying proof: {}", e)),
                Ok(_) => assert!(true),
            }
        },
    }
}


#[test]
fn and_test_insufficient_keys() {
    // Prover's scope
    let res = {
        let x = Scalar::from(89327492234u64).invert();
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let B = &Scalar::from(3u32) * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"And Clause Test");
        basic_and_clause::prove_compact(
            &mut transcript,
            basic_and_clause::ProveAssignments {
                x: &Some(x),
                y: &None,
                A: &A,
                B: &B,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        )
    };
    match res {
        Err(e) => assert!(false, format!("Error building proof: {}", e)),
        Ok((proof, points)) => {
            // Serialize and parse bincode representation
            let proof_bytes = bincode::serialize(&proof).unwrap();
            let parsed_proof: basic_and_clause::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

            // Verifier logic
            let mut transcript = Transcript::new(b"And Clause Test");
            let ver = basic_and_clause::verify_compact(
                &parsed_proof,
                &mut transcript,
                basic_and_clause::VerifyAssignments {
                    A: &points.A,
                    B: &points.B,
                    G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
                },
            );
            match ver {
                Err(e) => assert!(true, format!("This was intended to fail: {}", e)),
                Ok(_) => assert!(false, "This was supposed to fail!"),
            }
        },
    }
}