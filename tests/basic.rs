// -*- coding: utf-8; mode: rust; -*-
//
// To the extent possible under law, the authors have waived all
// copyright and related or neighboring rights to zkp,
// using the Creative Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/1.0/> for full
// details.
//
// Authors:
// - Henry de Valence <hdevalence@hdevalence.ca>
#![allow(non_snake_case)]

extern crate bincode;
extern crate curve25519_dalek;
extern crate serde;
#[macro_use]
extern crate zkp;

use curve25519_dalek::constants as dalek_constants;
use curve25519_dalek::scalar::Scalar;

use zkp::Transcript;

define_proof! {Dlp, "Discrete Log Proof", (x), (A), (G) : A = (G ^ x) }

#[test]
fn super_basic_create_and_verify() {
    // Prover's scope
    let (proof, points) = {
        let x = Scalar::from(89327492234u64).invert();
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"Discrete Log Test");
        Dlp::new().prove_compact(
            &mut transcript,
            Dlp::ProveAssignments {
                x: &Some(x),
                A: &A,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        ).unwrap()
    };

    // Serialize and parse bincode representation
    let proof_bytes = bincode::serialize(&proof).unwrap();
    // println!("{:?}", proof_bytes);
    let parsed_proof: Dlp::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"Discrete Log Test");
    assert!(Dlp::new().verify_compact(
        &parsed_proof,
        &mut transcript,
        Dlp::VerifyAssignments {
            A: &points.A,
            G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
        },
    )
    .is_ok());
}

#[test]
fn super_basic_failing_test() {
    // Prover's scope
    let (proof, points) = {
        let x = Scalar::from(89327492234u64).invert();
        let y = Scalar::from(89327492235u64).invert();
        let A = &y * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"Discrete Log Test");
        Dlp::new().prove_compact(
            &mut transcript,
            Dlp::ProveAssignments {
                x: &Some(x),
                A: &A,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        ).unwrap()
    };

    // Serialize and parse bincode representation
    let proof_bytes = bincode::serialize(&proof).unwrap();
    // println!("{:?}", proof_bytes);
    let parsed_proof: Dlp::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"Discrete Log Test");
    let res = Dlp::new().verify_compact(&parsed_proof,
        &mut transcript,
        Dlp::VerifyAssignments {
            A: &points.A,
            G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
        }
    );
    assert!(res.is_err(), "Shouldn't have been able to verify this!");
}