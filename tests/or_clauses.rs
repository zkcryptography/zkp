#![allow(non_snake_case)]

extern crate rand;
use rand::{thread_rng, CryptoRng, RngCore};

extern crate curve25519_dalek;
use curve25519_dalek::constants as dalek_constants;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;

#[macro_use]
extern crate zkp;
pub use zkp::Transcript;
use zkp::ProofError;


define_proof! {basic_or_clause, "basic_or_clause", (x,y), (A, B, G), () : A = (G ^ x) || B = (G ^ y)}
define_proof! {complex_or_clause, "complex_or_clause", (x, y, z, a), (A, B, C, D, G), (): A = (G^x) && B = (G^y) || C = (G^z) && D = (G^a)}

/// Defines how the construction interacts with the transcript.
trait TranscriptProtocol {
    fn append_message_example(&mut self, message: &[u8]);
    fn hash_to_group(self) -> RistrettoPoint;
}

impl TranscriptProtocol for Transcript {
    fn append_message_example(&mut self, message: &[u8]) {
        self.append_message(b"msg", message);
    }
    fn hash_to_group(mut self) -> RistrettoPoint {
        let mut bytes = [0u8; 64];
        self.challenge_bytes(b"output", &mut bytes);
        RistrettoPoint::from_uniform_bytes(&bytes)
    }
}

#[derive(Clone)]
pub struct SecretKey(Scalar);

impl SecretKey {
    fn new<R: RngCore + CryptoRng>(rng: &mut R) -> SecretKey {
        SecretKey(Scalar::random(rng))
    }
}

#[derive(Copy, Clone)]
pub struct PublicKey(RistrettoPoint, CompressedRistretto);

impl<'a> From<&'a SecretKey> for PublicKey {
    fn from(sk: &'a SecretKey) -> PublicKey {
        let pk = &sk.0 * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        PublicKey(pk, pk.compress())
    }
}

pub struct KeyPair {
    sk1: SecretKey,
    sk2: SecretKey,
    pk1: PublicKey,
    pk2: PublicKey,
}

impl From<(SecretKey, SecretKey)> for KeyPair {
    fn from((sk1, sk2): (SecretKey, SecretKey)) -> KeyPair {
        let pk1 = PublicKey::from(&sk1);
        let pk2 = PublicKey::from(&sk2);
        KeyPair { sk1, pk1, sk2, pk2 }
    }
}

pub struct Signature(basic_or_clause::CompactProof);

impl KeyPair {
    fn public_key(&self) -> (PublicKey, PublicKey) {
        (self.pk1, self.pk2)
    }

    fn sign(&self, clause: usize, message: &[u8], sig_transcript: &mut Transcript) -> Signature {
        sig_transcript.append_message_example(message);
        let result = basic_or_clause::prove_compact(
            sig_transcript,
            basic_or_clause::ProveAssignments {
                x: &match clause == 1 { true => Some(self.sk1.0), false => None },
                y: &match clause == 2 { true => Some(self.sk2.0), false => None },
                A: &self.pk1.0,
                B: &self.pk2.0,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        );
        if result.is_err() {
            assert!(false, format!("{}", result.as_ref().err().unwrap()));
        }

        let (proof, _points) = result.unwrap();
        return Signature(proof);
    }
}

impl Signature {
    fn verify(
        &self,
        message: &[u8],
        pubkey1: &PublicKey,
        pubkey2: &PublicKey,
        sig_transcript: &mut Transcript,
    ) -> Result<(), ProofError> {
        sig_transcript.append_message_example(message);
        basic_or_clause::verify_compact(
            &self.0,
            sig_transcript,
            basic_or_clause::VerifyAssignments {
                A: &pubkey1.1,
                B: &pubkey2.1,
                G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
            },
        )
            // .map_err(|_discard_error_info_in_test_code| ())
    }
}

#[test]
fn create_and_verify_or_sig() {
    let domain_sep = b"My Sig Application";
    let msg1 = b"Test Message 1";
    let msg2 = b"Test Message 2";

    let kp1 = KeyPair::from((SecretKey::new(&mut thread_rng()), SecretKey::new(&mut thread_rng())));
    let pk1 = kp1.public_key();
    let kp2 = KeyPair::from((SecretKey::new(&mut thread_rng()), SecretKey::new(&mut thread_rng())));
    let pk2 = kp2.public_key();

    let sig1 = kp1.sign(1, &msg1[..], &mut Transcript::new(domain_sep));

    let sig2 = kp2.sign(1, &msg2[..], &mut Transcript::new(domain_sep));

    let sig3 = kp1.sign(2, &msg1[..], &mut Transcript::new(domain_sep));

    let sig4 = kp2.sign(2, &msg2[..], &mut Transcript::new(domain_sep));

    // Check that each signature verifies
    assert!(sig1
        .verify(msg1, &pk1.0, &pk1.1, &mut Transcript::new(domain_sep))
        .is_ok());
    assert!(sig2
        .verify(msg2, &pk2.0, &pk2.1, &mut Transcript::new(domain_sep))
        .is_ok());
    assert!( sig3
        .verify(msg1, &pk1.0, &pk1.1, &mut Transcript::new(domain_sep))
        .is_ok());
    assert!(sig4
        .verify(msg2, &pk2.0, &pk2.1, &mut Transcript::new(domain_sep))
        .is_ok());

    // Check that verification with the wrong pubkey fails
    assert!(sig1
        .verify(msg1, &pk2.0, &pk2.1, &mut Transcript::new(domain_sep))
        .is_err());
    assert!(sig2
        .verify(msg2, &pk1.0, &pk1.1, &mut Transcript::new(domain_sep))
        .is_err());
    assert!(sig3
        .verify(msg1, &pk2.0, &pk2.1, &mut Transcript::new(domain_sep))
        .is_err());
    assert!(sig4
        .verify(msg2, &pk1.0, &pk1.1, &mut Transcript::new(domain_sep))
        .is_err());

    // Check that verification with the wrong message fails
    assert!(sig1
        .verify(msg2, &pk1.0, &pk1.1, &mut Transcript::new(domain_sep))
        .is_err());
    assert!(sig2
        .verify(msg1, &pk2.0, &pk2.1, &mut Transcript::new(domain_sep))
        .is_err());
    assert!(sig3
        .verify(msg2, &pk1.0, &pk1.1, &mut Transcript::new(domain_sep))
        .is_err());
    assert!(sig4
        .verify(msg1, &pk2.0, &pk2.1, &mut Transcript::new(domain_sep))
        .is_err());

    // Check that verification with the wrong domain separator fails
    assert!(sig1
        .verify(msg1, &pk1.0, &pk1.1, &mut Transcript::new(b"Wrong"))
        .is_err());
    assert!(sig2
        .verify(msg2, &pk2.0, &pk2.1, &mut Transcript::new(b"Wrong"))
        .is_err());
    assert!(sig3
        .verify(msg1, &pk1.0, &pk1.1, &mut Transcript::new(b"Wrong"))
        .is_err());
    assert!(sig4
        .verify(msg2, &pk2.0, &pk2.1, &mut Transcript::new(b"Wrong"))
        .is_err());
}

#[test]
fn or_test_basic() {
    // Prover's scope
    let (proof, points) = {
        let x = Scalar::from(89327492234u64).invert();
        let y = None;
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let B = &Scalar::from(7u32) * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"Or Clause Test");
        basic_or_clause::prove_compact(
            &mut transcript,
            basic_or_clause::ProveAssignments {
                x: &Some(x),
                y: &y,
                A: &A,
                B: &B,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        ).unwrap()
    };

    // Serialize and parse bincode representation
    let proof_bytes = bincode::serialize(&proof).unwrap();
    let parsed_proof: basic_or_clause::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"Or Clause Test");
    assert!(basic_or_clause::verify_compact(
        &parsed_proof,
        &mut transcript,
        basic_or_clause::VerifyAssignments {
            A: &points.A,
            B: &points.B,
            G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
        },
    )
    .is_ok());
}

#[test]
fn or_test_complex() {
    // Prover's scope
    let res = {
        let x = Scalar::from(89327492234u64).invert();
        let y = Scalar::from(8675309u32);
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let B = &y * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let C = &Scalar::from(3u32) * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let D = &Scalar::from(3u32) * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"Or Clause Test");
        complex_or_clause::prove_compact(
            &mut transcript,
            complex_or_clause::ProveAssignments {
                x: &Some(x),
                y: &Some(y),
                z: &None,
                a: &None,
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
            let parsed_proof: complex_or_clause::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

            // Verifier logic
            let mut transcript = Transcript::new(b"Or Clause Test");
            let ver = complex_or_clause::verify_compact(
                &parsed_proof,
                &mut transcript,
                complex_or_clause::VerifyAssignments {
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
fn or_test_insufficient_keys() {
    // Prover's scope
    let res = {
        let x = Scalar::from(89327492234u64).invert();
        let y = Scalar::from(8675309u32);
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let B = &y * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let C = &Scalar::from(3u32) * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let D = &Scalar::from(3u32) * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"Or Clause Test");
        complex_or_clause::prove_compact(
            &mut transcript,
            complex_or_clause::ProveAssignments {
                x: &Some(x),
                y: &None,
                z: &None,
                a: &None,
                A: &A,
                B: &B,
                C: &C,
                D: &D,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        )
    };
    match res {
        Err(_) => assert!(true),
        Ok(_) => assert!(false, "Shouldn't have been able to build this prover!"),
    }
}

#[test]
fn or_test_wrong_keys() {
    // Prover's scope
    let res = {
        let x = Scalar::from(89327492234u64).invert();
        let y = Scalar::from(8675309u32);
        let z = Scalar::from(654u32);
        let A = &x * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let B = &y * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let C = &Scalar::from(3u32) * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;
        let D = &Scalar::from(3u32) * &dalek_constants::RISTRETTO_BASEPOINT_TABLE;

        let mut transcript = Transcript::new(b"Or Clause Test");
        complex_or_clause::prove_compact(
            &mut transcript,
            complex_or_clause::ProveAssignments {
                x: &Some(x),
                y: &Some(z),
                z: &None,
                a: &None,
                A: &A,
                B: &B,
                C: &C,
                D: &D,
                G: &dalek_constants::RISTRETTO_BASEPOINT_POINT,
            },
        )
    };
    match res {
        Err(e) => assert!(false, "Error building proof: {}", e),
        Ok((proof, points)) => {
            // Serialize and parse bincode representation
            let proof_bytes = bincode::serialize(&proof).unwrap();
            let parsed_proof: complex_or_clause::CompactProof = bincode::deserialize(&proof_bytes).unwrap();

            // Verifier logic
            let mut transcript = Transcript::new(b"Or Clause Test");
            let ver = complex_or_clause::verify_compact(
                &parsed_proof,
                &mut transcript,
                complex_or_clause::VerifyAssignments {
                    A: &points.A,
                    B: &points.B,
                    C: &points.C,
                    D: &points.D,
                    G: &dalek_constants::RISTRETTO_BASEPOINT_COMPRESSED,
                },
            );
            match ver {
                Err(_) => assert!(true),
                Ok(_) => assert!(false, "This proof should not have validated!"),
            }
        },
    }
}