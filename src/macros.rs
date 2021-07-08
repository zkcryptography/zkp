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

#[doc(hidden)]
#[macro_export]
macro_rules! __compute_formula_constraint {
    // Unbracket a statement
    (($public_vars:ident, $secret_vars:ident) ($($x:tt)*)) => {
        // Add a trailing +
        __compute_formula_constraint!(($public_vars,$secret_vars) $($x)* *)
    };
    // Inner part of the formula: give a list of &Scalars
    // Since there's a trailing +, we can just generate the list as normal...
    (($public_vars:ident, $secret_vars:ident)
     $( $point:ident ^ $scalar:ident *)+ ) => {
        vec![ $( ($secret_vars.$scalar , $public_vars.$point), )* ]
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __parse_subroutine {
    ( $wrong:tt ) => {
        Err("Wrong")
    };
    ( $name:ident, ( $($secret_var:ident),+ ), ( $($instance_var:ident),* ) ) => {
        $name::new()
    };
}

/// Creates a module with code required to produce a non-interactive
/// zero-knowledge proof statement, to serialize it to wire format, to
/// parse from wire format, and to verify the proof or batch-verify
/// multiple proofs.
///
/// The statement is specified in an embedded DSL resembling
/// Camenisch-Stadler notation.  For instance, a proof of knowledge of
/// two equal discrete logarithms ("DLEQ") is specified as:
///
/// ```rust,ignore
/// define_proof! {dleq, "DLEQ Proof", (x), (A, B, H), (G) : A = (G ^ x), B = (H ^ x) }
/// ```
///
/// This creates a module `dleq` with code for proving knowledge of a
/// secret `x: Scalar` such that `A = G ^ x`, `B = H ^ x` for
/// per-proof public parameters `A, B, H: RistrettoPoint` and common
/// parameters `G: RistrettoPoint`; the UTF-8 string `"DLEQ Proof"` is
/// added to the transcript as a domain separator.
///
/// In general the syntax is
/// ```rust,ignore
/// define_proof!{
///     module_name,   // all generated code for this statement goes here
///     "Proof Label", // a UTF-8 domain separator unique to the statement
///     (x,y,z,...),   // secret variable labels (preferably lower-case)
///     (A,B,C,...),   // public per-proof parameter labels (upper-case)
///     (G,H,...)      // public common parameter labels (upper-case)
///     :
///     LHS = (A ^ x * B ^ y * C ^ z * ... ),  // comma-separated statements
///     ...
/// }
/// ```
///
/// Statements have the form `LHS = (A ^ x * B ^ y * C ^ z * ... )`,
/// where `LHS` is one of the points listed as a public parameter, and
/// the right-hand side is a product of public points raised to the power of
/// some secret scalars.
///
/// Points which have the same assignment for all instances of the
/// proof statement (for instance, a basepoint) should be specified as
/// common public parameters, so that the generated implementation of
/// batch verification is more efficient.
///
/// Proof creation is done in constant time.  Proof verification uses
/// variable-time code.
#[macro_export]
macro_rules! define_proof {
    (
        $proof_module_name:ident // Name of the module to create
        ,
        $proof_label_string:expr // A string literal, used as a domain separator
        ,
        ( $($secret_var:ident),+ ) // Secret variables, sep by commas
        ,
        ( $($instance_var:ident),* ) // Public instance variables, separated by commas
        ,
        ( $($common_var:ident),* ) // Public common variables, separated by commas
        :
        // List of statements to prove
        // Format: LHS = ( ... RHS expr ... ),
        $($($lhs:tt $(= $statement:tt)?)&&+)||*
    ) => {
        /// An auto-generated Schnorr proof implementation.
        ///
        /// Proofs are created using `prove_compact` or
        /// `prove_batchable`, producing `CompactProof`s or
        /// `BatchableProof`s respectively.  These are verified
        /// using `verify_compact` and `verify_batchable`;
        /// `BatchableProofs` can also be batch-verified using
        /// `batch_verify`, but they have slightly larger proof
        /// sizes compared to `CompactProof`s.
        ///
        /// The internal details of the proof statement are accessible
        /// in the `internals` module.  While this is not necessary
        /// to create and verify proofs, the it can be used with the
        /// lower-level constraint system API to manually combine
        /// statements from different proofs.
        #[allow(non_snake_case)]
        pub mod $proof_module_name {
            use $crate::curve25519_dalek::scalar::Scalar;
            use $crate::curve25519_dalek::ristretto::RistrettoPoint;
            use $crate::curve25519_dalek::ristretto::CompressedRistretto;

            use $crate::toolbox::prover::Prover;
            use $crate::toolbox::prover::PointVar;
            use $crate::toolbox::prover::ScalarVar;
            use $crate::toolbox::verifier::Verifier;

            use $crate::toolbox::SchnorrCS;
            use $crate::toolbox::ProofType;
            use $crate::toolbox::{IsSigmaProtocol, IsProverAssignments};

            use log::debug;

            pub use $crate::merlin::Transcript;
            pub use $crate::{CompactProof, BatchableProof, ProofError};

            pub struct $proof_module_name<'a> {
                transcript: &'a mut Transcript,
                scalars: Vec<Option<Scalar>>,
                points: Vec<RistrettoPoint>,
                point_labels: Vec<&'static [u8]>,
                constraints: Vec<(usize, PointVar, Vec<(ScalarVar, PointVar)>)>,
                subroutines: Vec<Prover<'a>>,
            
                //internals
                commitments: Vec<CompressedRistretto>,
                blindings: Vec<Option<Scalar>>,
                fake_responses: Vec<Option<Scalar>>,
                known_chal_shares: Vec<Option<Scalar>>,
                pub nr_clauses: usize,
            }

            /// The proof label committed to the transcript as a domain separator.
            pub const PROOF_LABEL: &'static str = $proof_label_string;

            /// A container type that holds transcript labels for secret variables.
            pub struct TranscriptLabels {
                $( pub $secret_var: &'static str, )+
                $( pub $instance_var: &'static str, )*
                $( pub $common_var: &'static str, )*
            }

            /// The transcript labels used for each secret variable.
            pub const TRANSCRIPT_LABELS: TranscriptLabels = TranscriptLabels {
                $( $secret_var: stringify!($secret_var), )+
                $( $instance_var: stringify!($instance_var), )*
                $( $common_var: stringify!($common_var), )*
            };

            /// A container type that simulates named parameters for [`proof_statement`].
            #[derive(Copy, Clone)]
            pub struct SecretVars<CS: SchnorrCS> {
                $( pub $secret_var: CS::ScalarVar, )+
            }

            /// A container type that simulates named parameters for [`proof_statement`].
            #[derive(Copy, Clone)]
            pub struct PublicVars<CS: SchnorrCS> {
                $( pub $instance_var: CS::PointVar, )*
                $( pub $common_var: CS::PointVar, )*
            }


            /// Named parameters for [`prove_compact`] and [`prove_batchable`].
            #[derive(Copy, Clone)]
            pub struct ProveAssignments<'a> {
                $(pub $secret_var: &'a Option<Scalar>,)+
                $(pub $instance_var: &'a RistrettoPoint,)*
                $(pub $common_var: &'a RistrettoPoint,)*
            }

            impl<'a> IsProverAssignments for ProveAssignments<'a> {
                fn secret_vars(&self) -> Vec<&Option<Scalar>> {
                    vec![$(self.$secret_var,)+]
                }

                fn instance_vars(&self) -> Vec<&RistrettoPoint> {
                    vec![$(self.$instance_var,)*]
                }

                fn common_vars(&self) -> Vec<&RistrettoPoint> {
                    vec![$(self.$common_var,)*]
                }
            }

            // impl<'a> From<IsProverAssignments> for ProveAssignments<'a> {
            //     fn from(ipa: &dyn IsProverAssignments) -> Self {
            //         let secrets = ipa.secret_vars().iter();
            //         let instances = ipa.instance_vars().iter();
            //         let commons = ipa.common_vars().iter();

            //         let mut to_ret = ProveAssignments{
            //             $(
            //                 $secret_var: secrets.next(),
            //             )+
            //             $(
            //                 $instance_var: instances.next(),
            //             )*
            //             $(
            //                 $common_var: commons.next(),
            //             )*
            //         };

            //         to_ret
            //     }
            // }

            /// Named parameters for [`verify_compact`] and [`verify_batchable`].
            #[derive(Copy, Clone)]
            pub struct VerifyAssignments<'a> {
                $(pub $instance_var: &'a CompressedRistretto,)*
                $(pub $common_var: &'a CompressedRistretto,)*
            }

            /// Point encodings computed during proving and returned to allow reuse.
            ///
            /// This is used to allow a prover to avoid having to
            /// re-compress points used in the proof that may be
            /// necessary to supply to the verifier.
            #[derive(Copy, Clone)]
            pub struct CompressedPoints {
                $(pub $instance_var: CompressedRistretto,)*
                $(pub $common_var: CompressedRistretto,)*
            }

            /// Named parameters for [`batch_verify`].
            #[derive(Clone)]
            pub struct BatchVerifyAssignments {
                $(pub $instance_var: Vec<CompressedRistretto>,)*
                $(pub $common_var: CompressedRistretto,)*
            }

            pub fn new(transcript: &mut Transcript) -> $proof_module_name {
                $proof_module_name{
                    transcript,
                    scalars: Vec::default(),
                    points: Vec::default(),
                    point_labels: Vec::default(),
                    constraints: Vec::default(),
                    subroutines: Vec::default(),
                    commitments: Vec::default(),
                    blindings: Vec::default(),
                    fake_responses: Vec::default(),
                    known_chal_shares: Vec::default(),
                    nr_clauses: 0,
                }
            }

            impl<'a> $proof_module_name<'a> {

                /// The underlying proof statement generated by the macro invocation.
                ///
                /// This function exists separately from the proving
                /// and verification functions to allow composition of
                /// different proof statements with common variable
                /// assignments.
                pub fn proof_statement<CS: SchnorrCS>(
                    &self,
                    cs: &mut CS,
                    secrets: SecretVars<CS>,
                    publics: PublicVars<CS>,
                ) -> usize {
                    let mut clause_nr = 1;
                    $($(
                        let mut subroutine = true;
                        $(
                            subroutine = false;
                            cs.constrain(
                                clause_nr,
                                publics.$lhs,
                                __compute_formula_constraint!( (publics, secrets) $statement ),
                            );
                        )?
                        if (subroutine) {
                            let result = __parse_subroutine!($lhs);
                            if result.is_ok() {
                                cs.add_subroutine(result.unwrap());
                            }
                        }
                    )+
                    clause_nr += 1;
                    )*
                    clause_nr - 1
                }

                fn build_prover(
                    &self,
                    transcript: &'a mut Transcript,
                    assignments: ProveAssignments,
                ) -> (Prover<'a>, CompressedPoints) {
                    use $crate::toolbox::prover::*;

                    let mut prover = Prover::new(PROOF_LABEL.as_bytes(), transcript);

                    let secret_vars = SecretVars {
                        $(
                            $secret_var: prover.allocate_scalar(
                                TRANSCRIPT_LABELS.$secret_var.as_bytes(),
                                *assignments.$secret_var,
                            ),
                        )+
                    };

                    struct VarPointPairs {
                        $( pub $instance_var: (PointVar, CompressedRistretto), )*
                        $( pub $common_var: (PointVar, CompressedRistretto), )*
                    }

                    let pairs = VarPointPairs {
                        $(
                            $instance_var: prover.allocate_point(
                                TRANSCRIPT_LABELS.$instance_var.as_bytes(),
                                *assignments.$instance_var,
                            ),
                        )*
                        $(
                            $common_var: prover.allocate_point(
                                TRANSCRIPT_LABELS.$common_var.as_bytes(),
                                *assignments.$common_var,
                            ),
                        )*
                    };

                    // XXX return compressed points
                    let public_vars = PublicVars {
                        $($instance_var: pairs.$instance_var.0,)*
                        $($common_var: pairs.$common_var.0,)*
                    };

                    let compressed = CompressedPoints {
                        $($instance_var: pairs.$instance_var.1,)*
                        $($common_var: pairs.$common_var.1,)*
                    };

                    prover.nr_clauses = self.proof_statement(&mut prover, secret_vars, public_vars);

                    // debug!("Prover transcript state after creation: {:?}", prover.transcript().);

                    (prover, compressed)
                }

                /// Given a transcript and assignments to secret and public variables, produce a proof in compact format.
                pub fn prove_compact(
                    &self,
                    transcript: &mut Transcript,
                    assignments: ProveAssignments,
                ) -> Result<(CompactProof, CompressedPoints), ProofError> {
                    let (mut prover, compressed) = self.build_prover(transcript, assignments);

                    let result = prover.commit(assignments);
                    if result.is_err() {
                        return Err(result.err().unwrap());
                    };

                    // Obtain a scalar challenge and compute responses
                    let challenge: Scalar = IsSigmaProtocol::<ProveAssignments>::challenge(&mut prover);
                    let proof = prover.response(challenge, assignments);

                    Ok((CompactProof {
                        challenges: proof.challenges,
                        responses: proof.responses,
                    }, compressed))
                }

                /// Given a transcript and assignments to secret and public variables, produce a proof in batchable format.
                pub fn prove_batchable(
                    &self,
                    transcript: &mut Transcript,
                    assignments: ProveAssignments,
                ) -> Result<(BatchableProof, CompressedPoints), ProofError> {
                    let (mut prover, compressed) = self.build_prover(transcript, assignments);

                    let result = prover.commit(assignments);
                    if result.is_err() {
                        return Err(result.err().unwrap());
                    };

                    let challenge: Scalar = IsSigmaProtocol::<ProveAssignments>::challenge(&mut prover);
                    let proof = prover.response(challenge, assignments);
                    
                    Ok((BatchableProof{
                        challenges: proof.challenges,
                        commitments: proof.commitments,
                        responses: proof.responses,
                    }, compressed))
                }

                fn build_verifier(
                    &self,
                    transcript: &'a mut Transcript,
                    assignments: VerifyAssignments,
                ) -> Result<Verifier<'a>, ProofError> {
                    use $crate::toolbox::verifier::*;

                    let mut verifier = Verifier::new(PROOF_LABEL.as_bytes(), transcript);

                    let secret_vars = SecretVars {
                        $($secret_var: verifier.allocate_scalar(TRANSCRIPT_LABELS.$secret_var.as_bytes()),)+
                    };

                    let public_vars = PublicVars {
                        $(
                            $instance_var: verifier.allocate_point(
                                TRANSCRIPT_LABELS.$instance_var.as_bytes(),
                                *assignments.$instance_var,
                            )?,
                        )*
                        $(
                            $common_var: verifier.allocate_point(
                                TRANSCRIPT_LABELS.$common_var.as_bytes(),
                                *assignments.$common_var,
                            )?,
                        )*
                    };

                    self.proof_statement(&mut verifier, secret_vars, public_vars);

                    Ok(verifier)
                }

                /// Given a transcript and assignments to public variables, verify a proof in compact format.
                pub fn verify_compact(
                    &self,
                    proof: &CompactProof,
                    transcript: &mut Transcript,
                    assignments: VerifyAssignments,
                ) -> Result<(), ProofError> {
                    let verifier = self.build_verifier(transcript, assignments)?;

                    verifier.verify_compact(proof)
                }

                /// Given a transcript and assignments to public variables, verify a proof in batchable format.
                pub fn verify_batchable(
                    &self,
                    proof: &BatchableProof,
                    transcript: &mut Transcript,
                    assignments: VerifyAssignments,
                ) -> Result<(), ProofError> {
                    let verifier = self.build_verifier(transcript, assignments)?;

                    verifier.verify_batchable(proof)
                }

                /// Verify a batch of proofs, given a batch of transcripts and a batch of assignments.
                pub fn batch_verify(
                    &self,
                    proofs: &[BatchableProof],
                    transcripts: Vec<&mut Transcript>,
                    assignments: BatchVerifyAssignments,
                ) -> Result<(), ProofError> {
                    use $crate::toolbox::batch_verifier::*;

                    let batch_size = proofs.len();

                    let mut verifier = BatchVerifier::new(PROOF_LABEL.as_bytes(), batch_size, transcripts)?;

                    let secret_vars = SecretVars {
                        $($secret_var: verifier.allocate_scalar(TRANSCRIPT_LABELS.$secret_var.as_bytes()),)+
                    };

                    let public_vars = PublicVars {
                        $(
                            $instance_var: verifier.allocate_instance_point(
                                TRANSCRIPT_LABELS.$instance_var.as_bytes(),
                                assignments.$instance_var,
                            )?,
                        )*
                        $(
                            $common_var: verifier.allocate_static_point(
                                TRANSCRIPT_LABELS.$common_var.as_bytes(),
                                assignments.$common_var,
                            )?,
                        )*
                    };

                    self.proof_statement(&mut verifier, secret_vars, public_vars);

                    verifier.verify_batchable(proofs)
                }

                pub fn output_latex_protocol() -> String {
                    "PoK$\\{(x) : A = g^x\\}$".to_string() //TODO: implement!
                }

                pub fn measure() -> usize {
                    5 //TODO: implement! I guess it's not gonna be usize as output, but some Measurement object
                }
            }

            impl<'a, P> IsSigmaProtocol<P> for $proof_module_name<'a> where P: IsProverAssignments {
                type Proof = BatchableProof;        // TODO we need to make this configurable
            
                fn commit(&mut self, assignments: P) -> Result<(), ProofError> {
                    // Construct a TranscriptRng
                    let mut rng_builder = self.transcript.build_rng();
                    for scalar in &self.scalars {
                        if scalar.is_some() {
                            rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.unwrap().as_bytes());
                        }
                    }
                    let mut transcript_rng = rng_builder.finalize(&mut thread_rng());
            
                    // Generate a blinding factor for each secret variable
                    let blindings = assignments.secret_vars().iter().map(|scalar| {
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
                                            shares.push(Some(random_scalar(&mut transcript_rng)));
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
            
                fn simulate(&mut self, _assignments: P) -> (Vec<Scalar>, Vec<Scalar>) {
                    (vec![], vec![])
                    // TODO
                }
            
                fn challenge(&mut self) -> Scalar {
                    let challenge = self.transcript.get_challenge(b"chal");
                    debug!("Prover's transcript challenge is {:?}", challenge);
                    challenge
                }
            
                // TODO it looks like we don't modify the transcript here; is that what we want?
                fn response(&mut self, challenge: Scalar, _assignments: P) -> Self::Proof {
                    let blindings = &self.blindings;
                    let fake_responses = &self.fake_responses;
                    let responses: Vec<Scalar>;
            
                    let mut rng = rand::thread_rng();
            
                    let mut sharing: Box<dyn SecretSharing> = match self.proof_type {
                        ProofType::Xor => {
                            Box::from(Xor::new(&mut rng)) as Box<dyn SecretSharing>
                        },
                        ProofType::Shamir => {
                            let threshold = 1 + self.known_chal_shares.iter().filter(|r| r.is_some()).count();
                            Box::from(Shamir::new(threshold, &mut rng)) as Box<dyn SecretSharing>
                        },
                        _ => {
                            panic!("This isn't implemented yet!");
                        }
                    };
            
                    let mut challenges = sharing.complete(&challenge, &self.known_chal_shares).unwrap();
                    trace!("Challenges: {:?}", challenges);
            
                    match self.proof_type {
                        ProofType::Xor => {
                            challenges = self.constraints.iter().map(|(clause_nr, _, _)| {
                                challenges[*clause_nr - 1]
                            }).collect();
                        },
                        _ => ()
                    };
            
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
            
                    let out_shares = challenges;
                    let commitments = self.commitments.clone();
                    Self::Proof{
                        challenges: out_shares,
                        responses,
                        commitments,
                    }
                }
            }

            // #[cfg(all(feature = "bench", test))]
            // mod bench {
            //     use super::*;
            //     use $crate::rand::thread_rng;

            //     extern crate test;
            //     use self::test::Bencher;

            //     #[bench]
            //     fn prove(b: &mut Bencher) {
            //         let mut rng = thread_rng();

            //         struct RandomAssignments {
            //             $(pub $secret_var: Scalar,)+
            //             $(pub $instance_var: RistrettoPoint,)*
            //             $(pub $common_var: RistrettoPoint,)*
            //         }

            //         let assignments = RandomAssignments {
            //             $($secret_var: Scalar::random(&mut rng),)+
            //             $($instance_var: RistrettoPoint::random(&mut rng),)*
            //             $($common_var: RistrettoPoint::random(&mut rng),)*
            //         };

            //         // Proving is constant time, so it shouldn't matter
            //         // that the relation is not satisfied by random assignments.
            //         b.iter(|| {
            //             let mut trans = Transcript::new(b"Benchmark");
            //             prove_compact(&mut trans, ProveAssignments {
            //                 $($secret_var: &assignments.$secret_var,)+
            //                 $($instance_var: &assignments.$instance_var,)*
            //                 $($common_var: &assignments.$common_var,)*
            //             })
            //         });
            //     }

            //     #[bench]
            //     fn verify_compact_proof(b: &mut Bencher) {
            //         let mut rng = thread_rng();

            //         struct RandomAssignments {
            //             $(pub $secret_var: Scalar,)+
            //             $(pub $instance_var: RistrettoPoint,)*
            //             $(pub $common_var: RistrettoPoint,)*
            //         }

            //         let assignments = RandomAssignments {
            //             $($secret_var: Scalar::random(&mut rng),)+
            //             $($instance_var: RistrettoPoint::random(&mut rng),)*
            //             $($common_var: RistrettoPoint::random(&mut rng),)*
            //         };

            //         let mut trans = Transcript::new(b"Benchmark");
            //         let (proof, points) = prove_compact(&mut trans, ProveAssignments {
            //             $($secret_var: &assignments.$secret_var,)+
            //             $($instance_var: &assignments.$instance_var,)*
            //             $($common_var: &assignments.$common_var,)*
            //         });

            //         // The proof is well-formed but invalid, so the
            //         // compact verification should fall through to the
            //         // final check on the recomputed challenge, and
            //         // therefore verification failure should not affect
            //         // timing.
            //         b.iter(|| {
            //             let mut trans = Transcript::new(b"Benchmark");
            //             verify_compact(&proof, &mut trans, VerifyAssignments {
            //                 $($instance_var: &points.$instance_var,)*
            //                 $($common_var: &points.$common_var,)*
            //             })
            //         });
            //     }

            //     #[bench]
            //     fn verify_batchable_proof(b: &mut Bencher) {
            //         let mut rng = thread_rng();

            //         struct RandomAssignments {
            //             $(pub $secret_var: Scalar,)+
            //             $(pub $instance_var: RistrettoPoint,)*
            //             $(pub $common_var: RistrettoPoint,)*
            //         }

            //         let assignments = RandomAssignments {
            //             $($secret_var: Scalar::random(&mut rng),)+
            //             $($instance_var: RistrettoPoint::random(&mut rng),)*
            //             $($common_var: RistrettoPoint::random(&mut rng),)*
            //         };

            //         let mut trans = Transcript::new(b"Benchmark");
            //         let (proof, points) = prove_batchable(&mut trans, ProveAssignments {
            //             $($secret_var: &assignments.$secret_var,)+
            //             $($instance_var: &assignments.$instance_var,)*
            //             $($common_var: &assignments.$common_var,)*
            //         });

            //         // The proof is well-formed but invalid, so the
            //         // batchable verification should perform the check and
            //         // see a non-identity point.  So verification failure
            //         // should not affect timing.
            //         b.iter(|| {
            //             let mut trans = Transcript::new(b"Benchmark");
            //             verify_batchable(&proof, &mut trans, VerifyAssignments {
            //                 $($instance_var: &points.$instance_var,)*
            //                 $($common_var: &points.$common_var,)*
            //             })
            //         });
            //     }
            // }
        }
    }
}
