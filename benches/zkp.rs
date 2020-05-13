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

#![feature(test)]

extern crate bincode;
extern crate curve25519_dalek;
extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate sha2;
#[macro_use]
extern crate zkp;

extern crate test;

mod cmz {
    // Proof statement for "credential presentation with 10 hidden attributes" from CMZ'13.
    define_proof! {
        cred_show_10,
        "CMZ cred show n=10",
        (m_1, m_2, m_3, m_4, m_5, m_6, m_7, m_8, m_9, m_10, z_1, z_2, z_3, z_4, z_5, z_6, z_7, z_8, z_9, z_10, minus_z_Q),
        (C_1, C_2, C_3, C_4, C_5, C_6, C_7, C_8, C_9, C_10, P, Q, V),
        (X_1, X_2, X_3, X_4, X_5, X_6, X_7, X_8, X_9, X_10, A, B)
        :
        C_1 = (P ^ m_1 * A ^ z_1 ) &&
        C_2 = (P ^ m_2 * A ^ z_2 ) &&
        C_3 = (P ^ m_3 * A ^ z_3 ) &&
        C_4 = (P ^ m_4 * A ^ z_4 ) &&
        C_5 = (P ^ m_5 * A ^ z_5 ) &&
        C_6 = (P ^ m_6 * A ^ z_6 ) &&
        C_7 = (P ^ m_7 * A ^ z_7 ) &&
        C_8 = (P ^ m_8 * A ^ z_8 ) &&
        C_9 = (P ^ m_9 * A ^ z_9 ) &&
        C_10 = (P ^ m_10 * A ^ z_10 ) &&
        V = (X_1^m_1 * X_2 ^ m_2* X_3 ^ m_3* X_4 ^ m_4* X_5 ^ m_5* X_6 ^ m_6
           * X_7 ^ m_7* X_8 ^ m_8* X_9 ^ m_9* X_10 ^ m_10* Q ^ minus_z_Q)
    }
}

define_proof! {dleq, "DLEQ proof", (x), (A, B, H), (G) : A = (G ^ x) && B = (H ^ x) }
