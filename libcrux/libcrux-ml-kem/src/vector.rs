//! # Polynomials for libcrux
//!
//! This crate abstracts efficient implementations of polynomials for algorithms
//! such as ML-KEM and ML-DSA.
//!
//! The crate only defines a common API.
//! The actual implementations are in separate crates for different platforms for
//! performance reasons.
//!
//! FIXME: This is kyber specific for now.

pub(crate) mod traits;
pub(crate) use traits::{
    decompress_1, montgomery_multiply_fe, to_standard_domain, to_unsigned_representative,
    Operations, FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS,
};

pub mod portable;
