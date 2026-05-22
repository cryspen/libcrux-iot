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

#[cfg(test)]
mod cross_spec {
    //! Sub-API cross-spec for the `Vector` trait's compression primitives.
    //! Anchors FIPS-203 Algorithm 4/5 with the compress/decompress
    //! definitions in §4.2.1.
    use super::portable::PortableVector;
    use super::Operations;
    use libcrux_secrets::{Classify, Declassify};

    /// `compress<d>` then `decompress_ciphertext_coefficient<d>` is the
    /// identity on values already within range [0, 2^d), matching the
    /// spec's `compress ∘ decompress` (`compress_decompress_roundtrip`).
    #[test]
    fn compress_decompress_roundtrip_d4() {
        // Build a vector of values in [0, 16).
        let mut v = PortableVector::ZERO();
        for i in 0..16 {
            v.elements[i] = ((i as i16) % 16).classify();
        }
        let mut compressed = v;
        PortableVector::compress::<4>(&mut compressed);
        let mut roundtrip = compressed;
        PortableVector::decompress_ciphertext_coefficient::<4>(&mut roundtrip);
        PortableVector::compress::<4>(&mut roundtrip);
        for i in 0..16 {
            assert_eq!(
                compressed.elements[i].declassify(),
                roundtrip.elements[i].declassify(),
                "compress(decompress(compress(x))) != compress(x) for d=4 at index {}",
                i
            );
        }
    }

    /// Spec `compress(_, 1)` matches impl `compress_1` on the same input.
    /// FIPS-203 §6.2 corresponds to d=1 with input ∈ {0, 1}.
    #[test]
    fn compress_1_matches_spec_zero() {
        let v = PortableVector::ZERO();
        let mut compressed = v;
        PortableVector::compress_1(&mut compressed);
        for i in 0..16 {
            assert_eq!(
                compressed.elements[i].declassify(),
                0,
                "compress_1(0) should be 0 at index {}",
                i
            );
        }
    }
}
