use libcrux_secrets::{ClassifyRef as _, U8};

use crate::{
    constants::{BYTES_PER_RING_ELEMENT, SHARED_SECRET_SIZE},
    helper::cloop,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{decompress_1, to_unsigned_representative, Operations},
};

#[inline(always)]
pub(super) fn to_unsigned_field_modulus<Vector: Operations>(a: &Vector, out: &mut Vector) {
    to_unsigned_representative::<Vector>(a, out)
}

#[hax_lib::requires(serialized.len() == SHARED_SECRET_SIZE)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
pub(super) fn compress_then_serialize_message<Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [U8],
    scratch: &mut Vector,
) {
    for i in 0..16 {
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == SHARED_SECRET_SIZE });
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress_1(scratch);

        Vector::serialize_1(scratch, &mut serialized[2 * i..2 * i + 2]);
    }
}

#[inline(always)]
pub(super) fn deserialize_then_decompress_message<Vector: Operations>(
    serialized: &[U8; SHARED_SECRET_SIZE],
    re: &mut PolynomialRingElement<Vector>,
) {
    for i in 0..16 {
        Vector::deserialize_1(&serialized[2 * i..2 * i + 2], &mut re.coefficients[i]);
        decompress_1::<Vector>(&mut re.coefficients[i]);
    }
}

#[hax_lib::requires(serialized.len() == BYTES_PER_RING_ELEMENT)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
pub(super) fn serialize_uncompressed_ring_element<Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    scratch: &mut Vector,
    serialized: &mut [U8],
) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == BYTES_PER_RING_ELEMENT);

    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == BYTES_PER_RING_ELEMENT });

        to_unsigned_field_modulus(&re.coefficients[i], scratch);

        Vector::serialize_12(scratch, &mut serialized[24 * i..24 * i + 24]);
    }
}

#[hax_lib::requires(serialized.len() == BYTES_PER_RING_ELEMENT)]
#[inline(always)]
pub(super) fn deserialize_to_uncompressed_ring_element<Vector: Operations>(
    serialized: &[U8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            Vector::deserialize_12(bytes, &mut re.coefficients[i]);
        }
    }
}

/// Only use with public values.
///
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
#[hax_lib::requires(
    serialized.len() == BYTES_PER_RING_ELEMENT
)]
#[inline(always)]
pub(crate) fn deserialize_to_reduced_ring_element<Vector: Operations>(
    serialized: &[U8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            Vector::deserialize_12(bytes, &mut re.coefficients[i]);
            Vector::cond_subtract_3329(&mut re.coefficients[i]);
        }
    }
}

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
///
/// This function MUST NOT be used on secret inputs.
#[hax_lib::requires(deserialized_pk.len() == K && public_key.len() / BYTES_PER_RING_ELEMENT == K)]
#[hax_lib::ensures(|_| future(deserialized_pk).len() == deserialized_pk.len())]
#[inline(always)]
pub(super) fn deserialize_ring_elements_reduced<const K: usize, Vector: Operations>(
    public_key: &[u8],
    deserialized_pk: &mut [PolynomialRingElement<Vector>],
) {
    cloop! {
        for (i, ring_element) in public_key
            .chunks_exact(BYTES_PER_RING_ELEMENT)
            .enumerate()
        {
            hax_lib::loop_invariant!(|i: usize| {
                deserialized_pk.len() == K
            });

            deserialize_to_reduced_ring_element(ring_element.classify_ref(), &mut deserialized_pk[i]);
        }
    };
}

#[hax_lib::requires(serialized.len() == BLOCK_LEN && BLOCK_LEN >= VECTORS_IN_RING_ELEMENT * 20)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_10<const BLOCK_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == BLOCK_LEN);
    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == BLOCK_LEN });
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress::<10>(scratch);

        Vector::serialize_10(scratch, &mut serialized[20 * i..20 * i + 20]);
    }
}

#[hax_lib::requires(serialized.len() == BLOCK_LEN && BLOCK_LEN >= VECTORS_IN_RING_ELEMENT * 22)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_11<const BLOCK_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == BLOCK_LEN);

    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == BLOCK_LEN });
        to_unsigned_representative::<Vector>(&re.coefficients[i], scratch);
        Vector::compress::<11>(scratch);

        Vector::serialize_11(scratch, &mut serialized[22 * i..22 * i + 22]);
    }
}

#[hax_lib::requires(
    ((U_COMPRESSION_FACTOR == 10 && BLOCK_LEN >= VECTORS_IN_RING_ELEMENT * 20)
      || (U_COMPRESSION_FACTOR == 11 && BLOCK_LEN >= VECTORS_IN_RING_ELEMENT * 22)) &&
    serialized.len() == BLOCK_LEN
)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_u<
    const U_COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
    Vector: Operations,
>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    match U_COMPRESSION_FACTOR as u32 {
        10 => compress_then_serialize_10::<BLOCK_LEN, Vector>(re, serialized, scratch),
        11 => compress_then_serialize_11::<BLOCK_LEN, Vector>(re, serialized, scratch),
        _ => unreachable!(),
    }
}

#[hax_lib::requires(serialized.len() == 128)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_4<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == 128 });
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress::<4>(scratch);

        Vector::serialize_4(scratch, &mut serialized[8 * i..8 * i + 8]);
    }
}

#[hax_lib::requires(serialized.len() == 160)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_5<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == 160 });
        to_unsigned_representative::<Vector>(&re.coefficients[i], scratch);
        Vector::compress::<5>(scratch);

        Vector::serialize_5(scratch, &mut serialized[10 * i..10 * i + 10]);
    }
}

#[hax_lib::requires(
    out.len() == C2_LEN &&
    (V_COMPRESSION_FACTOR == 4 && C2_LEN == 128 ||
        V_COMPRESSION_FACTOR == 5 && C2_LEN == 160))]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_v<
    const K: usize,
    const V_COMPRESSION_FACTOR: usize,
    const C2_LEN: usize,
    Vector: Operations,
>(
    re: PolynomialRingElement<Vector>,
    out: &mut [u8],
    scratch: &mut Vector,
) {
    match V_COMPRESSION_FACTOR as u32 {
        4 => compress_then_serialize_4::<Vector>(re, out, scratch),
        5 => compress_then_serialize_5::<Vector>(re, out, scratch),
        _ => unreachable!(),
    }
}

#[hax_lib::requires(
    serialized.len() == 320
)]
#[inline(always)]
fn deserialize_then_decompress_10<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(20).enumerate() {
            Vector::deserialize_10(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<10>(&mut re.coefficients[i]);
        }
    }
}

#[hax_lib::requires(
    serialized.len() == 352
)]
#[inline(always)]
fn deserialize_then_decompress_11<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(22).enumerate() {
            Vector::deserialize_11(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<11>(&mut re.coefficients[i]);
        }
    }
}

#[hax_lib::requires(
    (U_COMPRESSION_FACTOR == 10 || U_COMPRESSION_FACTOR == 11) &&
    serialized.len() == 32 * U_COMPRESSION_FACTOR
)]
#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_u<
    const U_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
    output: &mut PolynomialRingElement<Vector>,
) {
    match U_COMPRESSION_FACTOR as u32 {
        10 => deserialize_then_decompress_10::<Vector>(serialized, output),
        11 => deserialize_then_decompress_11::<Vector>(serialized, output),
        _ => unreachable!(),
    };
}

#[inline(always)]
#[hax_lib::requires(
    serialized.len() == 128
)]
fn deserialize_then_decompress_4<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(8).enumerate() {
            Vector::deserialize_4(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<4>(&mut re.coefficients[i]);
        }
    }
}

#[hax_lib::requires(
    serialized.len() == 160
)]
#[inline(always)]
fn deserialize_then_decompress_5<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(10).enumerate() {
            Vector::deserialize_5(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<5>(&mut re.coefficients[i]);
        }
    }
}

#[hax_lib::requires(
    (V_COMPRESSION_FACTOR == 4 || V_COMPRESSION_FACTOR == 5) &&
    serialized.len() == 32 * V_COMPRESSION_FACTOR)]
#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_v<
    const K: usize,
    const V_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
    output: &mut PolynomialRingElement<Vector>,
) {
    match V_COMPRESSION_FACTOR as u32 {
        4 => deserialize_then_decompress_4::<Vector>(serialized, output),
        5 => deserialize_then_decompress_5::<Vector>(serialized, output),
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod cross_spec {
    //! Sub-API cross-spec: impl serialize/deserialize against spec
    //! `byte_encode` / `byte_decode` (FIPS-203 Algorithms 4 & 5) and
    //! `compress_then_serialize_message` / `deserialize_then_decompress_message`
    //! (FIPS-203 Algorithms 4 with d=1 + compress/decompress).
    use super::*;
    use crate::polynomial::cross_spec::{lift_poly, unlift_poly};
    use crate::vector::portable::PortableVector;
    use libcrux_secrets::{Classify, Declassify, DeclassifyRef as _};
    use hacspec_ml_kem::parameters::{self as spec, FieldElement, Polynomial};

    /// impl `serialize_uncompressed_ring_element` (=ByteEncode₁₂) matches
    /// spec `byte_encode::<384, 3072>(_, 12)` on the same input.
    #[test]
    fn serialize_12_matches_spec() {
        let spec_poly: Polynomial =
            spec::createi(|i| FieldElement::new((i as u16 * 13) % spec::FIELD_MODULUS));

        // Spec
        let spec_encoded =
            hacspec_ml_kem::serialize::byte_encode::<384, 3072>(spec_poly, 12);

        // Impl
        let impl_poly = unlift_poly(&spec_poly);
        let mut impl_encoded = [0u8.classify(); BYTES_PER_RING_ELEMENT];
        let mut scratch = PortableVector::ZERO();
        serialize_uncompressed_ring_element::<PortableVector>(
            &impl_poly,
            &mut scratch,
            &mut impl_encoded,
        );
        let mut impl_encoded_pub = [0u8; BYTES_PER_RING_ELEMENT];
        for i in 0..BYTES_PER_RING_ELEMENT {
            impl_encoded_pub[i] = impl_encoded[i].declassify();
        }

        assert_eq!(&impl_encoded_pub[..], &spec_encoded[..]);
    }

    /// impl `deserialize_to_reduced_ring_element` (=ByteDecode₁₂)
    /// matches spec `byte_decode::<384, 3072>(_, 12)` on identical bytes.
    #[test]
    fn deserialize_12_matches_spec() {
        // Build canonical bytes by going through the spec first.
        let spec_poly: Polynomial =
            spec::createi(|i| FieldElement::new((i as u16 * 17 + 3) % spec::FIELD_MODULUS));
        let bytes = hacspec_ml_kem::serialize::byte_encode::<384, 3072>(spec_poly, 12);

        let spec_decoded =
            hacspec_ml_kem::serialize::byte_decode::<384, 3072>(&bytes, 12);

        let mut impl_decoded = PolynomialRingElement::<PortableVector>::ZERO();
        let bytes_classified: [U8; BYTES_PER_RING_ELEMENT] = bytes.classify();
        deserialize_to_reduced_ring_element::<PortableVector>(
            &bytes_classified[..],
            &mut impl_decoded,
        );

        assert_eq!(lift_poly(&impl_decoded), spec_decoded);
    }

    /// Roundtrip the message-compression-and-serialize path through impl,
    /// and verify the resulting bytes equal a spec roundtrip
    /// (`compress_then_serialize_message ∘ deserialize_then_decompress_message`).
    /// Anchors FIPS-203 §6.2 message compression.
    #[test]
    fn message_serialize_roundtrip_matches_spec() {
        let msg_bytes: [u8; 32] = [0xABu8; 32];

        // Spec roundtrip.
        let spec_round = hacspec_ml_kem::serialize::compress_then_serialize_message(
            hacspec_ml_kem::serialize::deserialize_then_decompress_message(&msg_bytes),
        );
        assert_eq!(msg_bytes, spec_round, "spec message roundtrip must be id");

        // Impl roundtrip.
        let msg_classified: [U8; 32] = msg_bytes.classify();
        let mut impl_poly = PolynomialRingElement::<PortableVector>::ZERO();
        deserialize_then_decompress_message::<PortableVector>(&msg_classified, &mut impl_poly);

        let mut impl_out = [0u8.classify(); 32];
        let mut scratch = PortableVector::ZERO();
        compress_then_serialize_message::<PortableVector>(&impl_poly, &mut impl_out, &mut scratch);

        let impl_out_decl = impl_out.declassify_ref().to_vec();
        assert_eq!(&impl_out_decl[..], &msg_bytes[..]);
    }
}
