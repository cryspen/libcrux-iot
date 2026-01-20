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
    // hax_lib::fstar!(r#"assert (v $BYTES_PER_RING_ELEMENT / 24 == 16)"#);
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
    // hax_lib::fstar!(r#"assert (v $BYTES_PER_RING_ELEMENT / 24 == 16)"#);
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

#[hax_lib::requires(serialized.len() == OUT_LEN && OUT_LEN >= VECTORS_IN_RING_ELEMENT * 20)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_10<const OUT_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == OUT_LEN);
    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == OUT_LEN });
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress::<10>(scratch);

        Vector::serialize_10(scratch, &mut serialized[20 * i..20 * i + 20]);
    }
}

#[hax_lib::requires(serialized.len() == OUT_LEN && OUT_LEN >= VECTORS_IN_RING_ELEMENT * 22)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_11<const OUT_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == OUT_LEN);

    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == OUT_LEN });
        to_unsigned_representative::<Vector>(&re.coefficients[i], scratch);
        Vector::compress::<11>(scratch);

        Vector::serialize_11(scratch, &mut serialized[22 * i..22 * i + 22]);
    }
}

#[hax_lib::requires(hax_lib::implies(COMPRESSION_FACTOR == 10, OUT_LEN >= VECTORS_IN_RING_ELEMENT * 20).and(
                    hax_lib::implies(COMPRESSION_FACTOR == 11, OUT_LEN >= VECTORS_IN_RING_ELEMENT * 22).and(
                    serialized.len() == OUT_LEN && (COMPRESSION_FACTOR == 10 || COMPRESSION_FACTOR == 11))))]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
    Vector: Operations,
>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    match COMPRESSION_FACTOR as u32 {
        10 => compress_then_serialize_10::<OUT_LEN, Vector>(re, serialized, scratch),
        11 => compress_then_serialize_11::<OUT_LEN, Vector>(re, serialized, scratch),
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

#[hax_lib::requires(out.len() == OUT_LEN &&
    (COMPRESSION_FACTOR == 4 && OUT_LEN == 128 ||
        COMPRESSION_FACTOR == 5 && OUT_LEN == 160))]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_v<
    const K: usize,
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
    Vector: Operations,
>(
    re: PolynomialRingElement<Vector>,
    out: &mut [u8],
    scratch: &mut Vector,
) {
    match COMPRESSION_FACTOR as u32 {
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

#[hax_lib::requires((COMPRESSION_FACTOR == 4 || COMPRESSION_FACTOR == 5) && serialized.len() == 32 * COMPRESSION_FACTOR)]
#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
    output: &mut PolynomialRingElement<Vector>,
) {
    match COMPRESSION_FACTOR as u32 {
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

#[hax_lib::requires((COMPRESSION_FACTOR == 4 || COMPRESSION_FACTOR == 5) && serialized.len() == 32 * COMPRESSION_FACTOR)]
#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_v<
    const K: usize,
    const COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
    output: &mut PolynomialRingElement<Vector>,
) {
    match COMPRESSION_FACTOR as u32 {
        4 => deserialize_then_decompress_4::<Vector>(serialized, output),
        5 => deserialize_then_decompress_5::<Vector>(serialized, output),
        _ => unreachable!(),
    }
}
