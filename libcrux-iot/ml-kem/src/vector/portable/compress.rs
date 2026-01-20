use super::arithmetic::*;
use super::vector_type::*;
use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;
use crate::vector::FIELD_MODULUS;
use libcrux_secrets::*;

/// The `compress_*` functions implement the `Compress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.5), which is defined as:
///
/// ```plaintext
/// Compress_d: ℤq -> ℤ_{2ᵈ}
/// Compress_d(x) = ⌈(2ᵈ/q)·x⌋
/// ```
///
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
///
/// ```plaintext
/// Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
///               = ⌊(2^{d+1}·x + q) / 2q⌋
/// ```
///
/// For further information about the function implementations, consult the
/// `implementation_notes.pdf` document in this directory.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[inline(always)]
pub(crate) fn compress_message_coefficient(fe: U16) -> U8 {
    // The approach used here is inspired by:
    // https://github.com/cloudflare/circl/blob/main/pke/kyber/internal/common/poly.go#L150

    // If 833 <= fe <= 2496,
    // then -832 <= shifted <= 831
    let shifted = 1664i16.classify().wrapping_sub(fe.as_i16());

    // If shifted < 0, then
    // (shifted >> 15) ^ shifted = flip_bits(shifted) = -shifted - 1, and so
    // if -832 <= shifted < 0 then 0 < shifted_positive <= 831
    //
    // If shifted >= 0 then
    // (shifted >> 15) ^ shifted = shifted, and so
    // if 0 <= shifted <= 831 then 0 <= shifted_positive <= 831
    let mask = shifted >> 15;

    let shifted_to_positive = mask ^ shifted;

    let shifted_positive_in_range = shifted_to_positive.wrapping_sub(832);

    // If x <= 831, then x - 832 <= -1, and so x - 832 < 0, which means
    // the most significant bit of shifted_positive_in_range will be 1.
    let r0 = shifted_positive_in_range >> 15;
    let r1 = r0 & 1i16;
    let res = r1.as_u8();

    res
}

#[hax_lib::requires(coefficient_bits <= 16)]
#[inline(always)]
pub(crate) fn compress_ciphertext_coefficient(coefficient_bits: u8, fe: U16) -> FieldElement {
    // This has to be constant time due to:
    // https://groups.google.com/a/list.nist.gov/g/pqc-forum/c/ldX0ThYJuBo/m/ovODsdY7AwAJ
    let mut compressed = fe.as_u64() << coefficient_bits;
    compressed = compressed.wrapping_add(1664);

    compressed = compressed.wrapping_mul(10_321_340);
    compressed >>= 35;

    get_n_least_significant_bits(coefficient_bits, compressed.as_u32()).as_i16()
}

#[inline(always)]
pub(crate) fn compress_1(a: &mut PortableVector) {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        a.elements[i] = compress_message_coefficient(a.elements[i].as_u16()).as_i16();
    }
}

#[hax_lib::requires(COEFFICIENT_BITS >= 0 && COEFFICIENT_BITS <= 16)]
#[inline(always)]
pub(crate) fn compress<const COEFFICIENT_BITS: i32>(a: &mut PortableVector) {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        a.elements[i] =
            compress_ciphertext_coefficient(COEFFICIENT_BITS as u8, a.elements[i].as_u16())
                .as_i16();
    }
}

#[hax_lib::requires(0 <= COEFFICIENT_BITS && COEFFICIENT_BITS < 31)]
#[inline(always)]
pub(crate) fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(
    a: &mut PortableVector,
) {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        let mut decompressed = a.elements[i]
            .as_i32()
            .wrapping_mul(FIELD_MODULUS.classify().as_i32());

        decompressed = (decompressed << 1).wrapping_add(1i32 << COEFFICIENT_BITS);

        decompressed = decompressed >> (COEFFICIENT_BITS + 1);

        a.elements[i] = decompressed.as_i16();
    }
}
