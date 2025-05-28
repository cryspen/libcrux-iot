use super::arithmetic::*;

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
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[cfg_attr(hax, hax_lib::requires(fe < (FIELD_MODULUS as u16)))]
#[cfg_attr(hax, hax_lib::ensures(|result| fstar!(r#"((833 <= v fe && v fe <= 2496) ==> v result == 1) /\
						    (~(833 <=  v fe && v fe <= 2496) ==> v result == 0)"#)))]
pub(crate) fn compress_message_coefficient(fe: u16) -> u8 {
    // The approach used here is inspired by:
    // https://github.com/cloudflare/circl/blob/main/pke/kyber/internal/common/poly.go#L150

    // If 833 <= fe <= 2496,
    // then -832 <= shifted <= 831
    let shifted: i16 = 1664 - (fe as i16);
    hax_lib::fstar!(r#"assert (v $shifted == 1664 - v $fe)"#);

    // If shifted < 0, then
    // (shifted >> 15) ^ shifted = flip_bits(shifted) = -shifted - 1, and so
    // if -832 <= shifted < 0 then 0 < shifted_positive <= 831
    //
    // If shifted >= 0 then
    // (shifted >> 15) ^ shifted = shifted, and so
    // if 0 <= shifted <= 831 then 0 <= shifted_positive <= 831
    let mask = shifted >> 15;
    hax_lib::fstar!(
        "assert (v $mask = v $shifted / pow2 15);
        assert (if v $shifted < 0 then $mask = ones else $mask = zero)"
    );
    let shifted_to_positive = mask ^ shifted;
    hax_lib::fstar!(
        "logxor_lemma $shifted $mask;
        assert (v $shifted < 0 ==> v $shifted_to_positive = v (lognot $shifted));
        neg_equiv_lemma $shifted;
        assert (v (lognot $shifted) = -(v $shifted) -1);
        assert (v $shifted >= 0 ==> v $shifted_to_positive = v ($mask `logxor` $shifted));
        assert (v $shifted >= 0 ==> $mask = zero);
        assert (v $shifted >= 0 ==> $mask ^. $shifted = $shifted);
        assert (v $shifted >= 0 ==> v $shifted_to_positive = v $shifted);
        assert ($shifted_to_positive >=. mk_i16 0)"
    );

    let shifted_positive_in_range = shifted_to_positive - 832;
    hax_lib::fstar!(
        "assert (1664 - v $fe >= 0 ==> v $shifted_positive_in_range == 832 - v $fe);
        assert (1664 - v $fe < 0 ==> v $shifted_positive_in_range == -2497 + v $fe)"
    );

    // If x <= 831, then x - 832 <= -1, and so x - 832 < 0, which means
    // the most significant bit of shifted_positive_in_range will be 1.
    let r0 = shifted_positive_in_range >> 15;
    let r1: i16 = r0 & 1;
    let res = r1 as u8;
    hax_lib::fstar!(
        r#"assert (v $r0 = v $shifted_positive_in_range / pow2 15);
        assert (if v $shifted_positive_in_range < 0 then $r0 = ones else $r0 = zero);
        logand_lemma (mk_i16 1) $r0; 
        assert (if v $shifted_positive_in_range < 0 then $r1 = mk_i16 1 else $r1 = mk_i16 0);
        assert ((v $fe >= 833 && v $fe <= 2496) ==> $r1 = mk_i16 1);
        assert (v $fe < 833 ==> $r1 = mk_i16 0);
        assert (v $fe > 2496 ==> $r1 = mk_i16 0);
        assert (v $res = v $r1)"#
    );
    res
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
#[cfg_attr(hax,
    hax_lib::requires(
        (coefficient_bits == 4 ||
         coefficient_bits == 5 ||
         coefficient_bits == 10 ||
         coefficient_bits == 11) &&
         fe < (FIELD_MODULUS as u16)))]
#[cfg_attr(hax,
     hax_lib::ensures(
     |result| result >= 0 && result < 2i16.pow(coefficient_bits as u32)))]
pub(crate) fn compress_ciphertext_coefficient(coefficient_bits: u8, fe: u16) -> FieldElement {
    // hax_debug_assert!(
    //     coefficient_bits == 4
    //         || coefficient_bits == 5
    //         || coefficient_bits == 10
    //         || coefficient_bits == 11
    // );
    // hax_debug_assert!(fe <= (FIELD_MODULUS as u16));

    // This has to be constant time due to:
    // https://groups.google.com/a/list.nist.gov/g/pqc-forum/c/ldX0ThYJuBo/m/ovODsdY7AwAJ
    let mut compressed = (fe as u64) << coefficient_bits;
    compressed += 1664 as u64;

    compressed *= 10_321_340;
    compressed >>= 35;

    get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement
}

pub(crate) fn decompress_1(input: i16) -> i16 {
    -input & 1665
}

pub(crate) fn decompress_ciphertext_coefficient(input: i16, coefficient_bits: i32) -> i16 {
    let mut decompressed = input as i32 * FIELD_MODULUS as i32;
    decompressed = (decompressed << 1) + (1i32 << coefficient_bits);
    decompressed = decompressed >> (coefficient_bits + 1);
    decompressed as i16
}
