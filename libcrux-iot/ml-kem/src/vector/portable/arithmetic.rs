use super::vector_type::*;
use crate::vector::traits::{
    BARRETT_R, BARRETT_SHIFT, FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS,
    INVERSE_OF_MODULUS_MOD_MONTGOMERY_R,
};
use libcrux_secrets::*;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
pub type MontgomeryFieldElement = I16;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub type FieldElementTimesMontgomeryR = I16;

pub(crate) const MONTGOMERY_SHIFT: u8 = 16;

#[cfg(hax)]
pub(crate) const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
pub(crate) const BARRETT_MULTIPLIER: i32 = 20159;

#[hax_lib::requires(n <= 16)]
#[inline(always)]
pub(crate) fn get_n_least_significant_bits(n: u8, value: U32) -> U32 {
    let res = value & (1u32 << n).wrapping_sub(1);

    res
}

#[hax_lib::requires(array.len() == 16)]
#[inline(always)]
pub fn reducing_from_i32_array(array: &[I32], out: &mut PortableVector) {
    for i in 0..16 {
        out.elements[i] = montgomery_reduce_element(array[i]);
    }
}

#[inline(always)]
pub(crate) fn add(lhs: &mut PortableVector, rhs: &PortableVector) {
    #[cfg(hax)]
    let _lhs0 = (*lhs).clone();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] = lhs.elements[i].wrapping_add(rhs.elements[i]);
    }
}

#[inline(always)]
pub(crate) fn sub(lhs: &mut PortableVector, rhs: &PortableVector) {
    #[cfg(hax)]
    let _lhs0 = (*lhs).clone();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] = lhs.elements[i].wrapping_sub(rhs.elements[i]);
    }
}

#[inline(always)]
pub(crate) fn negate(vec: &mut PortableVector) {
    #[cfg(hax)]
    let _vec0 = (*vec).clone();

    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        vec.elements[i] = vec.elements[i].wrapping_neg();
    }
}

#[inline(always)]
pub(crate) fn multiply_by_constant(vec: &mut PortableVector, c: i16) {
    #[cfg(hax)]
    let _vec0 = (*vec).clone();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        vec.elements[i] = vec.elements[i].wrapping_mul(c);
    }
}

#[inline(always)]
pub(crate) fn bitwise_and_with_constant(vec: &mut PortableVector, c: i16) {
    #[cfg(hax)]
    let _vec0 = (*vec).clone();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        vec.elements[i] &= c;
    }
}

#[hax_lib::requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
#[inline(always)]
pub(crate) fn shift_right<const SHIFT_BY: i32>(vec: &mut PortableVector) {
    #[cfg(hax)]
    let _vec0 = (*vec).clone();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        vec.elements[i] >>= SHIFT_BY as u32;
    }
}

/// Note: This function is not secret independent
/// Only use with public values.
#[inline(always)]
pub(crate) fn cond_subtract_3329(vec: &mut PortableVector) {
    #[cfg(hax)]
    let _vec0 = vec.clone();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        if vec.elements[i].declassify() >= 3329 {
            vec.elements[i] = vec.elements[i].wrapping_sub(3329);
        }
    }
}

/// Signed Barrett Reduction
///
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
///
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
///
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
///
/// Note: The input bound is 28296 to prevent overflow in the multiplication of quotient by FIELD_MODULUS
///
#[inline(always)]
pub(crate) fn barrett_reduce_element(value: FieldElement) -> FieldElement {
    let t = (value.as_i32().wrapping_mul(BARRETT_MULTIPLIER)).wrapping_add(BARRETT_R >> 1);
    let quotient = (t >> (BARRETT_SHIFT as u32)).as_i16();

    let result = value.wrapping_sub(quotient.wrapping_mul(FIELD_MODULUS));

    result
}

#[inline(always)]
pub(crate) fn barrett_reduce(vec: &mut PortableVector) {
    #[cfg(hax)]
    let _vec0 = vec.clone();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        let vi = barrett_reduce_element(vec.elements[i]);
        vec.elements[i] = vi;
    }
}

/// Signed Montgomery Reduction
///
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
///
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
///
/// `|result| ≤ ceil(|value| / MONTGOMERY_R) + 1665
///
/// In particular, if `|value| ≤ FIELD_MODULUS-1 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS-1`.
/// And, if `|value| ≤ pow2 16 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS + 1664
///
pub(crate) fn montgomery_reduce_element(value: I32) -> MontgomeryFieldElement {
    let k = (value.as_i16())
        .as_i32()
        .wrapping_mul(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R.classify().as_i32());

    let k_times_modulus = (k.as_i16().as_i32()).wrapping_mul(FIELD_MODULUS.classify().as_i32());

    let c = (k_times_modulus >> (MONTGOMERY_SHIFT as u32)).as_i16();

    let value_high = (value >> (MONTGOMERY_SHIFT as u32)).as_i16();

    let res = value_high.wrapping_sub(c);

    res
}

/// If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
///
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
#[inline(always)]
pub(crate) fn montgomery_multiply_fe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    let product = fe.as_i32().wrapping_mul(fer.as_i32());
    montgomery_reduce_element(product)
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(vec: &mut PortableVector, c: I16) {
    #[cfg(hax)]
    let _vec0 = (*vec).clone();
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        vec.elements[i] = montgomery_multiply_fe_by_fer(vec.elements[i], c)
    }
}
