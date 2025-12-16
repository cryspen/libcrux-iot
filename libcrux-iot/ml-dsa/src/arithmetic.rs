use crate::{
    constants::{Gamma2, COEFFICIENTS_IN_RING_ELEMENT},
    helper::cloop,
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[cfg(not(feature = "stack"))]
use libcrux_secrets::Classify as _;

#[inline(always)]
pub(crate) fn vector_infinity_norm_exceeds<SIMDUnit: Operations>(
    vector: &[PolynomialRingElement<SIMDUnit>],
    bound: i32,
) -> bool {
    let mut result = false;
    cloop! {
        for ring_element in vector.iter() {
            result = result || ring_element.infinity_norm_exceeds(bound);
        }
    }

    result
}

#[inline(always)]
pub(crate) fn shift_left_then_reduce<SIMDUnit: Operations, const SHIFT_BY: i32>(
    re: &mut PolynomialRingElement<SIMDUnit>,
) {
    for i in 0..re.simd_units.len() {
        SIMDUnit::shift_left_then_reduce::<SHIFT_BY>(&mut re.simd_units[i]);
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

#[inline(always)]
pub(crate) fn power2round_vector<SIMDUnit: Operations>(
    t0: &mut [PolynomialRingElement<SIMDUnit>],
    t1: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..t0.len() {
        for j in 0..t0[i].simd_units.len() {
            SIMDUnit::power2round(&mut t0[i].simd_units[j], &mut t1[i].simd_units[j]);
        }
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

#[inline(always)]
pub(crate) fn decompose_vector<SIMDUnit: Operations>(
    dimension: usize,
    gamma2: Gamma2,
    t: &[PolynomialRingElement<SIMDUnit>],
    low: &mut [PolynomialRingElement<SIMDUnit>],
    high: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..dimension {
        for j in 0..low[0].simd_units.len() {
            SIMDUnit::decompose(
                gamma2,
                &t[i].simd_units[j],
                &mut low[i].simd_units[j],
                &mut high[i].simd_units[j],
            );
        }
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

#[inline(always)]
pub(crate) fn make_hint<SIMDUnit: Operations>(
    low: &[PolynomialRingElement<SIMDUnit>],
    high: &[PolynomialRingElement<SIMDUnit>],
    gamma2: i32,
    hint: &mut [[i32; COEFFICIENTS_IN_RING_ELEMENT]],
) -> usize {
    let mut true_hints = 0;
    let mut hint_simd = PolynomialRingElement::<SIMDUnit>::zero();

    for i in 0..low.len() {
        for j in 0..hint_simd.simd_units.len() {
            let one_hints_count = SIMDUnit::compute_hint(
                &low[i].simd_units[j],
                &high[i].simd_units[j],
                gamma2,
                &mut hint_simd.simd_units[j],
            );

            true_hints += one_hints_count;
        }

        hint[i] = hint_simd.to_i32_array();
    }

    true_hints
}

#[inline(always)]
#[cfg(feature = "stack")]
pub(crate) fn use_hint_i<SIMDUnit: Operations>(
    max_ones_in_hint: usize,
    rows_in_a: usize,
    gamma2: Gamma2,
    hint_serialized: &[u8],
    i: usize,
    previous_true_hints_seen: &mut usize,
    re_vector: &mut PolynomialRingElement<SIMDUnit>, // precondition: should hold w'_approx[i], postcondition: holds w'_1[i]
    poly_slot_a: &mut PolynomialRingElement<SIMDUnit>, // no precondition, will be clobbered
) -> Result<(), crate::VerificationError> {
    use libcrux_secrets::ClassifyRef;

    let mut hint_deserialized = [0i32; COEFFICIENTS_IN_RING_ELEMENT];
    crate::encoding::signature::deserialize_hint(
        rows_in_a,
        max_ones_in_hint,
        hint_serialized,
        i,
        &mut hint_deserialized,
        previous_true_hints_seen,
    )?;
    PolynomialRingElement::<SIMDUnit>::from_i32_array(
        hint_deserialized.classify_ref(),
        poly_slot_a,
    );

    for j in 0..re_vector.simd_units.len() {
        SIMDUnit::use_hint(
            gamma2,
            &re_vector.simd_units[j],
            &mut poly_slot_a.simd_units[j],
        );
    }
    *re_vector = *poly_slot_a;

    Ok(())
}

#[inline(always)]
#[cfg(not(feature = "stack"))]
pub(crate) fn use_hint<SIMDUnit: Operations>(
    gamma2: Gamma2,
    hint: &[[i32; COEFFICIENTS_IN_RING_ELEMENT]],
    re_vector: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..re_vector.len() {
        let mut tmp = PolynomialRingElement::zero();
        PolynomialRingElement::<SIMDUnit>::from_i32_array(&hint[i].classify(), &mut tmp);

        for j in 0..re_vector[0].simd_units.len() {
            SIMDUnit::use_hint(gamma2, &re_vector[i].simd_units[j], &mut tmp.simd_units[j]);
        }
        re_vector[i] = tmp;
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}
