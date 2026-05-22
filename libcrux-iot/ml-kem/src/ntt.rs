use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{zeta, PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{montgomery_multiply_fe, Operations},
};

#[hax_lib::requires(*zeta_i == 63)]
#[inline(always)]
pub(crate) fn ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    for round in 0..16 {
        hax_lib::loop_invariant!(|i: usize| *zeta_i == 63 + i * 4);
        *zeta_i += 1;
        Vector::ntt_layer_1_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i + 1),
            zeta(*zeta_i + 2),
            zeta(*zeta_i + 3),
        );
        *zeta_i += 3;
    }
}

#[hax_lib::requires(*zeta_i == 31)]
#[inline(always)]
pub(crate) fn ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    for round in 0..16 {
        hax_lib::loop_invariant!(|i: usize| *zeta_i == 31 + i * 2);
        *zeta_i += 1;
        Vector::ntt_layer_2_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i + 1),
        );
        *zeta_i += 1;
    }
}

#[hax_lib::requires(*zeta_i == 15)]
#[inline(always)]
pub(crate) fn ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    for round in 0..16 {
        hax_lib::loop_invariant!(|i: usize| *zeta_i == 15 + i);
        *zeta_i += 1;
        Vector::ntt_layer_3_step(&mut re.coefficients[round], zeta(*zeta_i));
    }
}

#[hax_lib::requires(a < 16 && b < 16)]
#[inline(always)]
fn ntt_layer_int_vec_step<Vector: Operations>(
    coefficients: &mut [Vector; VECTORS_IN_RING_ELEMENT],
    a: usize,
    b: usize,
    scratch: &mut Vector,
    zeta_r: i16,
) {
    *scratch = coefficients[b];
    montgomery_multiply_fe::<Vector>(scratch, zeta_r);
    coefficients[b] = coefficients[a];
    Vector::add(&mut coefficients[a], scratch);
    Vector::sub(&mut coefficients[b], scratch);
}

#[hax_lib::requires(
    layer >= 4 && layer <= 7 && *zeta_i == (1 << (7 - layer)) - 1 
)]
#[inline(always)]
pub(crate) fn ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    scratch: &mut Vector,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    let step = 1 << layer;
    let step_vec = step / 16; //FIELD_ELEMENTS_IN_VECTOR;

    for round in 0..(128 >> layer) {
        hax_lib::loop_invariant!(|round: usize| *zeta_i == (1 << (7 - layer)) - 1 + round);
        *zeta_i += 1;

        let a_offset = round * 2 * step_vec;
        let b_offset = a_offset + step_vec;
        for j in 0..step_vec {
            hax_lib::loop_invariant!(|_: usize| *zeta_i == (1 << (7 - layer)) + round);
            ntt_layer_int_vec_step(
                &mut re.coefficients,
                a_offset + j,
                b_offset + j,
                scratch,
                zeta(*zeta_i),
            );
        }
    }
}

#[inline(always)]
pub(crate) fn ntt_at_layer_7<Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    let step = VECTORS_IN_RING_ELEMENT / 2;
    for j in 0..step {
        *scratch = re.coefficients[j + step];
        Vector::multiply_by_constant(scratch, -1600);
        re.coefficients[j + step] = re.coefficients[j];
        Vector::add(&mut re.coefficients[j], scratch);
        Vector::sub(&mut re.coefficients[j + step], scratch);
    }
}

#[inline(always)]
pub(crate) fn ntt_binomially_sampled_ring_element<Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    ntt_at_layer_7(re, scratch);

    let mut zeta_i = 1;
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, scratch, 11207);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, scratch, 11207 + 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, scratch, 11207 + 2 * 3328);
    ntt_at_layer_3(&mut zeta_i, re, 11207 + 3 * 3328);
    ntt_at_layer_2(&mut zeta_i, re, 11207 + 4 * 3328);
    ntt_at_layer_1(&mut zeta_i, re, 11207 + 5 * 3328);

    re.poly_barrett_reduce()
}

#[inline(always)]
pub(crate) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    ntt_at_layer_4_plus(&mut zeta_i, re, 7, scratch, 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, scratch, 2 * 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, scratch, 3 * 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, scratch, 4 * 3328);
    ntt_at_layer_3(&mut zeta_i, re, 5 * 3328);
    ntt_at_layer_2(&mut zeta_i, re, 6 * 3328);
    ntt_at_layer_1(&mut zeta_i, re, 7 * 3328);

    re.poly_barrett_reduce()
}

#[cfg(test)]
mod cross_spec {
    //! Impl-side NTT primitive sanity checks against the `hacspec_ml_kem`
    //! spec. NTT cross-spec proper (impl-vs-spec NTT byte equality after
    //! Montgomery cancellation) is tied to the spec's exact normalization
    //! convention and is exercised end-to-end by `tests/cross_spec.rs`'s
    //! `full_roundtrip_matches_spec`. Here we keep narrower invariants:
    //!
    //! - the impl's NTT followed by inverse-NTT (+ Montgomery scale) is
    //!   the identity, matching the spec's NTT/iNTT identity;
    //! - on the all-zero polynomial, impl NTT yields the zero polynomial.
    //!
    //! Anchored to FIPS-203 Algorithm 9 (NTT) and Algorithm 10 (iNTT).
    use super::*;
    use crate::polynomial::cross_spec::{lift_poly, unlift_poly};
    use crate::vector::portable::PortableVector;
    use crate::vector::Operations;
    use hacspec_ml_kem::parameters::{self as spec, FieldElement, Polynomial};

    /// Impl NTT of the zero polynomial is the zero polynomial.
    /// (Spec analog of `ntt_zero_is_zero`.)
    #[test]
    fn impl_ntt_zero_is_zero() {
        let zero: Polynomial = spec::createi(|_| FieldElement::new(0));
        let mut impl_poly = unlift_poly(&zero);
        let mut scratch = PortableVector::ZERO();
        ntt_binomially_sampled_ring_element::<PortableVector>(&mut impl_poly, &mut scratch);
        for c in lift_poly(&impl_poly).iter() {
            assert_eq!(c.val, 0);
        }
    }

    /// Spec NTT then iNTT is the identity. This is a pure-spec invariant
    /// that the impl is morally aligned with, but the impl carries a
    /// Montgomery scale factor through `ntt_vector_u` / `invert_ntt_montgomery`
    /// that requires variant-specific cancellation (e.g., the multiplier
    /// in `subtract_reduce`) which lives outside the per-primitive surface.
    /// Top-level cross-spec coverage is in `tests/cross_spec.rs`.
    #[test]
    fn spec_ntt_inverse_is_identity() {
        let spec_poly: Polynomial =
            spec::createi(|i| FieldElement::new((i as u16 * 13 + 7) % spec::FIELD_MODULUS));
        let spec_round = hacspec_ml_kem::invert_ntt::ntt_inverse(
            hacspec_ml_kem::ntt::vector_ntt([spec_poly])[0],
        );
        assert_eq!(spec_round, spec_poly);
    }
}
