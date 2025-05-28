use crate::{
    arithmetic::{barrett_reduce_element, montgomery_multiply_fe_by_fer},
    polynomial::{zeta, PolynomialRingElement},
};

#[inline(always)]
pub(crate) fn invert_ntt_montgomery<const K: usize>(re: &mut PolynomialRingElement) {
    let mut zeta_i = super::constants::COEFFICIENTS_IN_RING_ELEMENT / 2;

    for layer in 1..=7 {
        let step = 1 << layer;

        // For every round, split off two `step_vec` sized slices from the front.
        let mut remaining_elements = &mut re.coefficients[..];
        for _round in 0..(128 >> layer) {
            zeta_i -= 1;

            let (a, rest) = remaining_elements.split_at_mut(step);
            let (b, rest) = rest.split_at_mut(step);
            remaining_elements = rest;
            for j in 0..step {
                let tmp = b[j];
                b[j] -= a[j];
                b[j] = montgomery_multiply_fe_by_fer(b[j], zeta(zeta_i));
                a[j] = barrett_reduce_element(a[j] + tmp);
            }
        }
    }
    re.poly_barrett_reduce()
}
