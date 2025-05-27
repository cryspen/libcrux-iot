use crate::{
    arithmetic::montgomery_multiply_fe_by_fer,
    polynomial::{zeta, PolynomialRingElement},
};

#[inline(always)]
pub(crate) fn ntt_binomially_sampled_ring_element(re: &mut PolynomialRingElement) {
    // Due to the small coefficient bound due to binomial sampling, we
    // can skip the Montgomery reductions in layer 7.
    let remaining_elements = &mut re.coefficients[..];

    let (a, b) = remaining_elements.split_at_mut(128);
    for j in 0..128 {
        let b_zeta = b[j] * -1600;
        b[j] = a[j] - b_zeta;
        a[j] += b_zeta;
    }

    let mut zeta_i = 1;
    for layer in (1..=6).rev() {
        let step = 1 << layer;

        // For every round, split off two `step_vec` sized slices from the front.
        let mut remaining_elements = &mut re.coefficients[..];
        for _round in 0..(128 >> layer) {
            zeta_i += 1;

            let (a, rest) = remaining_elements.split_at_mut(step);
            let (b, rest) = rest.split_at_mut(step);
            remaining_elements = rest;
            for j in 0..step {
                let b_zeta = montgomery_multiply_fe_by_fer(b[j], zeta(zeta_i));
                b[j] = a[j] - b_zeta;
                a[j] += b_zeta;
            }
        }
    }

    re.poly_barrett_reduce()
}

#[inline(always)]
pub(crate) fn ntt_vector_u(re: &mut PolynomialRingElement) {
    let mut zeta_i = 0;

    for layer in (1..=7).rev() {
        let step = 1 << layer;

        // For every round, split off two `step_vec` sized slices from the front.
        let mut remaining_elements = &mut re.coefficients[..];
        for _round in 0..(128 >> layer) {
            zeta_i += 1;

            let (a, rest) = remaining_elements.split_at_mut(step);
            let (b, rest) = rest.split_at_mut(step);
            remaining_elements = rest;
            for j in 0..step {
                let b_zeta = montgomery_multiply_fe_by_fer(b[j], zeta(zeta_i));
                b[j] = a[j] - b_zeta;
                a[j] += b_zeta;
            }
        }
    }
    re.poly_barrett_reduce()
}
