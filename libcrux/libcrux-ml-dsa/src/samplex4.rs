use crate::{
    constants::Eta,
    hash_functions::{shake128, shake256},
    helper::cloop,
    polynomial::PolynomialRingElement,
    sample::{sample_four_error_ring_elements, sample_up_to_four_ring_elements_flat},
    simd::traits::Operations,
};

/// The x4 sampling implementation that is selected during multiplexing.
pub(crate) trait X4Sampler {
    /// Sample the matrix A using platform specific implementation.
    fn matrix_flat<SIMDUnit: Operations>(
        columns: usize,
        seed: &[u8],
        matrix: &mut [PolynomialRingElement<SIMDUnit>],
    );
}

#[inline(always)]
pub(crate) fn matrix_flat<SIMDUnit: Operations, Shake128: shake128::XofX4>(
    columns: usize,
    seed: &[u8],
    matrix: &mut [PolynomialRingElement<SIMDUnit>],
) {
    let mut rand_stack0 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack1 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack2 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack3 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut tmp_stack = [[0i32; 263], [0i32; 263], [0i32; 263], [0i32; 263]];

    cloop! {
        for start_index in (0..matrix.len()).step_by(4) {
            let elements_requested = if start_index + 4 <= matrix.len() {
                4
            } else {
                matrix.len() - start_index
            };
            sample_up_to_four_ring_elements_flat::<SIMDUnit, Shake128>(
                columns,
                seed,
                matrix,
                &mut rand_stack0,
                &mut rand_stack1,
                &mut rand_stack2,
                &mut rand_stack3,
                &mut tmp_stack,
                start_index,
                elements_requested,
            );
        }
    }

    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

/// Portable sampling
pub(crate) mod portable {
    use super::*;

    pub(crate) struct PortableSampler {}
    impl X4Sampler for PortableSampler {
        fn matrix_flat<SIMDUnit: Operations>(
            columns: usize,
            seed: &[u8],
            matrix: &mut [PolynomialRingElement<SIMDUnit>],
        ) {
            matrix_flat::<SIMDUnit, crate::hash_functions::portable::Shake128X4>(
                columns, seed, matrix,
            )
        }
    }
}

// Not inling this causes a 10x slow-down
#[inline(always)]
pub(crate) fn sample_s1_and_s2<SIMDUnit: Operations, Shake256X4: shake256::XofX4>(
    eta: Eta,
    seed: &[u8],
    s1_s2: &mut [PolynomialRingElement<SIMDUnit>],
) {
    let len = s1_s2.len();

    // XXX: div_ceil is not implemented in F*.
    for i in 0..len / 4 {
        sample_four_error_ring_elements::<SIMDUnit, Shake256X4>(eta, seed, 4 * i as u16, s1_s2);
    }

    // Do it another time if needed.
    let remainder = len % 4;
    if remainder != 0 {
        sample_four_error_ring_elements::<SIMDUnit, Shake256X4>(
            eta,
            seed,
            (len - remainder) as u16,
            s1_s2,
        );
    }
}
