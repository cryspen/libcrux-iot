use crate::{
    arithmetic::shift_left_then_reduce,
    constants::{BITS_IN_LOWER_PART_OF_T, RING_ELEMENT_OF_T1S_SIZE},
    encoding::{signature::deserialize_signer_response_j, t1},
    hash_functions::shake128,
    ntt::{invert_ntt_montgomery, ntt, ntt_multiply_montgomery},
    polynomial::PolynomialRingElement,
    sample::sample_ring_element,
    simd::traits::Operations,
    VerificationError,
};

/// Compute InvertNTT(Â ◦ ŝ₁) + s₂
pub(crate) fn compute_as1_plus_s2<SIMDUnit: Operations>(
    rows_in_a: usize,
    columns_in_a: usize,
    a_as_ntt: &[PolynomialRingElement<SIMDUnit>],
    s1_ntt: &[PolynomialRingElement<SIMDUnit>],
    s1_s2: &[PolynomialRingElement<SIMDUnit>],
    result: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..rows_in_a {
        for j in 0..columns_in_a {
            let mut product = a_as_ntt[i * columns_in_a + j];
            ntt_multiply_montgomery::<SIMDUnit>(&mut product, &s1_ntt[j]);
            PolynomialRingElement::add(&mut result[i], &product);
        }
    }

    for i in 0..result.len() {
        invert_ntt_montgomery::<SIMDUnit>(&mut result[i]);
        PolynomialRingElement::add(&mut result[i], &s1_s2[columns_in_a + i]);
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

/// Compute InvertNTT(Â ◦ ŷ)
#[inline(always)]
pub(crate) fn compute_matrix_x_mask<SIMDUnit: Operations>(
    rows_in_a: usize,
    columns_in_a: usize,
    matrix: &[PolynomialRingElement<SIMDUnit>],
    mask: &[PolynomialRingElement<SIMDUnit>],
    result: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..rows_in_a {
        for j in 0..columns_in_a {
            let mut product = mask[j];
            ntt_multiply_montgomery(&mut product, &matrix[i * columns_in_a + j]);
            PolynomialRingElement::<SIMDUnit>::add(&mut result[i], &product);
        }
        invert_ntt_montgomery(&mut result[i]);
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

#[inline(always)]
pub(crate) fn vector_times_ring_element<SIMDUnit: Operations>(
    vector: &mut [PolynomialRingElement<SIMDUnit>],
    ring_element: &PolynomialRingElement<SIMDUnit>,
) {
    for i in 0..vector.len() {
        ntt_multiply_montgomery(&mut vector[i], ring_element);
        invert_ntt_montgomery(&mut vector[i]);
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

#[inline(always)]
pub(crate) fn add_vectors<SIMDUnit: Operations>(
    dimension: usize,
    lhs: &mut [PolynomialRingElement<SIMDUnit>],
    rhs: &[PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..dimension {
        PolynomialRingElement::<SIMDUnit>::add(&mut lhs[i], &rhs[i]);
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

#[inline(always)]
pub(crate) fn subtract_vectors<SIMDUnit: Operations>(
    dimension: usize,
    lhs: &mut [PolynomialRingElement<SIMDUnit>],
    rhs: &[PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..dimension {
        PolynomialRingElement::<SIMDUnit>::subtract(&mut lhs[i], &rhs[i]);
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

/// Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
#[inline(always)]
pub(crate) fn compute_w_approx_i<SIMDUnit: Operations>(
    columns_in_a: usize,
    gamma1_exponent: usize,
    gamma1_ring_element_size: usize,
    beta: i32,
    seed: &[u8],
    verifier_challenge_as_ntt: &PolynomialRingElement<SIMDUnit>,
    t1_serialized: &[u8],
    signer_response_serialized: &[u8],
    i: usize,
    rand_stack: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
    rand_block: &mut [u8; shake128::BLOCK_SIZE],
    tmp_stack: &mut [i32; 263],
    poly_slot_a: &mut PolynomialRingElement<SIMDUnit>,
    poly_slot_b: &mut PolynomialRingElement<SIMDUnit>,
    poly_slot_c: &mut PolynomialRingElement<SIMDUnit>, // Must be zero
) -> Result<(), VerificationError> {
    for j in 0..columns_in_a {
        // Sample A[i,j] into slot A
        sample_ring_element(
            seed,
            (i as u8, j as u8),
            poly_slot_a,
            rand_stack,
            rand_block,
            tmp_stack,
        );

        // Deserialize signer_response[j] into slot B, then transform to NTT domain
        deserialize_signer_response_j(
            gamma1_exponent,
            gamma1_ring_element_size,
            beta,
            signer_response_serialized,
            j,
            poly_slot_b,
        )?;
        ntt(poly_slot_b);

        ntt_multiply_montgomery(poly_slot_a, poly_slot_b);

        // Accumulate into slot C
        PolynomialRingElement::<SIMDUnit>::add(poly_slot_c, &poly_slot_a);
    }

    // Deserialize t1[i] into slot A
    t1::deserialize::<SIMDUnit>(
        &t1_serialized[i * RING_ELEMENT_OF_T1S_SIZE..(i + 1) * RING_ELEMENT_OF_T1S_SIZE],
        poly_slot_a,
    );
    shift_left_then_reduce::<SIMDUnit, { BITS_IN_LOWER_PART_OF_T as i32 }>(poly_slot_a);
    ntt(poly_slot_a);
    ntt_multiply_montgomery(poly_slot_a, verifier_challenge_as_ntt);
    PolynomialRingElement::<SIMDUnit>::subtract(poly_slot_c, poly_slot_a);
    invert_ntt_montgomery(poly_slot_c);

    // [hax] https://github.com/hacspec/hax/issues/720
    Ok(())
}
