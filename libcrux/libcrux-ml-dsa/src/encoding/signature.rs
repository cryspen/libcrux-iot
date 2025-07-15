use crate::{
    constants::COEFFICIENTS_IN_RING_ELEMENT, encoding, polynomial::PolynomialRingElement,
    simd::traits::Operations, VerificationError,
};

#[inline(always)]
pub(crate) fn serialize<SIMDUnit: Operations>(
    commitment_hash: &[u8],
    signer_response: &[PolynomialRingElement<SIMDUnit>],
    hint: &[[i32; COEFFICIENTS_IN_RING_ELEMENT]],
    commitment_hash_size: usize,
    columns_in_a: usize,
    rows_in_a: usize,
    gamma1_exponent: usize,
    gamma1_ring_element_size: usize,
    max_ones_in_hint: usize,
    signature: &mut [u8],
) {
    let mut offset = 0;

    signature[offset..offset + commitment_hash_size].copy_from_slice(commitment_hash);
    offset += commitment_hash_size;

    for i in 0..columns_in_a {
        encoding::gamma1::serialize::<SIMDUnit>(
            &signer_response[i],
            &mut signature[offset..offset + gamma1_ring_element_size],
            gamma1_exponent,
        );
        offset += gamma1_ring_element_size;
    }

    let mut true_hints_seen = 0;

    // Unfortunately the following does not go through hax:
    //
    //     let hint_serialized = &mut signature[offset..];
    //
    // Instead, we have to mutate signature[offset + ..] directly.
    for i in 0..rows_in_a {
        // for (j, hint) in self.hint[i].into_iter().enumerate() {
        for j in 0..hint[i].len() {
            if hint[i][j] == 1 {
                signature[offset + true_hints_seen] = j as u8;
                true_hints_seen += 1;
            }
        }
        signature[offset + max_ones_in_hint + i] = true_hints_seen as u8;
    }

    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

#[inline(always)]
pub(crate) fn deserialize_signer_response_j<SIMDUnit: Operations>(
    gamma1_exponent: usize,
    gamma1_ring_element_size: usize,
    beta: i32,
    signer_response_serialized: &[u8],
    j: usize,
    out_signer_response: &mut PolynomialRingElement<SIMDUnit>,
) -> Result<(), VerificationError> {
    encoding::gamma1::deserialize::<SIMDUnit>(
        gamma1_exponent,
        &signer_response_serialized
            [j * gamma1_ring_element_size..(j + 1) * gamma1_ring_element_size],
        out_signer_response,
    );
    if out_signer_response.infinity_norm_exceeds((2 << gamma1_exponent) - beta) {
        return Err(VerificationError::SignerResponseExceedsBoundError);
    }
    Ok(())
}

#[inline(always)]
pub(crate) fn deserialize_hint(
    rows_in_a: usize,
    max_ones_in_hint: usize,
    hint_serialized: &[u8],
    i: usize,
    out_hint: &mut [i32; COEFFICIENTS_IN_RING_ELEMENT],
    previous_true_hints_seen: &mut usize, // initialize to 0
) -> Result<(), VerificationError> {
    let current_true_hints_seen = hint_serialized[max_ones_in_hint + i] as usize;

    if (current_true_hints_seen < *previous_true_hints_seen)
        || (*previous_true_hints_seen > max_ones_in_hint)
    {
        // the true hints seen should be increasing
        return Err(VerificationError::MalformedHintError);
    }

    let mut j = *previous_true_hints_seen;
    while j < current_true_hints_seen {
        if j > *previous_true_hints_seen && hint_serialized[j] <= hint_serialized[j - 1] {
            // indices of true hints for a specific polynomial should be
            // increasing
            return Err(VerificationError::MalformedHintError);
        }

        out_hint[hint_serialized[j] as usize] = 1;
        j += 1;
    }
    *previous_true_hints_seen = current_true_hints_seen;

    // ensures padding indices are zero
    if i == rows_in_a - 1 {
        hints_check_zero_padding(max_ones_in_hint, *previous_true_hints_seen, hint_serialized)?
    }
    Ok(())
}

#[inline(always)]
pub(crate) fn hints_check_zero_padding(
    max_ones_in_hint: usize,
    previous_true_hints_seen: usize,
    hint_serialized: &[u8],
) -> Result<(), VerificationError> {
    for j in previous_true_hints_seen..max_ones_in_hint {
        if hint_serialized[j] != 0 {
            return Err(VerificationError::MalformedHintError);
        }
    }

    Ok(())
}
