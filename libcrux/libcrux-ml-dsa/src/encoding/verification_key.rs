use crate::{
    constants::{RING_ELEMENT_OF_T1S_SIZE, SEED_FOR_A_SIZE},
    encoding::t1,
    helper::cloop,
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[inline(always)]
pub(crate) fn generate_serialized<SIMDUnit: Operations>(
    seed: &[u8],
    t1: &[PolynomialRingElement<SIMDUnit>],
    verification_key_serialized: &mut [u8],
) {
    verification_key_serialized[0..SEED_FOR_A_SIZE].copy_from_slice(seed);

    cloop! {
        for (i, ring_element) in t1.iter().enumerate() {
            let offset = SEED_FOR_A_SIZE + (i * RING_ELEMENT_OF_T1S_SIZE);
            t1::serialize::<SIMDUnit>(
                ring_element,
                &mut verification_key_serialized[offset..offset + RING_ELEMENT_OF_T1S_SIZE],
            );
        }
    }
    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}
