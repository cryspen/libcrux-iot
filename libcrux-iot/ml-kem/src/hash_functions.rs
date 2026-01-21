#![allow(non_snake_case)]
//! This module contains the hash functions needed by ML-KEM
//! Verification Status: Interface-Only, Lax

// TODO: Extract and verify the code, not just the interface, by relating to libcrux-sha3
// Related Issue: https://github.com/cryspen/libcrux/issues/395 for extracting/checking libcrux-sha3
// TODO: We need to manually pull out the code for G, H, PRFxN, etc. in each module to allow
// them to be properly abstracted in F*. We would like hax to do this automatically.
// Related Issue: https://github.com/hacspec/hax/issues/616

use libcrux_secrets::U8;

/// The SHA3 block size.
pub(crate) const BLOCK_SIZE: usize = 168;

/// The size of 3 SHA3 blocks.
pub(crate) const THREE_BLOCKS: usize = BLOCK_SIZE * 3;

/// Abstraction for the hashing, to pick the fastest version depending on the
/// platform features available.
///
/// In libcrux-iot we currently support a portable instantiations of
/// this trait right now, whereas mainline libcrux supports additional
/// SIMD platform.
#[hax_lib::attributes]
pub(crate) trait Hash {
    /// G aka SHA3 512
    #[requires(true)]
    #[requires(output.len() == 64)]
    #[ensures(|_| future(output).len() == output.len())]
    fn G(input: &[U8], output: &mut [U8]);

    /// H aka SHA3 256
    #[requires(true)]
    #[requires(output.len() == 32)]
    #[ensures(|_| future(output).len() == output.len())]
    fn H(input: &[U8], output: &mut [U8]);

    /// PRF aka SHAKE256
    #[requires(LEN <= u32::MAX as usize && out.len() == LEN)]
    #[ensures(|_| future(out).len() == out.len())]
    fn PRF<const LEN: usize>(input: &[U8], out: &mut [U8]);

    /// PRFxN aka N SHAKE256
    #[requires(
        (input.len() == 2 || input.len() == 3 || input.len() == 4) &&
        out_len <= (u32::MAX / 4) as usize &&
        outputs.len() == input.len() * out_len
    )]
    #[ensures(|_| future(outputs).len() == outputs.len())]
    fn PRFxN(input: &[[U8; 33]], outputs: &mut [U8], out_len: usize);

    /// Create a SHAKE128 state and absorb the input.
    // We only use this in sampling the public matrix A from the public seeds as input.
    #[requires(true)]
    fn shake128_init_absorb_final(input: &[[u8; 34]]) -> Self;

    /// Squeeze 3 blocks out of the SHAKE128 state.
    #[requires(true)]
    // We only use this to sample entries of the public matrix A, from the public seeds.
    fn shake128_squeeze_first_three_blocks(&mut self, output: &mut [[u8; THREE_BLOCKS]]);

    /// Squeeze 1 block out of the SHAKE128 state.
    #[requires(true)]
    // We only use this to sample entries of the public matrix A, from the public seeds.
    fn shake128_squeeze_next_block(&mut self, output: &mut [[u8; BLOCK_SIZE]]);
}

/// A portable implementation of [`Hash`]
pub(crate) mod portable {
    use super::*;
    use libcrux_iot_sha3::portable::{self, incremental, KeccakState};
    use libcrux_secrets::Classify as _;
    #[cfg(not(hax))]
    use libcrux_secrets::ClassifyRefMut as _;

    /// The state.
    ///
    /// It's only used for SHAKE128.
    /// All other functions don't actually use any members.
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct PortableHash {
        shake128_state: [KeccakState; 4],
    }

    #[hax_lib::attributes]
    impl Hash for PortableHash {
        #[hax_lib::requires(output.len() == 64)]
        #[hax_lib::ensures(|_| future(output).len() == output.len())]
        #[inline(always)]
        fn G(input: &[U8], output: &mut [U8]) {
            portable::sha512(output, input);
        }

        #[hax_lib::requires(output.len() == 32)]
        #[hax_lib::ensures(|_| future(output).len() == output.len())]
        #[inline(always)]
        fn H(input: &[U8], output: &mut [U8]) {
            portable::sha256(output, input);
        }

        #[hax_lib::requires(LEN <= u32::MAX as usize && out.len() == LEN)]
        #[hax_lib::ensures(|_| future(out).len() == out.len())]
        #[inline(always)]
        fn PRF<const LEN: usize>(input: &[U8], out: &mut [U8]) {
            #[cfg(not(eurydice))]
            debug_assert!(out.len() == LEN);
            portable::shake256(out, input);
        }

        #[hax_lib::requires((input.len() == 2 || input.len() == 3 || input.len() == 4) &&
             out_len <= (u32::MAX / 4) as usize &&
        outputs.len() == input.len() * out_len)]
        #[hax_lib::ensures(|_| future(outputs).len() == outputs.len())]
        #[inline]
        fn PRFxN(input: &[[U8; 33]], outputs: &mut [U8], out_len: usize) {
            for i in 0..input.len() {
                hax_lib::loop_invariant!(|_: usize| outputs.len() == input.len() * out_len);
                portable::shake256(
                    &mut outputs[i * out_len..(i + 1) * out_len],
                    input[i].as_slice(),
                );
            }
        }

        #[inline(always)]
        fn shake128_init_absorb_final(input: &[[u8; 34]]) -> Self {
            #[cfg(not(eurydice))]
            debug_assert!(
                input.len() == 1 || input.len() == 2 || input.len() == 3 || input.len() == 4
            );

            let mut shake128_state = [incremental::shake128_init(); 4];
            for i in 0..input.len() {
                incremental::shake128_absorb_final(&mut shake128_state[i], &input[i].classify());
            }

            PortableHash { shake128_state }
        }

        #[inline(always)]
        // We only use this to sample entries of the public matrix A, from the public seeds.
        fn shake128_squeeze_first_three_blocks(&mut self, output: &mut [[u8; THREE_BLOCKS]]) {
            #[cfg(not(eurydice))]
            debug_assert!(
                output.len() == 1 || output.len() == 2 || output.len() == 3 || output.len() == 4
            );

            for i in 0..output.len() {
                // XXX: We need a separate version for hax, entirely without
                // classification. The reason is that hax does not support for
                // `&mut`-returning functions.
                // (see https://github.com/cryspen/hax/issues/420)
                #[cfg(not(hax))]
                incremental::shake128_squeeze_first_three_blocks(
                    &mut self.shake128_state[i],
                    output[i].as_mut_slice().classify_ref_mut(),
                );
                #[cfg(hax)]
                incremental::shake128_squeeze_first_three_blocks(
                    &mut self.shake128_state[i],
                    &mut output[i],
                );
            }
        }

        #[inline(always)]
        // We only use this to sample entries of the public matrix A, from the public seeds.
        fn shake128_squeeze_next_block(&mut self, output: &mut [[u8; BLOCK_SIZE]]) {
            for i in 0..output.len() {
                // XXX: We need a separate version for hax, entirely without
                // classification. The reason is that hax does not support for
                // `&mut`-returning functions.
                // (see https://github.com/cryspen/hax/issues/420)
                #[cfg(not(hax))]
                incremental::shake128_squeeze_next_block(
                    &mut self.shake128_state[i],
                    output[i].as_mut_slice().classify_ref_mut(),
                );
                #[cfg(hax)]
                incremental::shake128_squeeze_next_block(
                    &mut self.shake128_state[i],
                    &mut output[i],
                );
            }
        }
    }
}
