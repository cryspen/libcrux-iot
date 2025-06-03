#![allow(non_snake_case)]
//! This module contains the hash functions needed by ML-KEM
//! Verification Status: Interface-Only, Lax

// TODO: Extract and verify the code, not just the interface, by relating to libcrux-sha3
// Related Issue: https://github.com/cryspen/libcrux/issues/395 for extracting/checking libcrux-sha3
// TODO: We need to manually pull out the code for G, H, PRFxN, etc. in each module to allow
// them to be properly abstracted in F*. We would like hax to do this automatically.
// Related Issue: https://github.com/hacspec/hax/issues/616

/// The SHA3 block size.
pub(crate) const BLOCK_SIZE: usize = 168;

/// The size of 3 SHA3 blocks.
pub(crate) const THREE_BLOCKS: usize = BLOCK_SIZE * 3;

/// A portable hashing abstraction.
pub(crate) mod portable {
    use super::*;
    use libcrux_sha3::portable::{self, incremental, KeccakState};

    /// The state.
    ///
    /// It's only used for SHAKE128.
    /// All other functions don't actually use any members.
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct PortableHash {
        shake128_state: KeccakState,
    }

    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_G $input"#))
    ]
    #[inline(always)]
    fn G(input: &[u8], output: &mut [u8]) {
        portable::sha512(output, input);
    }

    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_H $input"#))
    ]
    #[inline(always)]
    fn H(input: &[u8], output: &mut [u8]) {
        portable::sha256(output, input);
    }

    #[hax_lib::requires(fstar!(r#"v $LEN < pow2 32"#))]
    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_PRF $LEN $input"#))
    ]
    // #[inline(always)]
    fn PRF<const LEN: usize>(input: &[u8], out: &mut [u8]) {
        portable::shake256(out, input);
    }

    #[inline(always)]
    fn shake128_init_absorb_final(input: &[u8; 34]) -> PortableHash {
        let mut shake128_state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut shake128_state, &input[..]);
        PortableHash { shake128_state }
    }

    #[inline(always)]
    fn shake128_squeeze_first_three_blocks(st: &mut PortableHash, output: &mut [u8; THREE_BLOCKS]) {
        incremental::shake128_squeeze_first_three_blocks(&mut st.shake128_state, output);
    }

    #[inline(always)]
    fn shake128_squeeze_next_block(st: &mut PortableHash, output: &mut [u8; BLOCK_SIZE]) {
        incremental::shake128_squeeze_next_block(&mut st.shake128_state, output);
    }

    #[hax_lib::attributes]
    impl PortableHash {
        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_G $input"#))
        ]
        #[inline(always)]
        pub(crate) fn G(input: &[u8], output: &mut [u8]) {
            G(input, output)
        }

        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_H $input"#))
        ]
        #[inline(always)]
        pub(crate) fn H(input: &[u8], output: &mut [u8]) {
            H(input, output)
        }

        #[requires(fstar!(r#"v $LEN < pow2 32"#))]
        #[ensures(|out|
            // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
            fstar!(r#"v $LEN < pow2 32 ==> $out == Spec.Utils.v_PRF $LEN $input"#))
        ]
        #[inline(always)]
        pub(crate) fn PRF<const LEN: usize>(input: &[u8], out: &mut [u8]) {
            PRF::<LEN>(input, out)
        }

        #[inline(always)]
        pub(crate) fn shake128_init_absorb_final(input: &[u8; 34]) -> Self {
            shake128_init_absorb_final(input)
        }

        #[inline(always)]
        pub(crate) fn shake128_squeeze_first_three_blocks(
            &mut self,
            output: &mut [u8; THREE_BLOCKS],
        ) {
            shake128_squeeze_first_three_blocks(self, output)
        }

        #[inline(always)]
        pub(crate) fn shake128_squeeze_next_block(&mut self, output: &mut [u8; BLOCK_SIZE]) {
            shake128_squeeze_next_block(self, output)
        }
    }
}
