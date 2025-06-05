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
    #[ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_G $input"#))
    ]
    fn G(input: &[u8], output: &mut [u8]);

    /// H aka SHA3 256
    #[requires(true)]
    #[ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_H $input"#))
    ]
    fn H(input: &[u8], output: &mut [u8]);

    /// PRF aka SHAKE256
    #[requires(fstar!(r#"v $LEN < pow2 32"#))]
    #[ensures(|result|
        // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
        fstar!(r#"v $LEN < pow2 32 ==> $result == Spec.Utils.v_PRF $LEN $input"#))
    ]
    fn PRF<const LEN: usize>(input: &[u8], out: &mut [u8]);

    /// PRFxN aka N SHAKE256
    #[requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
    #[ensures(|result|
        // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
        fstar!(r#"(v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)) ==>
            $result == Spec.Utils.v_PRFxN $K $LEN $input"#))
    ]
    fn PRFxN(input: &[[u8; 33]], outputs: &mut [u8], out_len: usize);

    /// Create a SHAKE128 state and absorb the input.
    #[requires(true)]
    fn shake128_init_absorb_final(input: &[[u8; 34]]) -> Self;

    /// Squeeze 3 blocks out of the SHAKE128 state.
    #[requires(true)]
    fn shake128_squeeze_first_three_blocks(&mut self, output: &mut [[u8; THREE_BLOCKS]]);

    /// Squeeze 1 block out of the SHAKE128 state.
    #[requires(true)]
    fn shake128_squeeze_next_block(&mut self, output: &mut [[u8; BLOCK_SIZE]]);
}

/// A portable implementation of [`Hash`]
pub(crate) mod portable {
    use super::*;
    use libcrux_sha3::portable::{self, incremental, KeccakState};

    /// The state.
    ///
    /// It's only used for SHAKE128.
    /// All other functions don't actually use any members.
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct PortableHash {
        shake128_state: [KeccakState; 4],
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
    #[inline(always)]
    fn PRF<const LEN: usize>(input: &[u8], out: &mut [u8]) {
        portable::shake256(out, input);
    }

    #[hax_lib::requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_PRFxN $K $LEN $input"#))
    ]
    #[inline(always)]
    fn PRFxN(input: &[[u8; 33]], outputs: &mut [u8], out_len: usize) {
        for i in 0..input.len() {
            portable::shake256(&mut outputs[i * out_len..(i + 1) * out_len], &input[i]);
        }
    }

    #[inline(always)]
    fn shake128_init_absorb_final(input: &[[u8; 34]]) -> PortableHash {
        debug_assert!(input.len() == 2 || input.len() == 3 || input.len() == 4);

        let mut shake128_state = [incremental::shake128_init(); 4];
        for i in 0..input.len() {
            incremental::shake128_absorb_final(&mut shake128_state[i], &input[i]);
        }
        PortableHash { shake128_state }
    }

    #[inline(always)]
    fn shake128_squeeze_first_three_blocks(
        st: &mut PortableHash,
        outputs: &mut [[u8; THREE_BLOCKS]],
    ) {
        debug_assert!(outputs.len() == 2 || outputs.len() == 3 || outputs.len() == 4);

        for i in 0..outputs.len() {
            incremental::shake128_squeeze_first_three_blocks(
                &mut st.shake128_state[i],
                &mut outputs[i],
            );
        }
    }

    #[inline(always)]
    fn shake128_squeeze_next_block(st: &mut PortableHash, outputs: &mut [[u8; BLOCK_SIZE]]) {
        for i in 0..outputs.len() {
            incremental::shake128_squeeze_next_block(&mut st.shake128_state[i], &mut outputs[i]);
        }
    }

    #[hax_lib::attributes]
    impl Hash for PortableHash {
        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_G $input"#))
        ]
        #[inline(always)]
        fn G(input: &[u8], output: &mut [u8]) {
            G(input, output)
        }

        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_H $input"#))
        ]
        #[inline(always)]
        fn H(input: &[u8], output: &mut [u8]) {
            H(input, output)
        }

        #[requires(fstar!(r#"v $LEN < pow2 32"#))]
        #[ensures(|out|
            // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
            fstar!(r#"v $LEN < pow2 32 ==> $out == Spec.Utils.v_PRF $LEN $input"#))
        ]
        #[inline(always)]
        fn PRF<const LEN: usize>(input: &[u8], out: &mut [u8]) {
            PRF::<LEN>(input, out)
        }

        #[requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
        #[ensures(|out|
            fstar!(r#"(v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)) ==>
                $out == Spec.Utils.v_PRFxN $K $LEN $input"#))
        ]
        #[inline(always)]
        fn PRFxN(input: &[[u8; 33]], outputs: &mut [u8], out_len: usize) {
            PRFxN(input, outputs, out_len)
        }

        #[inline(always)]
        fn shake128_init_absorb_final(input: &[[u8; 34]]) -> Self {
            shake128_init_absorb_final(input)
        }

        #[inline(always)]
        fn shake128_squeeze_first_three_blocks(&mut self, output: &mut [[u8; THREE_BLOCKS]]) {
            shake128_squeeze_first_three_blocks(self, output)
        }

        #[inline(always)]
        fn shake128_squeeze_next_block(&mut self, output: &mut [[u8; BLOCK_SIZE]]) {
            shake128_squeeze_next_block(self, output)
        }
    }
}
