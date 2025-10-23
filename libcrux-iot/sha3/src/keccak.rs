//! The generic SHA3 implementation that uses portable or platform specific
//! sub-routines.

use libcrux_secrets::{Classify, U8};
#[cfg(feature = "check-secret-independence")]
use libcrux_secrets::{Declassify, U32};

use crate::{lane::Lane2U32, state::KeccakState};

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
#[cfg_attr(hax, hax_lib::opaque)]
pub(crate) struct KeccakXofState<const RATE: usize> {
    inner: KeccakState,

    // Buffer inputs on absorb.
    buf: [U8; RATE],

    // Buffered length.
    buf_len: usize,

    // Needs sponge.
    sponge: bool,
}

impl<const RATE: usize> KeccakXofState<RATE> {
    /// An all zero block
    pub(crate) fn zero_block() -> [U8; RATE] {
        [0; RATE].classify()
    }

    /// Generate a new keccak xof state.
    pub(crate) fn new() -> Self {
        Self {
            inner: KeccakState::new(),
            buf: Self::zero_block(),
            buf_len: 0,
            sponge: false,
        }
    }

    /// Absorb
    ///
    /// This function takes any number of bytes to absorb and buffers if it's not enough.
    /// The function assumes that all input slices in `blocks` have the same length.
    ///
    /// Only a multiple of `RATE` blocks are absorbed.
    /// For the remaining bytes [`absorb_final`] needs to be called.
    ///
    /// This works best with relatively small `inputs`.
    #[inline(always)]
    pub(crate) fn absorb(&mut self, inputs: &[U8]) {
        let input_remainder_len = self.absorb_full(inputs);

        // ... buffer the rest if there's not enough input (left).
        if input_remainder_len > 0 {
            debug_assert!(
                self.buf_len == 0  // We consumed everything (or it was empty all along).
                 || self.buf_len + input_remainder_len <= RATE
            );

            let input_len = inputs.len();
            self.buf[self.buf_len..self.buf_len + input_remainder_len]
                .copy_from_slice(&inputs[input_len - input_remainder_len..]);
            self.buf_len += input_remainder_len;
        }
    }

    fn absorb_full(&mut self, inputs: &[U8]) -> usize {
        debug_assert!(self.buf_len < RATE);
        // Check if there are buffered bytes to absorb first and consume them.
        let input_consumed = self.fill_buffer(inputs);

        if input_consumed > 0 {
            self.inner.load_block::<RATE>(&self.buf, 0);
            keccakf1600(&mut self.inner);

            // "empty" the local buffer
            self.buf_len = 0;
        }

        // We only need to consume the rest of the input.
        let input_to_consume = inputs.len() - input_consumed;

        // Consume the (rest of the) input ...
        let num_blocks = input_to_consume / RATE;
        let remainder = input_to_consume % RATE;
        for i in 0..num_blocks {
            // We only get in here if `input_len / RATE > 0`.
            self.inner
                .load_block::<RATE>(inputs, input_consumed + i * RATE);
            keccakf1600(&mut self.inner);
        }

        remainder
    }

    /// Consume the internal buffer and the required amount of the input to pad to
    /// `RATE`.
    ///
    /// Returns the `consumed` bytes from `inputs` if there's enough buffered
    /// content to consume, and `0` otherwise.
    /// If `consumed > 0` is returned, `self.buf` contains a full block to be
    /// loaded.
    fn fill_buffer(&mut self, inputs: &[U8]) -> usize {
        let input_len = inputs.len();
        let mut consumed = 0;
        if self.buf_len > 0 {
            // There's something buffered internally to consume.
            if self.buf_len + input_len >= RATE {
                // We have enough data when combining the internal buffer and
                // the input.
                consumed = RATE - self.buf_len;
                self.buf[self.buf_len..].copy_from_slice(&inputs[..consumed]);
                self.buf_len += consumed;
            }
        }
        consumed
    }

    /// Absorb a final block.
    ///
    /// The `inputs` block may be empty. Everything in the `inputs` block beyond
    /// `RATE` bytes is ignored.
    #[inline(always)]
    pub(crate) fn absorb_final<const DELIMITER: u8>(&mut self, inputs: &[U8]) {
        let input_remainder_len = self.absorb_full(inputs);

        // Consume the remaining bytes.
        // This may be in the local buffer or in the input.
        let input_len = inputs.len();
        let mut blocks = [0u8; 200].classify();
        if self.buf_len > 0 {
            blocks[0..self.buf_len].copy_from_slice(&self.buf[0..self.buf_len]);
        }
        if input_remainder_len > 0 {
            blocks[self.buf_len..self.buf_len + input_remainder_len]
                .copy_from_slice(&inputs[input_len - input_remainder_len..]);
        }
        blocks[self.buf_len + input_remainder_len] = DELIMITER.classify();
        blocks[RATE - 1] |= 0x80;

        self.inner.load_block_full::<RATE>(&blocks, 0);
        keccakf1600(&mut self.inner);
    }

    /// Squeeze `N` x `LEN` bytes.
    #[inline(always)]
    pub(crate) fn squeeze(&mut self, out: &mut [U8]) {
        if self.sponge {
            // If we called `squeeze` before, call f1600 first.
            // We do it this way around so that we don't call f1600 at the end
            // when we don't need it.
            keccakf1600(&mut self.inner);
        }

        // How many blocks do we need to squeeze out?
        let out_len = out.len();
        let blocks = out_len / RATE;
        let last = out_len - (out_len % RATE);

        // Squeeze out one to start with.
        // XXX: Eurydice does not extract `core::cmp::min`, so we do
        // this instead. (cf. https://github.com/AeneasVerif/eurydice/issues/49)
        let mid = if RATE >= out_len { out_len } else { RATE };
        let (out0, mut out_rest) = Lane2U32::split_at_mut_n(out, mid);
        self.inner.store::<RATE>(out0);

        // If we got asked for more than one block, squeeze out more.
        for _ in 1..blocks {
            // Here we know that we always have full blocks to write out.
            let (out0, tmp) = Lane2U32::split_at_mut_n(out_rest, RATE);
            keccakf1600(&mut self.inner);
            self.inner.store::<RATE>(out0);
            out_rest = tmp;
        }

        if last < out_len {
            // Squeeze out the last partial block
            keccakf1600(&mut self.inner);
            self.inner.store::<RATE>(out_rest);
        }

        self.sponge = true;
    }
}

//// From here, everything is generic

const RC_INTERLEAVED_0: [u32; 255] = [
    0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000,
    0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001,
    0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000001,
    0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000,
    0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000000,
    0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
    0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001,
    0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
];

const RC_INTERLEAVED_1: [u32; 255] = [
    0x00000000, 0x00000089, 0x8000008b, 0x80008080, 0x0000008b, 0x00008000, 0x80008088, 0x80000082,
    0x0000000b, 0x0000000a, 0x00008082, 0x00008003, 0x0000808b, 0x8000000b, 0x8000008a, 0x80000081,
    0x80000081, 0x80000008, 0x00000083, 0x80008003, 0x80008088, 0x80000088, 0x00008000, 0x80008082,
    0x80008089, 0x80008083, 0x80000001, 0x80008002, 0x80000089, 0x00000082, 0x80000008, 0x00000089,
    0x80000008, 0x00000000, 0x00000083, 0x80008080, 0x00000008, 0x80000080, 0x80008080, 0x00000002,
    0x8000808b, 0x00000008, 0x80000009, 0x0000800b, 0x80008082, 0x80008000, 0x00008008, 0x00008081,
    0x80008089, 0x80008089, 0x8000800a, 0x0000008a, 0x00000082, 0x80000002, 0x00008082, 0x00008080,
    0x8000000b, 0x80000003, 0x0000000a, 0x00008001, 0x80000083, 0x00008083, 0x0000008b, 0x0000800a,
    0x80000083, 0x0000800a, 0x80000000, 0x8000008a, 0x80000008, 0x0000000a, 0x00008088, 0x00000008,
    0x80000003, 0x00000000, 0x0000000a, 0x0000800b, 0x80008088, 0x8000000b, 0x80000080, 0x8000808a,
    0x00008009, 0x00000003, 0x80000003, 0x00000089, 0x80000081, 0x8000008b, 0x80008003, 0x8000800b,
    0x00008008, 0x00008008, 0x00008002, 0x00000009, 0x80008081, 0x0000808a, 0x8000800a, 0x00000080,
    0x00008089, 0x0000808a, 0x80008089, 0x80008000, 0x00008081, 0x8000800a, 0x00000009, 0x80008002,
    0x8000000a, 0x80008002, 0x80000000, 0x80000009, 0x00008088, 0x00000002, 0x80008008, 0x80008088,
    0x80000001, 0x8000808b, 0x00000002, 0x80008002, 0x80000083, 0x00008089, 0x00008080, 0x80000082,
    0x00000088, 0x8000808a, 0x0000808a, 0x80008083, 0x8000000b, 0x80000009, 0x00008001, 0x80000089,
    0x00000088, 0x80008003, 0x80008001, 0x00000003, 0x80000080, 0x80008009, 0x80000089, 0x0000000b,
    0x00000083, 0x80008009, 0x80000083, 0x00008000, 0x8000800b, 0x00008002, 0x00000003, 0x8000008a,
    0x80000002, 0x00008001, 0x80000000, 0x80000003, 0x00000083, 0x8000808a, 0x00008003, 0x00008008,
    0x0000808b, 0x80000082, 0x00000001, 0x00008001, 0x8000000a, 0x80008008, 0x8000800b, 0x00008081,
    0x80008083, 0x80000082, 0x00000082, 0x80000081, 0x80000002, 0x00008088, 0x0000008b, 0x00008083,
    0x00000008, 0x8000008a, 0x8000008b, 0x8000808a, 0x00008080, 0x80000088, 0x00008083, 0x00000002,
    0x80008081, 0x00008003, 0x00008081, 0x80008000, 0x00008002, 0x0000008a, 0x00000001, 0x00008082,
    0x0000808a, 0x80008000, 0x0000808b, 0x80000001, 0x80008081, 0x00008009, 0x0000008a, 0x00000088,
    0x80008009, 0x8000000a, 0x8000808b, 0x0000008b, 0x00008089, 0x00008003, 0x00008002, 0x00000080,
    0x0000800a, 0x8000000a, 0x80008081, 0x00008080, 0x80000001, 0x80008008, 0x80008082, 0x8000800a,
    0x00000003, 0x80000009, 0x00008082, 0x00008009, 0x00000080, 0x00008083, 0x00000081, 0x00000001,
    0x0000800b, 0x80008001, 0x00000080, 0x00008000, 0x80008001, 0x00000009, 0x8000808b, 0x00000081,
    0x00000082, 0x8000008b, 0x80008009, 0x80000000, 0x80000080, 0x80008003, 0x80008082, 0x80008083,
    0x80000088, 0x00008089, 0x00008009, 0x00000009, 0x80008008, 0x80008001, 0x0000008a, 0x0000000b,
    0x00000089, 0x80000002, 0x0000800b, 0x8000800b, 0x0000808b, 0x80000088, 0x0000800a, 0x80000089,
    0x00000001, 0x00008088, 0x00000081, 0x00000088, 0x80008080, 0x00000081, 0x0000000b,
];

// Insert Generated code here, e.g.
// ```
// :r !python libcrux/libcrux-sha3/codegen.py
// ```
#[inline(always)]
pub(crate) fn keccakf1600_round0<const BASE_ROUND: usize>(s: &mut KeccakState) {
    {
        let ax_0 = s.get_with_zeta(0, 0, 0);
        let ax_1 = s.get_with_zeta(1, 0, 0);
        let ax_2 = s.get_with_zeta(2, 0, 0);
        let ax_3 = s.get_with_zeta(3, 0, 0);
        let ax_4 = s.get_with_zeta(4, 0, 0);
        s.c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 0, 1);
        let ax_1 = s.get_with_zeta(1, 0, 1);
        let ax_2 = s.get_with_zeta(2, 0, 1);
        let ax_3 = s.get_with_zeta(3, 0, 1);
        let ax_4 = s.get_with_zeta(4, 0, 1);
        s.c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 1, 0);
        let ax_1 = s.get_with_zeta(1, 1, 0);
        let ax_2 = s.get_with_zeta(2, 1, 0);
        let ax_3 = s.get_with_zeta(3, 1, 0);
        let ax_4 = s.get_with_zeta(4, 1, 0);
        s.c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 1, 1);
        let ax_1 = s.get_with_zeta(1, 1, 1);
        let ax_2 = s.get_with_zeta(2, 1, 1);
        let ax_3 = s.get_with_zeta(3, 1, 1);
        let ax_4 = s.get_with_zeta(4, 1, 1);
        s.c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 2, 0);
        let ax_1 = s.get_with_zeta(1, 2, 0);
        let ax_2 = s.get_with_zeta(2, 2, 0);
        let ax_3 = s.get_with_zeta(3, 2, 0);
        let ax_4 = s.get_with_zeta(4, 2, 0);
        s.c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 2, 1);
        let ax_1 = s.get_with_zeta(1, 2, 1);
        let ax_2 = s.get_with_zeta(2, 2, 1);
        let ax_3 = s.get_with_zeta(3, 2, 1);
        let ax_4 = s.get_with_zeta(4, 2, 1);
        s.c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 3, 0);
        let ax_1 = s.get_with_zeta(1, 3, 0);
        let ax_2 = s.get_with_zeta(2, 3, 0);
        let ax_3 = s.get_with_zeta(3, 3, 0);
        let ax_4 = s.get_with_zeta(4, 3, 0);
        s.c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 3, 1);
        let ax_1 = s.get_with_zeta(1, 3, 1);
        let ax_2 = s.get_with_zeta(2, 3, 1);
        let ax_3 = s.get_with_zeta(3, 3, 1);
        let ax_4 = s.get_with_zeta(4, 3, 1);
        s.c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 4, 0);
        let ax_1 = s.get_with_zeta(1, 4, 0);
        let ax_2 = s.get_with_zeta(2, 4, 0);
        let ax_3 = s.get_with_zeta(3, 4, 0);
        let ax_4 = s.get_with_zeta(4, 4, 0);
        s.c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 4, 1);
        let ax_1 = s.get_with_zeta(1, 4, 1);
        let ax_2 = s.get_with_zeta(2, 4, 1);
        let ax_3 = s.get_with_zeta(3, 4, 1);
        let ax_4 = s.get_with_zeta(4, 4, 1);
        s.c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let c_x4_zeta0 = s.c[4][0];
        let c_x1_zeta1 = s.c[1][1];
        let c_x3_zeta0 = s.c[3][0];
        let c_x0_zeta1 = s.c[0][1];
        let c_x2_zeta0 = s.c[2][0];
        let c_x4_zeta1 = s.c[4][1];
        let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
        s.d[0][0] = d_x0_zeta0;
        let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
        s.d[2][1] = d_x2_zeta1;
        let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
        s.d[4][0] = d_x4_zeta0;
        let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
        s.d[1][1] = d_x1_zeta1;
        let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
        s.d[3][0] = d_x3_zeta0;
        let c_x1_zeta0 = s.c[1][0];
        let c_x3_zeta1 = s.c[3][1];
        let c_x2_zeta1 = s.c[2][1];
        let c_x0_zeta0 = s.c[0][0];
        let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
        s.d[0][1] = d_x0_zeta1;
        let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
        s.d[2][0] = d_x2_zeta0;
        let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
        s.d[4][1] = d_x4_zeta1;
        let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
        s.d[1][0] = d_x1_zeta0;
        let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
        s.d[3][1] = d_x3_zeta1;
    }
    #[cfg(not(feature = "full-unroll"))]
    let i = s.i;
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(1, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(2, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(3, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(4, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(22),
                (a3 ^ d3).rotate_left(11),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0;
        #[cfg(feature = "full-unroll")]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 0];
        };
        #[cfg(not(feature = "full-unroll"))]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[i];
        };
        s.set_with_zeta(0, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(1, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(2, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(3, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(4, 4, 0, ax4);
    }
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(1, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(2, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(3, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(4, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(21),
                (a3 ^ d3).rotate_left(10),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0;
        #[cfg(feature = "full-unroll")]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 0];
        };
        #[cfg(not(feature = "full-unroll"))]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[i];
            s.i = i + 1;
        };
        s.set_with_zeta(0, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(1, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(2, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(3, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(4, 4, 1, ax4);
    }
    {
        let (bx2, bx3) = {
            let a0 = s.get_with_zeta(2, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(3, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(4, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(0, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(1, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(14),
                (a4 ^ d4).rotate_left(10),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(2, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(3, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(4, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(0, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(1, 4, 0, ax4);
    }
    {
        let (bx2, bx3) = {
            let a0 = s.get_with_zeta(2, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(3, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(4, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(0, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(1, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(30),
                (a3 ^ d3).rotate_left(14),
                (a4 ^ d4).rotate_left(10),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(2, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(3, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(4, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(0, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(1, 4, 1, ax4);
    }
    {
        let (bx4, bx0) = {
            let a0 = s.get_with_zeta(4, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(0, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(1, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(2, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(3, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(3),
                (a3 ^ d3).rotate_left(13),
                (a4 ^ d4).rotate_left(4),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(4, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(0, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(1, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(2, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(3, 4, 0, ax4);
    }
    {
        let (bx4, bx0) = {
            let a0 = s.get_with_zeta(4, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(0, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(1, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(2, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(3, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(3),
                (a3 ^ d3).rotate_left(12),
                (a4 ^ d4).rotate_left(4),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(4, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(0, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(1, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(2, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(3, 4, 1, ax4);
    }
    {
        let (bx1, bx2) = {
            let a0 = s.get_with_zeta(1, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(2, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(4, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(0, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(8),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(14),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(1, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(2, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(3, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(4, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(0, 4, 1, ax4);
    }
    {
        let (bx1, bx2) = {
            let a0 = s.get_with_zeta(1, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(2, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(4, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(0, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(7),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(13),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(1, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(2, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(3, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(4, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(0, 4, 0, ax4);
    }
    {
        let (bx3, bx4) = {
            let a0 = s.get_with_zeta(3, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(4, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(0, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(1, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(2, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(20),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(3, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(4, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(0, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(1, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(2, 4, 1, ax4);
    }
    {
        let (bx3, bx4) = {
            let a0 = s.get_with_zeta(3, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(4, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(0, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(1, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(2, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(27),
                (a4 ^ d4).rotate_left(19),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(3, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(4, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(0, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(1, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(2, 4, 0, ax4);
    }
}

#[inline(always)]
pub(crate) fn keccakf1600_round1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    {
        let ax_0 = s.get_with_zeta(0, 0, 0);
        let ax_2 = s.get_with_zeta(2, 0, 1);
        let ax_4 = s.get_with_zeta(4, 0, 0);
        let ax_1 = s.get_with_zeta(1, 0, 0);
        let ax_3 = s.get_with_zeta(3, 0, 1);
        s.c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 0, 1);
        let ax_2 = s.get_with_zeta(2, 0, 0);
        let ax_4 = s.get_with_zeta(4, 0, 1);
        let ax_1 = s.get_with_zeta(1, 0, 1);
        let ax_3 = s.get_with_zeta(3, 0, 0);
        s.c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 1, 0);
        let ax_3 = s.get_with_zeta(3, 1, 1);
        let ax_0 = s.get_with_zeta(0, 1, 1);
        let ax_2 = s.get_with_zeta(2, 1, 0);
        let ax_4 = s.get_with_zeta(4, 1, 0);
        s.c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 1, 1);
        let ax_3 = s.get_with_zeta(3, 1, 0);
        let ax_0 = s.get_with_zeta(0, 1, 0);
        let ax_2 = s.get_with_zeta(2, 1, 1);
        let ax_4 = s.get_with_zeta(4, 1, 1);
        s.c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 2, 1);
        let ax_4 = s.get_with_zeta(4, 2, 1);
        let ax_1 = s.get_with_zeta(1, 2, 0);
        let ax_3 = s.get_with_zeta(3, 2, 1);
        let ax_0 = s.get_with_zeta(0, 2, 0);
        s.c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 2, 0);
        let ax_4 = s.get_with_zeta(4, 2, 0);
        let ax_1 = s.get_with_zeta(1, 2, 1);
        let ax_3 = s.get_with_zeta(3, 2, 0);
        let ax_0 = s.get_with_zeta(0, 2, 1);
        s.c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 3, 1);
        let ax_0 = s.get_with_zeta(0, 3, 0);
        let ax_2 = s.get_with_zeta(2, 3, 1);
        let ax_4 = s.get_with_zeta(4, 3, 0);
        let ax_1 = s.get_with_zeta(1, 3, 1);
        s.c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 3, 0);
        let ax_0 = s.get_with_zeta(0, 3, 1);
        let ax_2 = s.get_with_zeta(2, 3, 0);
        let ax_4 = s.get_with_zeta(4, 3, 1);
        let ax_1 = s.get_with_zeta(1, 3, 0);
        s.c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 4, 0);
        let ax_1 = s.get_with_zeta(1, 4, 0);
        let ax_3 = s.get_with_zeta(3, 4, 0);
        let ax_0 = s.get_with_zeta(0, 4, 1);
        let ax_2 = s.get_with_zeta(2, 4, 1);
        s.c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 4, 1);
        let ax_1 = s.get_with_zeta(1, 4, 1);
        let ax_3 = s.get_with_zeta(3, 4, 1);
        let ax_0 = s.get_with_zeta(0, 4, 0);
        let ax_2 = s.get_with_zeta(2, 4, 0);
        s.c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let c_x4_zeta0 = s.c[4][0];
        let c_x1_zeta1 = s.c[1][1];
        let c_x3_zeta0 = s.c[3][0];
        let c_x0_zeta1 = s.c[0][1];
        let c_x2_zeta0 = s.c[2][0];
        let c_x4_zeta1 = s.c[4][1];
        let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
        s.d[0][0] = d_x0_zeta0;
        let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
        s.d[2][1] = d_x2_zeta1;
        let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
        s.d[4][0] = d_x4_zeta0;
        let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
        s.d[1][1] = d_x1_zeta1;
        let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
        s.d[3][0] = d_x3_zeta0;
        let c_x1_zeta0 = s.c[1][0];
        let c_x3_zeta1 = s.c[3][1];
        let c_x2_zeta1 = s.c[2][1];
        let c_x0_zeta0 = s.c[0][0];
        let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
        s.d[0][1] = d_x0_zeta1;
        let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
        s.d[2][0] = d_x2_zeta0;
        let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
        s.d[4][1] = d_x4_zeta1;
        let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
        s.d[1][0] = d_x1_zeta0;
        let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
        s.d[3][1] = d_x3_zeta1;
    }
    #[cfg(not(feature = "full-unroll"))]
    let i = s.i;
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(3, 1, 1);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(1, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(4, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(2, 4, 1);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(22),
                (a3 ^ d3).rotate_left(11),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0;
        #[cfg(feature = "full-unroll")]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 1];
        };
        #[cfg(not(feature = "full-unroll"))]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[i];
        };
        s.set_with_zeta(0, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(3, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(1, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(4, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(2, 4, 1, ax4);
    }
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(3, 1, 0);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(1, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(4, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(2, 4, 0);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(21),
                (a3 ^ d3).rotate_left(10),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0;
        #[cfg(feature = "full-unroll")]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 1];
        };
        #[cfg(not(feature = "full-unroll"))]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[i];
            s.i = i + 1;
        };
        s.set_with_zeta(0, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(3, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(1, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(4, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(2, 4, 0, ax4);
    }
    {
        let (bx2, bx3) = {
            let a0 = s.get_with_zeta(4, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(2, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(0, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(3, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(1, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(14),
                (a4 ^ d4).rotate_left(10),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(4, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(2, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(0, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(3, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(1, 4, 0, ax4);
    }
    {
        let (bx2, bx3) = {
            let a0 = s.get_with_zeta(4, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(2, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(0, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(3, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(1, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(30),
                (a3 ^ d3).rotate_left(14),
                (a4 ^ d4).rotate_left(10),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(4, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(2, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(0, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(3, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(1, 4, 1, ax4);
    }
    {
        let (bx4, bx0) = {
            let a0 = s.get_with_zeta(3, 0, 1);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(1, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(4, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(2, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(0, 4, 1);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(3),
                (a3 ^ d3).rotate_left(13),
                (a4 ^ d4).rotate_left(4),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(3, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(1, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(4, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(2, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(0, 4, 1, ax4);
    }
    {
        let (bx4, bx0) = {
            let a0 = s.get_with_zeta(3, 0, 0);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(1, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(4, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(2, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(0, 4, 0);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(3),
                (a3 ^ d3).rotate_left(12),
                (a4 ^ d4).rotate_left(4),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(3, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(1, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(4, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(2, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(0, 4, 0, ax4);
    }
    {
        let (bx1, bx2) = {
            let a0 = s.get_with_zeta(2, 0, 1);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(0, 1, 1);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(1, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(4, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(8),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(14),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(2, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(0, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(3, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(1, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(4, 4, 1, ax4);
    }
    {
        let (bx1, bx2) = {
            let a0 = s.get_with_zeta(2, 0, 0);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(0, 1, 0);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(1, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(4, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(7),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(13),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(2, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(0, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(3, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(1, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(4, 4, 0, ax4);
    }
    {
        let (bx3, bx4) = {
            let a0 = s.get_with_zeta(1, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(4, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(2, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(0, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(3, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(20),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(1, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(4, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(2, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(0, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(3, 4, 1, ax4);
    }
    {
        let (bx3, bx4) = {
            let a0 = s.get_with_zeta(1, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(4, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(2, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(0, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(3, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(27),
                (a4 ^ d4).rotate_left(19),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(1, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(4, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(2, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(0, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(3, 4, 0, ax4);
    }
}

#[inline(always)]
pub(crate) fn keccakf1600_round2<const BASE_ROUND: usize>(s: &mut KeccakState) {
    {
        let ax_0 = s.get_with_zeta(0, 0, 0);
        let ax_4 = s.get_with_zeta(4, 0, 1);
        let ax_3 = s.get_with_zeta(3, 0, 1);
        let ax_2 = s.get_with_zeta(2, 0, 1);
        let ax_1 = s.get_with_zeta(1, 0, 1);
        s.c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 0, 1);
        let ax_4 = s.get_with_zeta(4, 0, 0);
        let ax_3 = s.get_with_zeta(3, 0, 0);
        let ax_2 = s.get_with_zeta(2, 0, 0);
        let ax_1 = s.get_with_zeta(1, 0, 0);
        s.c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 1, 1);
        let ax_2 = s.get_with_zeta(2, 1, 1);
        let ax_1 = s.get_with_zeta(1, 1, 1);
        let ax_0 = s.get_with_zeta(0, 1, 1);
        let ax_4 = s.get_with_zeta(4, 1, 0);
        s.c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 1, 0);
        let ax_2 = s.get_with_zeta(2, 1, 0);
        let ax_1 = s.get_with_zeta(1, 1, 0);
        let ax_0 = s.get_with_zeta(0, 1, 0);
        let ax_4 = s.get_with_zeta(4, 1, 1);
        s.c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 2, 1);
        let ax_0 = s.get_with_zeta(0, 2, 1);
        let ax_4 = s.get_with_zeta(4, 2, 1);
        let ax_3 = s.get_with_zeta(3, 2, 0);
        let ax_2 = s.get_with_zeta(2, 2, 1);
        s.c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 2, 0);
        let ax_0 = s.get_with_zeta(0, 2, 0);
        let ax_4 = s.get_with_zeta(4, 2, 0);
        let ax_3 = s.get_with_zeta(3, 2, 1);
        let ax_2 = s.get_with_zeta(2, 2, 0);
        s.c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 3, 1);
        let ax_3 = s.get_with_zeta(3, 3, 1);
        let ax_2 = s.get_with_zeta(2, 3, 0);
        let ax_1 = s.get_with_zeta(1, 3, 1);
        let ax_0 = s.get_with_zeta(0, 3, 1);
        s.c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 3, 0);
        let ax_3 = s.get_with_zeta(3, 3, 0);
        let ax_2 = s.get_with_zeta(2, 3, 1);
        let ax_1 = s.get_with_zeta(1, 3, 0);
        let ax_0 = s.get_with_zeta(0, 3, 0);
        s.c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 4, 1);
        let ax_1 = s.get_with_zeta(1, 4, 0);
        let ax_0 = s.get_with_zeta(0, 4, 1);
        let ax_4 = s.get_with_zeta(4, 4, 1);
        let ax_3 = s.get_with_zeta(3, 4, 1);
        s.c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 4, 0);
        let ax_1 = s.get_with_zeta(1, 4, 1);
        let ax_0 = s.get_with_zeta(0, 4, 0);
        let ax_4 = s.get_with_zeta(4, 4, 0);
        let ax_3 = s.get_with_zeta(3, 4, 0);
        s.c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let c_x4_zeta0 = s.c[4][0];
        let c_x1_zeta1 = s.c[1][1];
        let c_x3_zeta0 = s.c[3][0];
        let c_x0_zeta1 = s.c[0][1];
        let c_x2_zeta0 = s.c[2][0];
        let c_x4_zeta1 = s.c[4][1];
        let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
        s.d[0][0] = d_x0_zeta0;
        let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
        s.d[2][1] = d_x2_zeta1;
        let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
        s.d[4][0] = d_x4_zeta0;
        let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
        s.d[1][1] = d_x1_zeta1;
        let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
        s.d[3][0] = d_x3_zeta0;
        let c_x1_zeta0 = s.c[1][0];
        let c_x3_zeta1 = s.c[3][1];
        let c_x2_zeta1 = s.c[2][1];
        let c_x0_zeta0 = s.c[0][0];
        let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
        s.d[0][1] = d_x0_zeta1;
        let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
        s.d[2][0] = d_x2_zeta0;
        let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
        s.d[4][1] = d_x4_zeta1;
        let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
        s.d[1][0] = d_x1_zeta0;
        let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
        s.d[3][1] = d_x3_zeta1;
    }
    #[cfg(not(feature = "full-unroll"))]
    let i = s.i;
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(2, 1, 1);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(4, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(1, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(3, 4, 1);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(22),
                (a3 ^ d3).rotate_left(11),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0;
        #[cfg(feature = "full-unroll")]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 2];
        };
        #[cfg(not(feature = "full-unroll"))]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[i];
        };
        s.set_with_zeta(0, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(2, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(4, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(1, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(3, 4, 1, ax4);
    }
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(2, 1, 0);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(4, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(1, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(3, 4, 0);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(21),
                (a3 ^ d3).rotate_left(10),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0;
        #[cfg(feature = "full-unroll")]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 2];
        };
        #[cfg(not(feature = "full-unroll"))]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[i];
            s.i = i + 1;
        };
        s.set_with_zeta(0, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(2, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(4, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(1, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(3, 4, 0, ax4);
    }
    {
        let (bx2, bx3) = {
            let a0 = s.get_with_zeta(3, 0, 0);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(0, 1, 0);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(2, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(4, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(1, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(14),
                (a4 ^ d4).rotate_left(10),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(3, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(0, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(2, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(4, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(1, 4, 0, ax4);
    }
    {
        let (bx2, bx3) = {
            let a0 = s.get_with_zeta(3, 0, 1);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(0, 1, 1);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(2, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(4, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(1, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(30),
                (a3 ^ d3).rotate_left(14),
                (a4 ^ d4).rotate_left(10),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(3, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(0, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(2, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(4, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(1, 4, 1, ax4);
    }
    {
        let (bx4, bx0) = {
            let a0 = s.get_with_zeta(1, 0, 1);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(3, 1, 0);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(0, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(2, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(4, 4, 1);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(3),
                (a3 ^ d3).rotate_left(13),
                (a4 ^ d4).rotate_left(4),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(1, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(3, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(0, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(2, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(4, 4, 1, ax4);
    }
    {
        let (bx4, bx0) = {
            let a0 = s.get_with_zeta(1, 0, 0);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(3, 1, 1);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(0, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(2, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(4, 4, 0);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(3),
                (a3 ^ d3).rotate_left(12),
                (a4 ^ d4).rotate_left(4),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(1, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(3, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(0, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(2, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(4, 4, 0, ax4);
    }
    {
        let (bx1, bx2) = {
            let a0 = s.get_with_zeta(4, 0, 1);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(1, 1, 1);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(0, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(2, 4, 0);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(8),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(14),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(4, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(1, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(3, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(0, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(2, 4, 0, ax4);
    }
    {
        let (bx1, bx2) = {
            let a0 = s.get_with_zeta(4, 0, 0);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(1, 1, 0);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(0, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(2, 4, 1);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(7),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(13),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(4, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(1, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(3, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(0, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(2, 4, 1, ax4);
    }
    {
        let (bx3, bx4) = {
            let a0 = s.get_with_zeta(2, 0, 0);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(4, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(1, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(3, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(0, 4, 0);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(20),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(2, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(4, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(1, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(3, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(0, 4, 0, ax4);
    }
    {
        let (bx3, bx4) = {
            let a0 = s.get_with_zeta(2, 0, 1);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(4, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(1, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(3, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(0, 4, 1);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(27),
                (a4 ^ d4).rotate_left(19),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(2, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(4, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(1, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(3, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(0, 4, 1, ax4);
    }
}

#[inline(always)]
pub(crate) fn keccakf1600_round3<const BASE_ROUND: usize>(s: &mut KeccakState) {
    {
        let ax_0 = s.get_with_zeta(0, 0, 0);
        let ax_3 = s.get_with_zeta(3, 0, 0);
        let ax_1 = s.get_with_zeta(1, 0, 1);
        let ax_4 = s.get_with_zeta(4, 0, 1);
        let ax_2 = s.get_with_zeta(2, 0, 0);
        s.c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 0, 1);
        let ax_3 = s.get_with_zeta(3, 0, 1);
        let ax_1 = s.get_with_zeta(1, 0, 0);
        let ax_4 = s.get_with_zeta(4, 0, 0);
        let ax_2 = s.get_with_zeta(2, 0, 1);
        s.c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 1, 1);
        let ax_0 = s.get_with_zeta(0, 1, 0);
        let ax_3 = s.get_with_zeta(3, 1, 0);
        let ax_1 = s.get_with_zeta(1, 1, 1);
        let ax_4 = s.get_with_zeta(4, 1, 0);
        s.c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 1, 0);
        let ax_0 = s.get_with_zeta(0, 1, 1);
        let ax_3 = s.get_with_zeta(3, 1, 1);
        let ax_1 = s.get_with_zeta(1, 1, 0);
        let ax_4 = s.get_with_zeta(4, 1, 1);
        s.c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 2, 0);
        let ax_2 = s.get_with_zeta(2, 2, 0);
        let ax_0 = s.get_with_zeta(0, 2, 1);
        let ax_3 = s.get_with_zeta(3, 2, 1);
        let ax_1 = s.get_with_zeta(1, 2, 1);
        s.c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 2, 1);
        let ax_2 = s.get_with_zeta(2, 2, 1);
        let ax_0 = s.get_with_zeta(0, 2, 0);
        let ax_3 = s.get_with_zeta(3, 2, 0);
        let ax_1 = s.get_with_zeta(1, 2, 0);
        s.c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 3, 0);
        let ax_4 = s.get_with_zeta(4, 3, 1);
        let ax_2 = s.get_with_zeta(2, 3, 1);
        let ax_0 = s.get_with_zeta(0, 3, 1);
        let ax_3 = s.get_with_zeta(3, 3, 0);
        s.c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 3, 1);
        let ax_4 = s.get_with_zeta(4, 3, 0);
        let ax_2 = s.get_with_zeta(2, 3, 0);
        let ax_0 = s.get_with_zeta(0, 3, 0);
        let ax_3 = s.get_with_zeta(3, 3, 1);
        s.c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 4, 1);
        let ax_1 = s.get_with_zeta(1, 4, 0);
        let ax_4 = s.get_with_zeta(4, 4, 1);
        let ax_2 = s.get_with_zeta(2, 4, 0);
        let ax_0 = s.get_with_zeta(0, 4, 0);
        s.c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 4, 0);
        let ax_1 = s.get_with_zeta(1, 4, 1);
        let ax_4 = s.get_with_zeta(4, 4, 0);
        let ax_2 = s.get_with_zeta(2, 4, 1);
        let ax_0 = s.get_with_zeta(0, 4, 1);
        s.c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let c_x4_zeta0 = s.c[4][0];
        let c_x1_zeta1 = s.c[1][1];
        let c_x3_zeta0 = s.c[3][0];
        let c_x0_zeta1 = s.c[0][1];
        let c_x2_zeta0 = s.c[2][0];
        let c_x4_zeta1 = s.c[4][1];
        let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
        s.d[0][0] = d_x0_zeta0;
        let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
        s.d[2][1] = d_x2_zeta1;
        let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
        s.d[4][0] = d_x4_zeta0;
        let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
        s.d[1][1] = d_x1_zeta1;
        let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
        s.d[3][0] = d_x3_zeta0;
        let c_x1_zeta0 = s.c[1][0];
        let c_x3_zeta1 = s.c[3][1];
        let c_x2_zeta1 = s.c[2][1];
        let c_x0_zeta0 = s.c[0][0];
        let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
        s.d[0][1] = d_x0_zeta1;
        let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
        s.d[2][0] = d_x2_zeta0;
        let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
        s.d[4][1] = d_x4_zeta1;
        let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
        s.d[1][0] = d_x1_zeta0;
        let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
        s.d[3][1] = d_x3_zeta1;
    }
    #[cfg(not(feature = "full-unroll"))]
    let i = s.i;
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(0, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(0, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(0, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(0, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(22),
                (a3 ^ d3).rotate_left(11),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0;
        #[cfg(feature = "full-unroll")]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 3];
        };
        #[cfg(not(feature = "full-unroll"))]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[i];
        };
        s.set_with_zeta(0, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(0, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(0, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(0, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(0, 4, 0, ax4);
    }
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(0, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(0, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(0, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(0, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(21),
                (a3 ^ d3).rotate_left(10),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0;
        #[cfg(feature = "full-unroll")]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 3];
        };
        #[cfg(not(feature = "full-unroll"))]
        {
            ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[i];
            s.i = i + 1;
        };
        s.set_with_zeta(0, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(0, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(0, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(0, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(0, 4, 1, ax4);
    }
    {
        let (bx2, bx3) = {
            let a0 = s.get_with_zeta(1, 0, 0);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(1, 1, 0);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(1, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(1, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(1, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(14),
                (a4 ^ d4).rotate_left(10),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(1, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(1, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(1, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(1, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(1, 4, 0, ax4);
    }
    {
        let (bx2, bx3) = {
            let a0 = s.get_with_zeta(1, 0, 1);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(1, 1, 1);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(1, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(1, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(1, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(30),
                (a3 ^ d3).rotate_left(14),
                (a4 ^ d4).rotate_left(10),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(1, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(1, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(1, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(1, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(1, 4, 1, ax4);
    }
    {
        let (bx4, bx0) = {
            let a0 = s.get_with_zeta(2, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(2, 1, 0);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(2, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(2, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(2, 4, 0);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(3),
                (a3 ^ d3).rotate_left(13),
                (a4 ^ d4).rotate_left(4),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(2, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(2, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(2, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(2, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(2, 4, 0, ax4);
    }
    {
        let (bx4, bx0) = {
            let a0 = s.get_with_zeta(2, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(2, 1, 1);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(2, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(2, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(2, 4, 1);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(3),
                (a3 ^ d3).rotate_left(12),
                (a4 ^ d4).rotate_left(4),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(2, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(2, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(2, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(2, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(2, 4, 1, ax4);
    }
    {
        let (bx1, bx2) = {
            let a0 = s.get_with_zeta(3, 0, 0);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(3, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 0);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(3, 3, 0);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(3, 4, 0);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(8),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(14),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(3, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(3, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(3, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(3, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(3, 4, 0, ax4);
    }
    {
        let (bx1, bx2) = {
            let a0 = s.get_with_zeta(3, 0, 1);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(3, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 1);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(3, 3, 1);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(3, 4, 1);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(7),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(13),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(3, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(3, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(3, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(3, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(3, 4, 1, ax4);
    }
    {
        let (bx3, bx4) = {
            let a0 = s.get_with_zeta(4, 0, 0);
            let d0 = s.d[0][1];
            let a1 = s.get_with_zeta(4, 1, 0);
            let d1 = s.d[1][0];
            ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(4, 2, 0);
            let d2 = s.d[2][0];
            let a3 = s.get_with_zeta(4, 3, 0);
            let d3 = s.d[3][1];
            let a4 = s.get_with_zeta(4, 4, 0);
            let d4 = s.d[4][1];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(28),
                (a4 ^ d4).rotate_left(20),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(4, 0, 0, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(4, 1, 0, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(4, 2, 0, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(4, 3, 0, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(4, 4, 0, ax4);
    }
    {
        let (bx3, bx4) = {
            let a0 = s.get_with_zeta(4, 0, 1);
            let d0 = s.d[0][0];
            let a1 = s.get_with_zeta(4, 1, 1);
            let d1 = s.d[1][1];
            ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(4, 2, 1);
            let d2 = s.d[2][1];
            let a3 = s.get_with_zeta(4, 3, 1);
            let d3 = s.d[3][0];
            let a4 = s.get_with_zeta(4, 4, 1);
            let d4 = s.d[4][0];
            (
                (a2 ^ d2).rotate_left(31),
                (a3 ^ d3).rotate_left(27),
                (a4 ^ d4).rotate_left(19),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
        s.set_with_zeta(4, 0, 1, ax0);
        let ax1 = bx1 ^ ((!bx2) & bx3);
        s.set_with_zeta(4, 1, 1, ax1);
        let ax2 = bx2 ^ ((!bx3) & bx4);
        s.set_with_zeta(4, 2, 1, ax2);
        let ax3 = bx3 ^ ((!bx4) & bx0);
        s.set_with_zeta(4, 3, 1, ax3);
        let ax4 = bx4 ^ ((!bx0) & bx1);
        s.set_with_zeta(4, 4, 1, ax4);
    }
}

// What is interesting is that I assumed that not inlining here should be relatively cheap, because
// it's just 6 calls more per permutation, but commenting out the inline here gives a 10%
// performance hit, e.g.
//   [CYCLE_MEASUREMENT libcrux SHAKE256 (PRF_ETA1_RANDOMNESS_1024)] : + 21535 cycles
// vs
//   [CYCLE_MEASUREMENT libcrux SHAKE256 (PRF_ETA1_RANDOMNESS_1024)] : + 19139 cycles
#[inline(always)]
pub(crate) fn keccakf1600_4rounds<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round0::<BASE_ROUND>(s);
    keccakf1600_round1::<BASE_ROUND>(s);
    keccakf1600_round2::<BASE_ROUND>(s);
    keccakf1600_round3::<BASE_ROUND>(s);
}

#[inline(never)]
pub(crate) fn keccakf1600(s: &mut KeccakState) {
    #[cfg(not(feature = "full-unroll"))]
    for _ in 0..6 {
        // dummy base round, is ignored if we don't unroll
        keccakf1600_4rounds::<0>(s);
    }
    #[cfg(feature = "full-unroll")]
    {
        keccakf1600_4rounds::<0>(s);
        keccakf1600_4rounds::<4>(s);
        keccakf1600_4rounds::<8>(s);
        keccakf1600_4rounds::<12>(s);
        keccakf1600_4rounds::<16>(s);
        keccakf1600_4rounds::<20>(s);
    }
    s.i = 0;
}

#[inline(always)]
pub(crate) fn absorb_block<const RATE: usize>(s: &mut KeccakState, blocks: &[U8], start: usize) {
    s.load_block::<RATE>(blocks, start);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn absorb_final<const RATE: usize, const DELIM: u8>(
    s: &mut KeccakState,
    last: &[U8],
    start: usize,
    len: usize,
) {
    debug_assert!(len < RATE); // && last[0].len() < RATE

    let mut blocks = [0u8; WIDTH].classify();
    if len > 0 {
        blocks[0..len].copy_from_slice(&last[start..start + len]);
    }
    blocks[len] = DELIM.classify();
    blocks[RATE - 1] |= 0x80;
    s.load_block_full::<RATE>(&blocks, 0);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn squeeze_first_block<const RATE: usize>(s: &KeccakState, out: &mut [U8]) {
    s.store_block::<RATE>(out)
}

#[inline(always)]
pub(crate) fn squeeze_next_block<const RATE: usize>(s: &mut KeccakState, out: &mut [U8]) {
    keccakf1600(s);
    s.store_block::<RATE>(out)
}

#[inline(always)]
pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(s: &mut KeccakState, out: &mut [U8]) {
    let (mut o0, o1) = Lane2U32::split_at_mut_n(out, RATE);
    squeeze_first_block::<RATE>(s, &mut o0);
    let (mut o1, mut o2) = Lane2U32::split_at_mut_n(o1, RATE);
    squeeze_next_block::<RATE>(s, &mut o1);
    squeeze_next_block::<RATE>(s, &mut o2);
}

#[inline(always)]
pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(s: &mut KeccakState, out: &mut [U8]) {
    let (mut o0, o1) = Lane2U32::split_at_mut_n(out, RATE);
    squeeze_first_block::<RATE>(s, &mut o0);
    let (mut o1, o2) = Lane2U32::split_at_mut_n(o1, RATE);

    squeeze_next_block::<RATE>(s, &mut o1);
    let (mut o2, o3) = Lane2U32::split_at_mut_n(o2, RATE);

    squeeze_next_block::<RATE>(s, &mut o2);
    let (mut o3, mut o4) = Lane2U32::split_at_mut_n(o3, RATE);

    squeeze_next_block::<RATE>(s, &mut o3);
    squeeze_next_block::<RATE>(s, &mut o4);
}

#[inline(always)]
pub(crate) fn squeeze_last<const RATE: usize>(mut s: KeccakState, out: &mut [U8]) {
    keccakf1600(&mut s);
    let mut b = [0u8; 200].classify();
    s.store_block_full::<RATE>(&mut b);
    out.copy_from_slice(&b[0..out.len()]);
}

#[inline(always)]
pub(crate) fn squeeze_first_and_last<const RATE: usize>(s: &KeccakState, out: &mut [U8]) {
    let mut b = [0u8; 200].classify();
    s.store_block_full::<RATE>(&mut b);
    out.copy_from_slice(&b[0..out.len()]);
}

// in bytes; this is the 1600 (in bits) in keccak-f[1600]
const WIDTH: usize = 200;

#[inline(always)]
pub(crate) fn keccak<const RATE: usize, const DELIM: u8>(data: &[U8], out: &mut [U8]) {
    let n = data.len() / RATE;
    let rem = data.len() % RATE;

    let outlen = out.len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    let mut s = KeccakState::new();

    for i in 0..n {
        absorb_block::<RATE>(&mut s, &data, i * RATE);
    }

    absorb_final::<RATE, DELIM>(&mut s, data, data.len() - rem, rem);

    if blocks == 0 {
        squeeze_first_and_last::<RATE>(&s, out)
    } else {
        let (mut o0, mut o1) = Lane2U32::split_at_mut_n(out, RATE);
        squeeze_first_block::<RATE>(&s, &mut o0);
        for _i in 1..blocks {
            let (mut o, orest) = Lane2U32::split_at_mut_n(o1, RATE);
            squeeze_next_block::<RATE>(&mut s, &mut o);
            o1 = orest;
        }
        if last < outlen {
            squeeze_last::<RATE>(s, o1)
        }
    }
}

#[cfg(feature = "check-secret-independence")]
trait RotateLeft {
    fn rotate_left(self, n: u32) -> Self;
}

#[cfg(feature = "check-secret-independence")]
impl RotateLeft for U32 {
    fn rotate_left(self, n: u32) -> Self {
        self.declassify().rotate_left(n).classify()
    }
}
