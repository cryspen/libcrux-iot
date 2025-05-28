//! The generic SHA3 implementation that uses portable or platform specific
//! sub-routines.

use crate::traits::*;

#[cfg_attr(hax, hax_lib::opaque)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct KeccakState<const N: usize, T: KeccakStateItem<N>> {
    st: [T; 25],
}

impl KeccakState<1, Lane2U32> {
    fn get_with_zeta(&self, i: usize, j: usize, zeta: usize) -> u32 {
        self.st[5 * j + i][zeta]
    }

    fn set_with_zeta(&mut self, i: usize, j: usize, zeta: usize, v: u32) {
        self.st[5 * j + i][zeta] = v
    }
}

impl<const N: usize, T: KeccakStateItem<N>> KeccakState<N, T> {
    /// Create a new Shake128 x4 state.
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {
            st: [T::zero(); 25],
        }
    }
}

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
#[cfg_attr(hax, hax_lib::opaque)]
pub(crate) struct KeccakXofState<const RATE: usize> {
    inner: KeccakState<PARALLEL_LANES, STATE>,

    // Buffer inputs on absorb.
    buf: [[u8; RATE]; PARALLEL_LANES],

    // Buffered length.
    buf_len: usize,

    // Needs sponge.
    sponge: bool,
}

const PARALLEL_LANES: usize = 1;
type STATE = Lane2U32;

impl<const RATE: usize> KeccakXofState<RATE> {
    /// An all zero block
    pub(crate) const fn zero_block() -> [u8; RATE] {
        [0u8; RATE]
    }

    /// Generate a new keccak xof state.
    pub(crate) fn new() -> Self {
        Self {
            inner: KeccakState::new(),
            buf: [Self::zero_block(); PARALLEL_LANES],
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
    pub(crate) fn absorb(&mut self, inputs: &[&[u8]; PARALLEL_LANES]) {
        let input_remainder_len = self.absorb_full(inputs);

        // ... buffer the rest if there's not enough input (left).
        if input_remainder_len > 0 {
            debug_assert!(
                self.buf_len == 0  // We consumed everything (or it was empty all along).
                 || self.buf_len + input_remainder_len <= RATE
            );

            let input_len = inputs[0].len();
            for i in 0..PARALLEL_LANES {
                self.buf[i][self.buf_len..self.buf_len + input_remainder_len]
                    .copy_from_slice(&inputs[i][input_len - input_remainder_len..]);
            }
            self.buf_len += input_remainder_len;
        }
    }

    fn absorb_full(&mut self, inputs: &[&[u8]; PARALLEL_LANES]) -> usize {
        debug_assert!(PARALLEL_LANES > 0);
        debug_assert!(self.buf_len < RATE);
        #[cfg(debug_assertions)]
        {
            for block in inputs {
                debug_assert!(block.len() == inputs[0].len());
            }
        }

        // Check if there are buffered bytes to absorb first and consume them.
        let input_consumed = self.fill_buffer(inputs);

        if input_consumed > 0 {
            let mut borrowed = [[0u8; RATE].as_slice(); PARALLEL_LANES];
            // We have a full block in the local buffer now.
            for i in 0..PARALLEL_LANES {
                borrowed[i] = &self.buf[i];
            }
            STATE::load_block::<RATE>(&mut self.inner.st, &borrowed, 0);
            keccakf1600(&mut self.inner);

            // "empty" the local buffer
            self.buf_len = 0;
        }

        // We only need to consume the rest of the input.
        let input_to_consume = inputs[0].len() - input_consumed;

        // Consume the (rest of the) input ...
        let num_blocks = input_to_consume / RATE;
        let remainder = input_to_consume % RATE;
        for i in 0..num_blocks {
            // We only get in here if `input_len / RATE > 0`.
            STATE::load_block::<RATE>(&mut self.inner.st, &inputs, input_consumed + i * RATE);
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
    fn fill_buffer(&mut self, inputs: &[&[u8]; PARALLEL_LANES]) -> usize {
        let input_len = inputs[0].len();
        let mut consumed = 0;
        if self.buf_len > 0 {
            // There's something buffered internally to consume.
            if self.buf_len + input_len >= RATE {
                // We have enough data when combining the internal buffer and
                // the input.
                consumed = RATE - self.buf_len;
                for i in 0..PARALLEL_LANES {
                    self.buf[i][self.buf_len..].copy_from_slice(&inputs[i][..consumed]);
                }
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
    pub(crate) fn absorb_final<const DELIMITER: u8>(&mut self, inputs: &[&[u8]; PARALLEL_LANES]) {
        let input_remainder_len = self.absorb_full(inputs);

        // Consume the remaining bytes.
        // This may be in the local buffer or in the input.
        let input_len = inputs[0].len();
        let mut blocks = [[0u8; 200]; PARALLEL_LANES];
        for i in 0..PARALLEL_LANES {
            if self.buf_len > 0 {
                blocks[i][0..self.buf_len].copy_from_slice(&self.buf[i][0..self.buf_len]);
            }
            if input_remainder_len > 0 {
                blocks[i][self.buf_len..self.buf_len + input_remainder_len]
                    .copy_from_slice(&inputs[i][input_len - input_remainder_len..]);
            }
            blocks[i][self.buf_len + input_remainder_len] = DELIMITER;
            blocks[i][RATE - 1] |= 0x80;
        }

        STATE::load_block_full::<RATE>(&mut self.inner.st, &blocks, 0);
        keccakf1600(&mut self.inner);
    }

    /// Squeeze `N` x `LEN` bytes.
    #[inline(always)]
    pub(crate) fn squeeze(&mut self, out: [&mut [u8]; PARALLEL_LANES]) {
        if self.sponge {
            // If we called `squeeze` before, call f1600 first.
            // We do it this way around so that we don't call f1600 at the end
            // when we don't need it.
            keccakf1600(&mut self.inner);
        }

        // How many blocks do we need to squeeze out?
        let out_len = out[0].len();
        let blocks = out_len / RATE;
        let last = out_len - (out_len % RATE);

        // Squeeze out one to start with.
        // XXX: Eurydice does not extract `core::cmp::min`, so we do
        // this instead. (cf. https://github.com/AeneasVerif/eurydice/issues/49)
        let mid = if RATE >= out_len { out_len } else { RATE };
        let (out0, mut out_rest) = STATE::split_at_mut_n(out, mid);
        STATE::store::<RATE>(&self.inner.st, out0);

        // If we got asked for more than one block, squeeze out more.
        for _ in 1..blocks {
            // Here we know that we always have full blocks to write out.
            let (out0, tmp) = STATE::split_at_mut_n(out_rest, RATE);
            keccakf1600(&mut self.inner);
            STATE::store::<RATE>(&self.inner.st, out0);
            out_rest = tmp;
        }

        if last < out_len {
            // Squeeze out the last partial block
            keccakf1600(&mut self.inner);
            STATE::store::<RATE>(&self.inner.st, out_rest);
        }

        self.sponge = true;
    }
}

//// From here, everything is generic

use crate::portable_keccak::Lane2U32;
use crate::traits::internal::KeccakItem;

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

#[inline(always)]
pub(crate) fn keccakf1600_round0(
    s: &mut KeccakState<1, Lane2U32>,
    c: &mut [Lane2U32; 5],
    d: &mut [Lane2U32; 5],
    i: usize,
) {
    {
        let ax_0 = s.get_with_zeta(0, 0, 0);
        let ax_1 = s.get_with_zeta(1, 0, 0);
        let ax_2 = s.get_with_zeta(2, 0, 0);
        let ax_3 = s.get_with_zeta(3, 0, 0);
        let ax_4 = s.get_with_zeta(4, 0, 0);
        c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 0, 1);
        let ax_1 = s.get_with_zeta(1, 0, 1);
        let ax_2 = s.get_with_zeta(2, 0, 1);
        let ax_3 = s.get_with_zeta(3, 0, 1);
        let ax_4 = s.get_with_zeta(4, 0, 1);
        c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 1, 0);
        let ax_1 = s.get_with_zeta(1, 1, 0);
        let ax_2 = s.get_with_zeta(2, 1, 0);
        let ax_3 = s.get_with_zeta(3, 1, 0);
        let ax_4 = s.get_with_zeta(4, 1, 0);
        c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 1, 1);
        let ax_1 = s.get_with_zeta(1, 1, 1);
        let ax_2 = s.get_with_zeta(2, 1, 1);
        let ax_3 = s.get_with_zeta(3, 1, 1);
        let ax_4 = s.get_with_zeta(4, 1, 1);
        c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 2, 0);
        let ax_1 = s.get_with_zeta(1, 2, 0);
        let ax_2 = s.get_with_zeta(2, 2, 0);
        let ax_3 = s.get_with_zeta(3, 2, 0);
        let ax_4 = s.get_with_zeta(4, 2, 0);
        c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 2, 1);
        let ax_1 = s.get_with_zeta(1, 2, 1);
        let ax_2 = s.get_with_zeta(2, 2, 1);
        let ax_3 = s.get_with_zeta(3, 2, 1);
        let ax_4 = s.get_with_zeta(4, 2, 1);
        c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 3, 0);
        let ax_1 = s.get_with_zeta(1, 3, 0);
        let ax_2 = s.get_with_zeta(2, 3, 0);
        let ax_3 = s.get_with_zeta(3, 3, 0);
        let ax_4 = s.get_with_zeta(4, 3, 0);
        c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 3, 1);
        let ax_1 = s.get_with_zeta(1, 3, 1);
        let ax_2 = s.get_with_zeta(2, 3, 1);
        let ax_3 = s.get_with_zeta(3, 3, 1);
        let ax_4 = s.get_with_zeta(4, 3, 1);
        c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 4, 0);
        let ax_1 = s.get_with_zeta(1, 4, 0);
        let ax_2 = s.get_with_zeta(2, 4, 0);
        let ax_3 = s.get_with_zeta(3, 4, 0);
        let ax_4 = s.get_with_zeta(4, 4, 0);
        c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 4, 1);
        let ax_1 = s.get_with_zeta(1, 4, 1);
        let ax_2 = s.get_with_zeta(2, 4, 1);
        let ax_3 = s.get_with_zeta(3, 4, 1);
        let ax_4 = s.get_with_zeta(4, 4, 1);
        c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let c_x4_zeta0 = c[4][0];
        let c_x1_zeta1 = c[1][1];
        let c_x3_zeta0 = c[3][0];
        let c_x0_zeta1 = c[0][1];
        let c_x2_zeta0 = c[2][0];
        let c_x4_zeta1 = c[4][1];
        let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
        d[0][0] = d_x0_zeta0;
        let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
        d[2][1] = d_x2_zeta1;
        let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
        d[4][0] = d_x4_zeta0;
        let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
        d[1][1] = d_x1_zeta1;
        let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
        d[3][0] = d_x3_zeta0;
        let c_x1_zeta0 = c[1][0];
        let c_x3_zeta1 = c[3][1];
        let c_x2_zeta1 = c[2][1];
        let c_x0_zeta0 = c[0][0];
        let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
        d[0][1] = d_x0_zeta1;
        let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
        d[2][0] = d_x2_zeta0;
        let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
        d[4][1] = d_x4_zeta1;
        let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
        d[1][0] = d_x1_zeta0;
        let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
        d[3][1] = d_x3_zeta1;
    }
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 0);
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(1, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(2, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(3, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(4, 4, 0);
            let d4 = d[4][0];
            (
                (a2 ^ d2).rotate_left(22),
                (a3 ^ d3).rotate_left(11),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(1, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(2, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(3, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(4, 4, 1);
            let d4 = d[4][1];
            (
                (a2 ^ d2).rotate_left(21),
                (a3 ^ d3).rotate_left(10),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(3, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(4, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(0, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(1, 4, 0);
            let d4 = d[4][0];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(3, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(4, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(0, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(1, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(0, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(1, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(2, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(3, 4, 0);
            let d4 = d[4][0];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(0, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(1, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(2, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(3, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(2, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(4, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(0, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(2, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(4, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(0, 4, 0);
            let d4 = d[4][0];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(4, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(0, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(1, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(2, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(4, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(0, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(1, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(2, 4, 0);
            let d4 = d[4][0];
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
    let az0 = s.get_with_zeta(0, 0, 0);
    let az1 = s.get_with_zeta(0, 0, 1);
    s.set_with_zeta(0, 0, 0, az0 ^ RC_INTERLEAVED_0[i]);
    s.set_with_zeta(0, 0, 1, az1 ^ RC_INTERLEAVED_1[i]);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1(
    s: &mut KeccakState<1, Lane2U32>,
    c: &mut [Lane2U32; 5],
    d: &mut [Lane2U32; 5],
    i: usize,
) {
    {
        let ax_0 = s.get_with_zeta(0, 0, 0);
        let ax_2 = s.get_with_zeta(2, 0, 1);
        let ax_4 = s.get_with_zeta(4, 0, 0);
        let ax_1 = s.get_with_zeta(1, 0, 0);
        let ax_3 = s.get_with_zeta(3, 0, 1);
        c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 0, 1);
        let ax_2 = s.get_with_zeta(2, 0, 0);
        let ax_4 = s.get_with_zeta(4, 0, 1);
        let ax_1 = s.get_with_zeta(1, 0, 1);
        let ax_3 = s.get_with_zeta(3, 0, 0);
        c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 1, 0);
        let ax_3 = s.get_with_zeta(3, 1, 1);
        let ax_0 = s.get_with_zeta(0, 1, 1);
        let ax_2 = s.get_with_zeta(2, 1, 0);
        let ax_4 = s.get_with_zeta(4, 1, 0);
        c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 1, 1);
        let ax_3 = s.get_with_zeta(3, 1, 0);
        let ax_0 = s.get_with_zeta(0, 1, 0);
        let ax_2 = s.get_with_zeta(2, 1, 1);
        let ax_4 = s.get_with_zeta(4, 1, 1);
        c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 2, 1);
        let ax_4 = s.get_with_zeta(4, 2, 1);
        let ax_1 = s.get_with_zeta(1, 2, 0);
        let ax_3 = s.get_with_zeta(3, 2, 1);
        let ax_0 = s.get_with_zeta(0, 2, 0);
        c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 2, 0);
        let ax_4 = s.get_with_zeta(4, 2, 0);
        let ax_1 = s.get_with_zeta(1, 2, 1);
        let ax_3 = s.get_with_zeta(3, 2, 0);
        let ax_0 = s.get_with_zeta(0, 2, 1);
        c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 3, 1);
        let ax_0 = s.get_with_zeta(0, 3, 0);
        let ax_2 = s.get_with_zeta(2, 3, 1);
        let ax_4 = s.get_with_zeta(4, 3, 0);
        let ax_1 = s.get_with_zeta(1, 3, 1);
        c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 3, 0);
        let ax_0 = s.get_with_zeta(0, 3, 1);
        let ax_2 = s.get_with_zeta(2, 3, 0);
        let ax_4 = s.get_with_zeta(4, 3, 1);
        let ax_1 = s.get_with_zeta(1, 3, 0);
        c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 4, 0);
        let ax_1 = s.get_with_zeta(1, 4, 0);
        let ax_3 = s.get_with_zeta(3, 4, 0);
        let ax_0 = s.get_with_zeta(0, 4, 1);
        let ax_2 = s.get_with_zeta(2, 4, 1);
        c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 4, 1);
        let ax_1 = s.get_with_zeta(1, 4, 1);
        let ax_3 = s.get_with_zeta(3, 4, 1);
        let ax_0 = s.get_with_zeta(0, 4, 0);
        let ax_2 = s.get_with_zeta(2, 4, 0);
        c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let c_x4_zeta0 = c[4][0];
        let c_x1_zeta1 = c[1][1];
        let c_x3_zeta0 = c[3][0];
        let c_x0_zeta1 = c[0][1];
        let c_x2_zeta0 = c[2][0];
        let c_x4_zeta1 = c[4][1];
        let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
        d[0][0] = d_x0_zeta0;
        let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
        d[2][1] = d_x2_zeta1;
        let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
        d[4][0] = d_x4_zeta0;
        let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
        d[1][1] = d_x1_zeta1;
        let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
        d[3][0] = d_x3_zeta0;
        let c_x1_zeta0 = c[1][0];
        let c_x3_zeta1 = c[3][1];
        let c_x2_zeta1 = c[2][1];
        let c_x0_zeta0 = c[0][0];
        let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
        d[0][1] = d_x0_zeta1;
        let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
        d[2][0] = d_x2_zeta0;
        let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
        d[4][1] = d_x4_zeta1;
        let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
        d[1][0] = d_x1_zeta0;
        let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
        d[3][1] = d_x3_zeta1;
    }
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 0);
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(3, 1, 1);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(1, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(4, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(2, 4, 1);
            let d4 = d[4][0];
            (
                (a2 ^ d2).rotate_left(22),
                (a3 ^ d3).rotate_left(11),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(3, 1, 0);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(1, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(4, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(2, 4, 0);
            let d4 = d[4][1];
            (
                (a2 ^ d2).rotate_left(21),
                (a3 ^ d3).rotate_left(10),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(2, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(0, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(3, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(1, 4, 0);
            let d4 = d[4][0];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(2, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(0, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(3, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(1, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(1, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(4, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(2, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(0, 4, 1);
            let d4 = d[4][0];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(1, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(4, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(2, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(0, 4, 0);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(0, 1, 1);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(1, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(4, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(0, 1, 0);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(1, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(4, 4, 0);
            let d4 = d[4][0];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(4, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(2, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(0, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(3, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(4, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(2, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(0, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(3, 4, 0);
            let d4 = d[4][0];
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
    let az0 = s.get_with_zeta(0, 0, 0);
    let az1 = s.get_with_zeta(0, 0, 1);
    s.set_with_zeta(0, 0, 0, az0 ^ RC_INTERLEAVED_0[i]);
    s.set_with_zeta(0, 0, 1, az1 ^ RC_INTERLEAVED_1[i]);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2(
    s: &mut KeccakState<1, Lane2U32>,
    c: &mut [Lane2U32; 5],
    d: &mut [Lane2U32; 5],
    i: usize,
) {
    {
        let ax_0 = s.get_with_zeta(0, 0, 0);
        let ax_4 = s.get_with_zeta(4, 0, 1);
        let ax_3 = s.get_with_zeta(3, 0, 1);
        let ax_2 = s.get_with_zeta(2, 0, 1);
        let ax_1 = s.get_with_zeta(1, 0, 1);
        c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 0, 1);
        let ax_4 = s.get_with_zeta(4, 0, 0);
        let ax_3 = s.get_with_zeta(3, 0, 0);
        let ax_2 = s.get_with_zeta(2, 0, 0);
        let ax_1 = s.get_with_zeta(1, 0, 0);
        c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 1, 1);
        let ax_2 = s.get_with_zeta(2, 1, 1);
        let ax_1 = s.get_with_zeta(1, 1, 1);
        let ax_0 = s.get_with_zeta(0, 1, 1);
        let ax_4 = s.get_with_zeta(4, 1, 0);
        c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 1, 0);
        let ax_2 = s.get_with_zeta(2, 1, 0);
        let ax_1 = s.get_with_zeta(1, 1, 0);
        let ax_0 = s.get_with_zeta(0, 1, 0);
        let ax_4 = s.get_with_zeta(4, 1, 1);
        c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 2, 1);
        let ax_0 = s.get_with_zeta(0, 2, 1);
        let ax_4 = s.get_with_zeta(4, 2, 1);
        let ax_3 = s.get_with_zeta(3, 2, 0);
        let ax_2 = s.get_with_zeta(2, 2, 1);
        c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 2, 0);
        let ax_0 = s.get_with_zeta(0, 2, 0);
        let ax_4 = s.get_with_zeta(4, 2, 0);
        let ax_3 = s.get_with_zeta(3, 2, 1);
        let ax_2 = s.get_with_zeta(2, 2, 0);
        c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 3, 1);
        let ax_3 = s.get_with_zeta(3, 3, 1);
        let ax_2 = s.get_with_zeta(2, 3, 0);
        let ax_1 = s.get_with_zeta(1, 3, 1);
        let ax_0 = s.get_with_zeta(0, 3, 1);
        c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 3, 0);
        let ax_3 = s.get_with_zeta(3, 3, 0);
        let ax_2 = s.get_with_zeta(2, 3, 1);
        let ax_1 = s.get_with_zeta(1, 3, 0);
        let ax_0 = s.get_with_zeta(0, 3, 0);
        c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 4, 1);
        let ax_1 = s.get_with_zeta(1, 4, 0);
        let ax_0 = s.get_with_zeta(0, 4, 1);
        let ax_4 = s.get_with_zeta(4, 4, 1);
        let ax_3 = s.get_with_zeta(3, 4, 1);
        c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 4, 0);
        let ax_1 = s.get_with_zeta(1, 4, 1);
        let ax_0 = s.get_with_zeta(0, 4, 0);
        let ax_4 = s.get_with_zeta(4, 4, 0);
        let ax_3 = s.get_with_zeta(3, 4, 0);
        c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let c_x4_zeta0 = c[4][0];
        let c_x1_zeta1 = c[1][1];
        let c_x3_zeta0 = c[3][0];
        let c_x0_zeta1 = c[0][1];
        let c_x2_zeta0 = c[2][0];
        let c_x4_zeta1 = c[4][1];
        let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
        d[0][0] = d_x0_zeta0;
        let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
        d[2][1] = d_x2_zeta1;
        let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
        d[4][0] = d_x4_zeta0;
        let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
        d[1][1] = d_x1_zeta1;
        let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
        d[3][0] = d_x3_zeta0;
        let c_x1_zeta0 = c[1][0];
        let c_x3_zeta1 = c[3][1];
        let c_x2_zeta1 = c[2][1];
        let c_x0_zeta0 = c[0][0];
        let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
        d[0][1] = d_x0_zeta1;
        let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
        d[2][0] = d_x2_zeta0;
        let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
        d[4][1] = d_x4_zeta1;
        let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
        d[1][0] = d_x1_zeta0;
        let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
        d[3][1] = d_x3_zeta1;
    }
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 0);
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(2, 1, 1);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(4, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(1, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(3, 4, 1);
            let d4 = d[4][0];
            (
                (a2 ^ d2).rotate_left(22),
                (a3 ^ d3).rotate_left(11),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(2, 1, 0);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(4, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(1, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(3, 4, 0);
            let d4 = d[4][1];
            (
                (a2 ^ d2).rotate_left(21),
                (a3 ^ d3).rotate_left(10),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(0, 1, 0);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(2, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(4, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(1, 4, 0);
            let d4 = d[4][0];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(0, 1, 1);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(2, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(4, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(1, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(3, 1, 0);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(0, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(2, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(4, 4, 1);
            let d4 = d[4][0];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(3, 1, 1);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(0, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(2, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(4, 4, 0);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(1, 1, 1);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(0, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(2, 4, 0);
            let d4 = d[4][1];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(1, 1, 0);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(0, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(2, 4, 1);
            let d4 = d[4][0];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(4, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(1, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(3, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(0, 4, 0);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(4, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(1, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(3, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(0, 4, 1);
            let d4 = d[4][0];
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
    let az0 = s.get_with_zeta(0, 0, 0);
    let az1 = s.get_with_zeta(0, 0, 1);
    s.set_with_zeta(0, 0, 0, az0 ^ RC_INTERLEAVED_0[i]);
    s.set_with_zeta(0, 0, 1, az1 ^ RC_INTERLEAVED_1[i]);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3(
    s: &mut KeccakState<1, Lane2U32>,
    c: &mut [Lane2U32; 5],
    d: &mut [Lane2U32; 5],
    i: usize,
) {
    {
        let ax_0 = s.get_with_zeta(0, 0, 0);
        let ax_3 = s.get_with_zeta(3, 0, 0);
        let ax_1 = s.get_with_zeta(1, 0, 1);
        let ax_4 = s.get_with_zeta(4, 0, 1);
        let ax_2 = s.get_with_zeta(2, 0, 0);
        c[0][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_0 = s.get_with_zeta(0, 0, 1);
        let ax_3 = s.get_with_zeta(3, 0, 1);
        let ax_1 = s.get_with_zeta(1, 0, 0);
        let ax_4 = s.get_with_zeta(4, 0, 0);
        let ax_2 = s.get_with_zeta(2, 0, 1);
        c[0][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 1, 1);
        let ax_0 = s.get_with_zeta(0, 1, 0);
        let ax_3 = s.get_with_zeta(3, 1, 0);
        let ax_1 = s.get_with_zeta(1, 1, 1);
        let ax_4 = s.get_with_zeta(4, 1, 0);
        c[1][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_2 = s.get_with_zeta(2, 1, 0);
        let ax_0 = s.get_with_zeta(0, 1, 1);
        let ax_3 = s.get_with_zeta(3, 1, 1);
        let ax_1 = s.get_with_zeta(1, 1, 0);
        let ax_4 = s.get_with_zeta(4, 1, 1);
        c[1][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 2, 0);
        let ax_2 = s.get_with_zeta(2, 2, 0);
        let ax_0 = s.get_with_zeta(0, 2, 1);
        let ax_3 = s.get_with_zeta(3, 2, 1);
        let ax_1 = s.get_with_zeta(1, 2, 1);
        c[2][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_4 = s.get_with_zeta(4, 2, 1);
        let ax_2 = s.get_with_zeta(2, 2, 1);
        let ax_0 = s.get_with_zeta(0, 2, 0);
        let ax_3 = s.get_with_zeta(3, 2, 0);
        let ax_1 = s.get_with_zeta(1, 2, 0);
        c[2][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 3, 0);
        let ax_4 = s.get_with_zeta(4, 3, 1);
        let ax_2 = s.get_with_zeta(2, 3, 1);
        let ax_0 = s.get_with_zeta(0, 3, 1);
        let ax_3 = s.get_with_zeta(3, 3, 0);
        c[3][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_1 = s.get_with_zeta(1, 3, 1);
        let ax_4 = s.get_with_zeta(4, 3, 0);
        let ax_2 = s.get_with_zeta(2, 3, 0);
        let ax_0 = s.get_with_zeta(0, 3, 0);
        let ax_3 = s.get_with_zeta(3, 3, 1);
        c[3][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 4, 1);
        let ax_1 = s.get_with_zeta(1, 4, 0);
        let ax_4 = s.get_with_zeta(4, 4, 1);
        let ax_2 = s.get_with_zeta(2, 4, 0);
        let ax_0 = s.get_with_zeta(0, 4, 0);
        c[4][0] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let ax_3 = s.get_with_zeta(3, 4, 0);
        let ax_1 = s.get_with_zeta(1, 4, 1);
        let ax_4 = s.get_with_zeta(4, 4, 0);
        let ax_2 = s.get_with_zeta(2, 4, 1);
        let ax_0 = s.get_with_zeta(0, 4, 1);
        c[4][1] = ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4;
    }
    {
        let c_x4_zeta0 = c[4][0];
        let c_x1_zeta1 = c[1][1];
        let c_x3_zeta0 = c[3][0];
        let c_x0_zeta1 = c[0][1];
        let c_x2_zeta0 = c[2][0];
        let c_x4_zeta1 = c[4][1];
        let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
        d[0][0] = d_x0_zeta0;
        let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
        d[2][1] = d_x2_zeta1;
        let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
        d[4][0] = d_x4_zeta0;
        let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
        d[1][1] = d_x1_zeta1;
        let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
        d[3][0] = d_x3_zeta0;
        let c_x1_zeta0 = c[1][0];
        let c_x3_zeta1 = c[3][1];
        let c_x2_zeta1 = c[2][1];
        let c_x0_zeta0 = c[0][0];
        let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
        d[0][1] = d_x0_zeta1;
        let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
        d[2][0] = d_x2_zeta0;
        let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
        d[4][1] = d_x4_zeta1;
        let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
        d[1][0] = d_x1_zeta0;
        let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
        d[3][1] = d_x3_zeta1;
    }
    {
        let (bx0, bx1) = {
            let a0 = s.get_with_zeta(0, 0, 0);
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(0, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(0, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(0, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(0, 4, 0);
            let d4 = d[4][0];
            (
                (a2 ^ d2).rotate_left(22),
                (a3 ^ d3).rotate_left(11),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(0, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
        };
        let (bx2, bx3, bx4) = {
            let a2 = s.get_with_zeta(0, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(0, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(0, 4, 1);
            let d4 = d[4][1];
            (
                (a2 ^ d2).rotate_left(21),
                (a3 ^ d3).rotate_left(10),
                (a4 ^ d4).rotate_left(7),
            )
        };
        let ax0 = bx0 ^ ((!bx1) & bx2);
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(1, 1, 0);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(1, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(1, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(1, 4, 0);
            let d4 = d[4][0];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(1, 1, 1);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
        };
        let (bx4, bx0, bx1) = {
            let a2 = s.get_with_zeta(1, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(1, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(1, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(2, 1, 0);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(2, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(2, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(2, 4, 0);
            let d4 = d[4][0];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(2, 1, 1);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
        };
        let (bx1, bx2, bx3) = {
            let a2 = s.get_with_zeta(2, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(2, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(2, 4, 1);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(3, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 0);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(3, 3, 0);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(3, 4, 0);
            let d4 = d[4][1];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(3, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
        };
        let (bx3, bx4, bx0) = {
            let a2 = s.get_with_zeta(3, 2, 1);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(3, 3, 1);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(3, 4, 1);
            let d4 = d[4][0];
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
            let d0 = d[0][1];
            let a1 = s.get_with_zeta(4, 1, 0);
            let d1 = d[1][0];
            ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(4, 2, 0);
            let d2 = d[2][0];
            let a3 = s.get_with_zeta(4, 3, 0);
            let d3 = d[3][1];
            let a4 = s.get_with_zeta(4, 4, 0);
            let d4 = d[4][1];
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
            let d0 = d[0][0];
            let a1 = s.get_with_zeta(4, 1, 1);
            let d1 = d[1][1];
            ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
        };
        let (bx0, bx1, bx2) = {
            let a2 = s.get_with_zeta(4, 2, 1);
            let d2 = d[2][1];
            let a3 = s.get_with_zeta(4, 3, 1);
            let d3 = d[3][0];
            let a4 = s.get_with_zeta(4, 4, 1);
            let d4 = d[4][0];
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
    let az0 = s.get_with_zeta(0, 0, 0);
    let az1 = s.get_with_zeta(0, 0, 1);
    s.set_with_zeta(0, 0, 0, az0 ^ RC_INTERLEAVED_0[i]);
    s.set_with_zeta(0, 0, 1, az1 ^ RC_INTERLEAVED_1[i]);
}

#[inline(always)]
pub(crate) fn keccakf1600_4rounds_inner(
    s: &mut KeccakState<1, Lane2U32>,
    c: &mut [Lane2U32; 5],
    d: &mut [Lane2U32; 5],
    i: usize,
) {
    keccakf1600_round0(s, c, d, i);
    keccakf1600_round1(s, c, d, i + 1);
    keccakf1600_round2(s, c, d, i + 2);
    keccakf1600_round3(s, c, d, i + 3);
}

#[inline(always)]
pub(crate) fn keccakf1600_4rounds(s: &mut KeccakState<1, Lane2U32>) {
    let mut c: [Lane2U32; 5] = [[0; 2]; 5];
    let mut d: [Lane2U32; 5] = [[0; 2]; 5];

    keccakf1600_4rounds_inner(s, &mut c, &mut d, 0);
}

#[inline(always)]
pub(crate) fn keccakf1600(s: &mut KeccakState<1, Lane2U32>) {
    let mut c: [Lane2U32; 5] = [[0; 2]; 5];
    let mut d: [Lane2U32; 5] = [[0; 2]; 5];
    keccakf1600_4rounds_inner(s, &mut c, &mut d, 0);
    keccakf1600_4rounds_inner(s, &mut c, &mut d, 4);
    keccakf1600_4rounds_inner(s, &mut c, &mut d, 8);
    keccakf1600_4rounds_inner(s, &mut c, &mut d, 12);
    keccakf1600_4rounds_inner(s, &mut c, &mut d, 16);
    keccakf1600_4rounds_inner(s, &mut c, &mut d, 20);
}

#[inline(always)]
pub(crate) fn absorb_block<const RATE: usize>(
    s: &mut KeccakState<1, Lane2U32>,
    blocks: &[&[u8]; 1],
    start: usize,
) {
    Lane2U32::load_block::<RATE>(&mut s.st, blocks, start);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn absorb_final<const RATE: usize, const DELIM: u8>(
    s: &mut KeccakState<1, Lane2U32>,
    last: &[&[u8]; 1],
    start: usize,
    len: usize,
) {
    debug_assert!(len < RATE); // && last[0].len() < RATE

    let mut blocks = [[0u8; WIDTH]; 1];
    for i in 0..1 {
        if len > 0 {
            blocks[i][0..len].copy_from_slice(&last[i][start..start + len]);
        }
        blocks[i][len] = DELIM;
        blocks[i][RATE - 1] |= 0x80;
    }
    Lane2U32::load_block_full::<RATE>(&mut s.st, &blocks, 0);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn squeeze_first_block<const RATE: usize>(
    s: &KeccakState<1, Lane2U32>,
    out: &mut [&mut [u8]; 1],
) {
    Lane2U32::store_block::<RATE>(&s.st, out)
}

#[inline(always)]
pub(crate) fn squeeze_next_block<const RATE: usize>(
    s: &mut KeccakState<1, Lane2U32>,
    out: &mut [&mut [u8]; 1],
) {
    keccakf1600(s);
    Lane2U32::store_block::<RATE>(&s.st, out)
}

#[inline(always)]
pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(
    s: &mut KeccakState<1, Lane2U32>,
    out: [&mut [u8]; 1],
) {
    let (mut o0, o1) = Lane2U32::split_at_mut_n(out, RATE);
    squeeze_first_block::<RATE>(s, &mut o0);
    let (mut o1, mut o2) = Lane2U32::split_at_mut_n(o1, RATE);
    squeeze_next_block::<RATE>(s, &mut o1);
    squeeze_next_block::<RATE>(s, &mut o2);
}

#[inline(always)]
pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(
    s: &mut KeccakState<1, Lane2U32>,
    out: [&mut [u8]; 1],
) {
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
pub(crate) fn squeeze_last<const RATE: usize>(
    mut s: KeccakState<1, Lane2U32>,
    out: [&mut [u8]; 1],
) {
    keccakf1600(&mut s);
    let mut b = [[0u8; 200]; 1];
    Lane2U32::store_block_full::<RATE>(&s.st, &mut b);
    for i in 0..1 {
        out[i].copy_from_slice(&b[i][0..out[i].len()]);
    }
}

#[inline(always)]
pub(crate) fn squeeze_first_and_last<const RATE: usize>(
    s: &KeccakState<1, Lane2U32>,
    out: [&mut [u8]; 1],
) {
    let mut b = [[0u8; 200]; 1];
    Lane2U32::store_block_full::<RATE>(&s.st, &mut b);
    for i in 0..1 {
        out[i].copy_from_slice(&b[i][0..out[i].len()]);
    }
}

// in bytes; this is the 1600 (in bits) in keccak-f[1600]
const WIDTH: usize = 200;

#[inline(always)]
pub(crate) fn keccak<const RATE: usize, const DELIM: u8>(data: &[&[u8]; 1], out: [&mut [u8]; 1]) {
    // 1. Let P = M || pad(r, len(N))
    //   (implied?)

    // 2. Let n = len(P) / r
    let n = data[0].len() / RATE;

    // 3. Let c = b - r
    let c: usize = WIDTH - RATE;

    // 4. Let P_0..P_{n-1} be the unique sequence of strings
    // of length r such that P = P_0 || ... || P_{n-1}.
    //   (implied)

    // 5. Let S = 0^b.
    let mut s = KeccakState::<1, Lane2U32>::new();

    // 6. For i from 0 to n-1,
    for i in 0..n {
        // T::slice_n(data, i * RATE, RATE)

        // 6. (cont.) Let S = f(S XOR (P_i || 0^c))
        absorb_block::<RATE>(&mut s, &data, i * RATE);
    }

    // Handle remaining data, padding
    let rem = data[0].len() % RATE;
    // T::slice_n(data, data[0].len() - rem, rem)
    absorb_final::<RATE, DELIM>(&mut s, data, data[0].len() - rem, rem);

    let outlen = out[0].len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

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
