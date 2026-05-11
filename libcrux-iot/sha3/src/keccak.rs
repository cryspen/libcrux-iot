//! The generic SHA3 implementation that uses portable or platform specific
//! sub-routines.

#[cfg(hax)]
use hax_lib::{ToInt, ToProp};
use libcrux_secrets::{Classify, U8};
#[cfg(feature = "check-secret-independence")]
use libcrux_secrets::{Declassify, U32};

use crate::state::KeccakState;

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
pub(crate) struct KeccakXofState<const RATE: usize> {
    inner: KeccakState,

    // Buffer inputs on absorb.
    buf: [U8; RATE],

    // Buffered length.
    buf_len: usize,

    // Needs sponge.
    sponge: bool,
}

#[hax_lib::attributes]
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
    #[hax_lib::requires(
        RATE > 0 &&
        RATE % 8 == 0 &&
        RATE <= 168 &&
        self.buf_len < RATE &&
        inputs.len().to_int() + self.buf_len.to_int() <= usize::MAX.to_int()
    )]
    pub(crate) fn absorb(&mut self, inputs: &[U8]) {
        let input_remainder_len = self.absorb_full(inputs);

        // ... buffer the rest if there's not enough input (left).
        if input_remainder_len > 0 {
            #[cfg(not(eurydice))]
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

    #[hax_lib::requires(
        RATE > 0 &&
        RATE % 8 == 0 &&
        RATE <= 168 &&
        self.buf_len < RATE &&
        inputs.len().to_int() + self.buf_len.to_int() <= usize::MAX.to_int()
    )]
    #[hax_lib::ensures(|remainder|
        remainder < RATE
        && remainder <= inputs.len()
        && future(self).buf_len <= RATE
        && future(self).buf_len.to_int() + remainder.to_int() < usize::MAX.to_int()
    )]
    fn absorb_full(&mut self, inputs: &[U8]) -> usize {
        _absorb_full::<RATE>(self, inputs)
    }

    /// Consume the internal buffer and the required amount of the input to pad to
    /// `RATE`.
    ///
    /// Returns the `consumed` bytes from `inputs` if there's enough buffered
    /// content to consume, and `0` otherwise.
    /// If `consumed > 0` is returned, `self.buf` contains a full block to be
    /// loaded.
    #[hax_lib::requires(
        self.buf_len <= RATE &&
        inputs.len().to_int() + self.buf_len.to_int() <= usize::MAX.to_int()
    )]
    #[hax_lib::ensures(|res|
        (res <= RATE).to_prop()
        & (future(self).buf_len <= RATE).to_prop()
        & hax_lib::implies(res > 0, future(self).buf_len == RATE)
    )]
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
    #[hax_lib::requires(
        RATE > 0 &&
        RATE % 8 == 0 &&
        RATE <= 168 &&
        self.buf_len < RATE &&
        inputs.len().to_int() + self.buf_len.to_int() <= usize::MAX.to_int()
    )]
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
    #[hax_lib::requires(RATE > 0 && RATE % 8 == 0 && RATE <= 168)]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    // This code verifies with the z3rlimit specified below, but we
    // can't use the `options` attribute because of a hax issue.
    // cf. https://github.com/cryspen/hax/issues/1698
    pub(crate) fn squeeze(&mut self, out: &mut [U8]) {
        _squeeze(self, out);
    }
}

#[hax_lib::requires(RATE > 0 && RATE % 8 == 0 && RATE <= 168)]
#[hax_lib::fstar::options("--z3rlimit 100 --split_queries always")]
fn _squeeze<const RATE: usize>(state: &mut KeccakXofState<RATE>, out: &mut [u8]) {
    if state.sponge {
        // If we called `squeeze` before, call f1600 first.
        // We do it this way around so that we don't call f1600 at the end
        // when we don't need it.
        keccakf1600(&mut state.inner);
    }

    // How many blocks do we need to squeeze out?
    let out_len = out.len();
    let blocks = out_len / RATE;
    let last = out_len - (out_len % RATE);

    // Squeeze out one to start with.
    // XXX: Eurydice does not extract `core::cmp::min`, so we do
    // this instead. (cf. https://github.com/AeneasVerif/eurydice/issues/49)
    let mid = if RATE >= out_len { out_len } else { RATE };
    state.inner.store::<RATE>(&mut out[..mid]);

    // If we got asked for more than one block, squeeze out more.
    let mut offset = mid;
    for _k in 1..blocks {
        hax_lib::loop_invariant!(|_k: usize| {
            out.len() == out_len && offset.to_int() == _k.to_int() * RATE.to_int() &&
            offset - RATE <= out.len()
        });
        // Here we know that we always have full blocks to write out.
        squeeze_update::<RATE>(&mut state.inner, out, offset);
        // keccakf1600(&mut state.inner);
        // state.inner.store::<RATE>(&mut out[offset..offset + RATE]);
        offset += RATE;
    }

    if last > 0 && last < out_len {
        debug_assert_eq!(last, offset);
        // Squeeze out the last partial block
        keccakf1600(&mut state.inner);
        state.inner.store::<RATE>(&mut out[offset..]);
    }

    state.sponge = true;
}

#[hax_lib::requires(RATE > 0 && RATE % 8 == 0 && RATE <= 168 &&
    offset.to_int() + RATE.to_int() <= out.len().to_int()
)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
fn squeeze_update<const RATE: usize>(state: &mut KeccakState, out: &mut [u8], offset: usize) {
    keccakf1600(state);
    state.store::<RATE>(&mut out[offset..offset + RATE]);
}

#[hax_lib::requires(
        RATE > 0 &&
        RATE % 8 == 0 &&
        RATE <= 168 &&
        state.buf_len < RATE &&
        inputs.len().to_int() + state.buf_len.to_int() <= usize::MAX.to_int()
    )]
#[hax_lib::ensures(|remainder|
        remainder < RATE
        && remainder <= inputs.len()
        && future(state).buf_len <= RATE
        && future(state).buf_len.to_int() + remainder.to_int() < usize::MAX.to_int()
    )]
#[hax_lib::fstar::options("--z3rlimit 100")]
fn _absorb_full<const RATE: usize>(state: &mut KeccakXofState<RATE>, inputs: &[U8]) -> usize {
    #[cfg(not(eurydice))]
    debug_assert!(state.buf_len < RATE);

    // Check if there are buffered bytes to absorb first and consume them.
    let input_consumed = state.fill_buffer(inputs);

    if input_consumed > 0 {
        state.inner.load_block::<RATE>(&state.buf, 0);
        keccakf1600(&mut state.inner);

        // "empty" the local buffer
        state.buf_len = 0;
    }

    // We only need to consume the rest of the input.
    let input_to_consume = inputs.len() - input_consumed;

    // Consume the (rest of the) input ...
    let num_blocks = input_to_consume / RATE;
    let remainder = input_to_consume % RATE;

    #[cfg(hax)]
    let _buf_len = state.buf_len;
    for i in 0..num_blocks {
        hax_lib::loop_invariant!(|_i: usize| state.buf_len == _buf_len);

        // We only get in here if `input_len / RATE > 0`.
        state
            .inner
            .load_block::<RATE>(inputs, input_consumed + i * RATE);
        keccakf1600(&mut state.inner);
    }

    remainder
}

//// From here, everything is generic

#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
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

#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
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
pub(crate) fn keccakf1600_round0_theta_c_x0_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 0);
    let ax_1 = s.get_with_zeta(1, 0, 0);
    let ax_2 = s.get_with_zeta(2, 0, 0);
    let ax_3 = s.get_with_zeta(3, 0, 0);
    let ax_4 = s.get_with_zeta(4, 0, 0);
    s.set_lane_value(0, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_c_x0_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 1);
    let ax_1 = s.get_with_zeta(1, 0, 1);
    let ax_2 = s.get_with_zeta(2, 0, 1);
    let ax_3 = s.get_with_zeta(3, 0, 1);
    let ax_4 = s.get_with_zeta(4, 0, 1);
    s.set_lane_value(0, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_c_x1_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 1, 0);
    let ax_1 = s.get_with_zeta(1, 1, 0);
    let ax_2 = s.get_with_zeta(2, 1, 0);
    let ax_3 = s.get_with_zeta(3, 1, 0);
    let ax_4 = s.get_with_zeta(4, 1, 0);
    s.set_lane_value(1, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_c_x1_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 1, 1);
    let ax_1 = s.get_with_zeta(1, 1, 1);
    let ax_2 = s.get_with_zeta(2, 1, 1);
    let ax_3 = s.get_with_zeta(3, 1, 1);
    let ax_4 = s.get_with_zeta(4, 1, 1);
    s.set_lane_value(1, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_c_x2_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 2, 0);
    let ax_1 = s.get_with_zeta(1, 2, 0);
    let ax_2 = s.get_with_zeta(2, 2, 0);
    let ax_3 = s.get_with_zeta(3, 2, 0);
    let ax_4 = s.get_with_zeta(4, 2, 0);
    s.set_lane_value(2, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_c_x2_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 2, 1);
    let ax_1 = s.get_with_zeta(1, 2, 1);
    let ax_2 = s.get_with_zeta(2, 2, 1);
    let ax_3 = s.get_with_zeta(3, 2, 1);
    let ax_4 = s.get_with_zeta(4, 2, 1);
    s.set_lane_value(2, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_c_x3_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 3, 0);
    let ax_1 = s.get_with_zeta(1, 3, 0);
    let ax_2 = s.get_with_zeta(2, 3, 0);
    let ax_3 = s.get_with_zeta(3, 3, 0);
    let ax_4 = s.get_with_zeta(4, 3, 0);
    s.set_lane_value(3, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_c_x3_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 3, 1);
    let ax_1 = s.get_with_zeta(1, 3, 1);
    let ax_2 = s.get_with_zeta(2, 3, 1);
    let ax_3 = s.get_with_zeta(3, 3, 1);
    let ax_4 = s.get_with_zeta(4, 3, 1);
    s.set_lane_value(3, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_c_x4_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 4, 0);
    let ax_1 = s.get_with_zeta(1, 4, 0);
    let ax_2 = s.get_with_zeta(2, 4, 0);
    let ax_3 = s.get_with_zeta(3, 4, 0);
    let ax_4 = s.get_with_zeta(4, 4, 0);
    s.set_lane_value(4, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_c_x4_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 4, 1);
    let ax_1 = s.get_with_zeta(1, 4, 1);
    let ax_2 = s.get_with_zeta(2, 4, 1);
    let ax_3 = s.get_with_zeta(3, 4, 1);
    let ax_4 = s.get_with_zeta(4, 4, 1);
    s.set_lane_value(4, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_d_x0(s: &mut KeccakState) {
    let c_x4_zeta0 = s.c[4][0];
    let c_x1_zeta1 = s.c[1][1];
    let c_x4_zeta1 = s.c[4][1];
    let c_x1_zeta0 = s.c[1][0];
    s.d[0].0[0] = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
    s.d[0].0[1] = c_x4_zeta1 ^ c_x1_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_d_x1(s: &mut KeccakState) {
    let c_x0_zeta0 = s.c[0][0];
    let c_x2_zeta1 = s.c[2][1];
    let c_x0_zeta1 = s.c[0][1];
    let c_x2_zeta0 = s.c[2][0];
    s.d[1].0[0] = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
    s.d[1].0[1] = c_x0_zeta1 ^ c_x2_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_d_x2(s: &mut KeccakState) {
    let c_x1_zeta0 = s.c[1][0];
    let c_x3_zeta1 = s.c[3][1];
    let c_x1_zeta1 = s.c[1][1];
    let c_x3_zeta0 = s.c[3][0];
    s.d[2].0[0] = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
    s.d[2].0[1] = c_x1_zeta1 ^ c_x3_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_d_x3(s: &mut KeccakState) {
    let c_x2_zeta0 = s.c[2][0];
    let c_x4_zeta1 = s.c[4][1];
    let c_x2_zeta1 = s.c[2][1];
    let c_x4_zeta0 = s.c[4][0];
    s.d[3].0[0] = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
    s.d[3].0[1] = c_x2_zeta1 ^ c_x4_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_d_x4(s: &mut KeccakState) {
    let c_x3_zeta0 = s.c[3][0];
    let c_x0_zeta1 = s.c[0][1];
    let c_x3_zeta1 = s.c[3][1];
    let c_x0_zeta0 = s.c[0][0];
    s.d[4].0[0] = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
    s.d[4].0[1] = c_x3_zeta1 ^ c_x0_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta_d(s: &mut KeccakState) {
    keccakf1600_round0_theta_d_x0(s);
    keccakf1600_round0_theta_d_x1(s);
    keccakf1600_round0_theta_d_x2(s);
    keccakf1600_round0_theta_d_x3(s);
    keccakf1600_round0_theta_d_x4(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_theta(s: &mut KeccakState) {
    // C[x][zeta] = A[0,x][zeta] ^ A[1,x][zeta] ^ A[2,x][zeta] ^ A[3,x][zeta] ^ A[4,x][zeta]
    // https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.SHA3.fst#L28C1-L29C74
    keccakf1600_round0_theta_c_x0_z0(s);
    keccakf1600_round0_theta_c_x0_z1(s);
    keccakf1600_round0_theta_c_x1_z0(s);
    keccakf1600_round0_theta_c_x1_z1(s);
    keccakf1600_round0_theta_c_x2_z0(s);
    keccakf1600_round0_theta_c_x2_z1(s);
    keccakf1600_round0_theta_c_x3_z0(s);
    keccakf1600_round0_theta_c_x3_z1(s);
    keccakf1600_round0_theta_c_x4_z0(s);
    keccakf1600_round0_theta_c_x4_z1(s);
    keccakf1600_round0_theta_d(s);
}

#[derive(Clone, Copy)]
struct BxArg(usize, usize, usize, usize, u32); // x, y, zeta, d_zeta, rot

#[inline(always)]
#[hax_lib::requires(
    a.0 < 5 && a.1 < 5 && a.2 < 2 && a.3 < 2 &&
    b.0 < 5 && b.1 < 5 && b.2 < 2 && b.3 < 2
)]
fn bx_2(s: &KeccakState, a: BxArg, b: BxArg) -> (u32, u32) {
    (
        (s.get_with_zeta(a.0, a.1, a.2) ^ s.d[a.1][a.3]).rotate_left(a.4),
        (s.get_with_zeta(b.0, b.1, b.2) ^ s.d[b.1][b.3]).rotate_left(b.4),
    )
}

#[inline(always)]
#[hax_lib::requires(
    a.0 < 5 && a.1 < 5 && a.2 < 2 && a.3 < 2 &&
    b.0 < 5 && b.1 < 5 && b.2 < 2 && b.3 < 2 &&
    c.0 < 5 && c.1 < 5 && c.2 < 2 && c.3 < 2
)]
fn bx_3(s: &KeccakState, a: BxArg, b: BxArg, c: BxArg) -> (u32, u32, u32) {
    (
        (s.get_with_zeta(a.0, a.1, a.2) ^ s.d[a.1][a.3]).rotate_left(a.4),
        (s.get_with_zeta(b.0, b.1, b.2) ^ s.d[b.1][b.3]).rotate_left(b.4),
        (s.get_with_zeta(c.0, c.1, c.2) ^ s.d[c.1][c.3]).rotate_left(c.4),
    )
}

#[inline(always)]
// #[hax_lib::fstar::options("--split_queries always --fuel 1")]
#[hax_lib::requires(BASE_ROUND < 255)]
pub(crate) fn keccakf1600_round0_pi_rho_chi_1a<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = bx_2(s, BxArg(0, 0, 0, 0, 0), BxArg(1, 1, 0, 0, 22));
    let (bx2, bx3, bx4) = bx_3(
        s,
        BxArg(2, 2, 1, 1, 22),
        BxArg(3, 3, 1, 1, 11),
        BxArg(4, 4, 0, 0, 7),
    );

    let ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 0];

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

#[inline(always)]
#[hax_lib::requires(BASE_ROUND < 255)]
pub(crate) fn keccakf1600_round0_pi_rho_chi_1b<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = bx_2(s, BxArg(0, 0, 1, 1, 0), BxArg(1, 1, 1, 1, 22));
    let (bx2, bx3, bx4) = bx_3(
        s,
        BxArg(2, 2, 0, 0, 21),
        BxArg(3, 3, 0, 0, 10),
        BxArg(4, 4, 1, 1, 7),
    );

    let ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 0];

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

#[inline(always)]
// #[hax_lib::fstar::options("--split_queries always --fuel 1")]
pub(crate) fn keccakf1600_round0_pi_rho_chi_1c(s: &mut KeccakState) {
    let (bx4, bx0, bx1) = bx_3(
        s,
        BxArg(4, 2, 1, 1, 31),
        BxArg(0, 3, 0, 0, 14),
        BxArg(1, 4, 0, 0, 10),
    );
    let (bx2, bx3) = bx_2(s, BxArg(2, 0, 1, 1, 2), BxArg(3, 1, 1, 1, 23));

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

#[inline(always)]
// #[hax_lib::fstar::options("--split_queries always --fuel 1")]
pub(crate) fn keccakf1600_round0_pi_rho_chi_1d(s: &mut KeccakState) {
    let (bx4, bx0, bx1) = bx_3(
        s,
        BxArg(4, 2, 0, 0, 30),
        BxArg(0, 3, 1, 1, 14),
        BxArg(1, 4, 1, 1, 10),
    );
    let (bx2, bx3) = bx_2(s, BxArg(2, 0, 0, 0, 1), BxArg(3, 1, 0, 0, 22));

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

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
// #[hax_lib::fstar::options("--split_queries always --z3rlimit 100 --fuel 1")]
#[hax_lib::requires(BASE_ROUND < 255)]
pub(crate) fn keccakf1600_round0_pi_rho_chi_1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round0_pi_rho_chi_1a::<BASE_ROUND>(s);
    keccakf1600_round0_pi_rho_chi_1b::<BASE_ROUND>(s);
    keccakf1600_round0_pi_rho_chi_1c(s);
    keccakf1600_round0_pi_rho_chi_1d(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round0_pi_rho_chi_2a(s: &mut KeccakState) {
    let (bx4, bx0) = bx_2(s, BxArg(4, 0, 0, 0, 9), BxArg(0, 1, 1, 1, 1));
    let (bx1, bx2, bx3) = bx_3(
        s,
        BxArg(1, 2, 0, 0, 3),
        BxArg(2, 3, 1, 1, 13),
        BxArg(3, 4, 0, 0, 4),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round0_pi_rho_chi_2b(s: &mut KeccakState) {
    let (bx4, bx0) = bx_2(s, BxArg(4, 0, 1, 1, 9), BxArg(0, 1, 0, 0, 0));
    let (bx1, bx2, bx3) = bx_3(
        s,
        BxArg(1, 2, 1, 1, 3),
        BxArg(2, 3, 0, 0, 12),
        BxArg(3, 4, 1, 1, 4),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round0_pi_rho_chi_2c(s: &mut KeccakState) {
    let (bx1, bx2) = bx_2(s, BxArg(1, 0, 0, 0, 18), BxArg(2, 1, 0, 0, 5));
    let (bx3, bx4, bx0) = bx_3(
        s,
        BxArg(3, 2, 1, 1, 8),
        BxArg(4, 3, 0, 0, 28),
        BxArg(0, 4, 1, 1, 14),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round0_pi_rho_chi_2d(s: &mut KeccakState) {
    let (bx1, bx2) = bx_2(s, BxArg(1, 0, 1, 1, 18), BxArg(2, 1, 1, 1, 5));
    let (bx3, bx4, bx0) = bx_3(
        s,
        BxArg(3, 2, 0, 0, 7),
        BxArg(4, 3, 1, 1, 28),
        BxArg(0, 4, 0, 0, 13),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round0_pi_rho_chi_2e(s: &mut KeccakState) {
    let (bx0, bx1, bx2) = bx_3(
        s,
        BxArg(0, 2, 0, 0, 31),
        BxArg(1, 3, 1, 1, 28),
        BxArg(2, 4, 1, 1, 20),
    );
    let (bx3, bx4) = bx_2(s, BxArg(3, 0, 1, 1, 21), BxArg(4, 1, 0, 0, 1));
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

#[inline(always)]
pub(crate) fn keccakf1600_round0_pi_rho_chi_2f(s: &mut KeccakState) {
    let (bx0, bx1, bx2) = bx_3(
        s,
        BxArg(0, 2, 1, 1, 31),
        BxArg(1, 3, 0, 0, 27),
        BxArg(2, 4, 0, 0, 19),
    );
    let (bx3, bx4) = bx_2(s, BxArg(3, 0, 0, 0, 20), BxArg(4, 1, 1, 1, 1));
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

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1500 in")
)]
// #[hax_lib::fstar::options("--split_queries always --fuel 1")]
pub(crate) fn keccakf1600_round0_pi_rho_chi_2(s: &mut KeccakState) {
    keccakf1600_round0_pi_rho_chi_2a(s);
    keccakf1600_round0_pi_rho_chi_2b(s);
    keccakf1600_round0_pi_rho_chi_2c(s);
    keccakf1600_round0_pi_rho_chi_2d(s);
    keccakf1600_round0_pi_rho_chi_2e(s);
    keccakf1600_round0_pi_rho_chi_2f(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x0_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 0);
    let ax_2 = s.get_with_zeta(2, 0, 1);
    let ax_4 = s.get_with_zeta(4, 0, 0);
    let ax_1 = s.get_with_zeta(1, 0, 0);
    let ax_3 = s.get_with_zeta(3, 0, 1);
    s.set_lane_value(0, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x0_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 1);
    let ax_2 = s.get_with_zeta(2, 0, 0);
    let ax_4 = s.get_with_zeta(4, 0, 1);
    let ax_1 = s.get_with_zeta(1, 0, 1);
    let ax_3 = s.get_with_zeta(3, 0, 0);
    s.set_lane_value(0, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x1_z0(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 1, 0);
    let ax_3 = s.get_with_zeta(3, 1, 1);
    let ax_0 = s.get_with_zeta(0, 1, 1);
    let ax_2 = s.get_with_zeta(2, 1, 0);
    let ax_4 = s.get_with_zeta(4, 1, 0);
    s.set_lane_value(1, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x1_z1(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 1, 1);
    let ax_3 = s.get_with_zeta(3, 1, 0);
    let ax_0 = s.get_with_zeta(0, 1, 0);
    let ax_2 = s.get_with_zeta(2, 1, 1);
    let ax_4 = s.get_with_zeta(4, 1, 1);
    s.set_lane_value(1, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x2_z0(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 2, 1);
    let ax_4 = s.get_with_zeta(4, 2, 1);
    let ax_1 = s.get_with_zeta(1, 2, 0);
    let ax_3 = s.get_with_zeta(3, 2, 1);
    let ax_0 = s.get_with_zeta(0, 2, 0);
    s.set_lane_value(2, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x2_z1(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 2, 0);
    let ax_4 = s.get_with_zeta(4, 2, 0);
    let ax_1 = s.get_with_zeta(1, 2, 1);
    let ax_3 = s.get_with_zeta(3, 2, 0);
    let ax_0 = s.get_with_zeta(0, 2, 1);
    s.set_lane_value(2, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x3_z0(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 3, 1);
    let ax_0 = s.get_with_zeta(0, 3, 0);
    let ax_2 = s.get_with_zeta(2, 3, 1);
    let ax_4 = s.get_with_zeta(4, 3, 0);
    let ax_1 = s.get_with_zeta(1, 3, 1);
    s.set_lane_value(3, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x3_z1(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 3, 0);
    let ax_0 = s.get_with_zeta(0, 3, 1);
    let ax_2 = s.get_with_zeta(2, 3, 0);
    let ax_4 = s.get_with_zeta(4, 3, 1);
    let ax_1 = s.get_with_zeta(1, 3, 0);
    s.set_lane_value(3, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x4_z0(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 4, 0);
    let ax_1 = s.get_with_zeta(1, 4, 0);
    let ax_3 = s.get_with_zeta(3, 4, 0);
    let ax_0 = s.get_with_zeta(0, 4, 1);
    let ax_2 = s.get_with_zeta(2, 4, 1);
    s.set_lane_value(4, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_c_x4_z1(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 4, 1);
    let ax_1 = s.get_with_zeta(1, 4, 1);
    let ax_3 = s.get_with_zeta(3, 4, 1);
    let ax_0 = s.get_with_zeta(0, 4, 0);
    let ax_2 = s.get_with_zeta(2, 4, 0);
    s.set_lane_value(4, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_d_x0(s: &mut KeccakState) {
    let c_x4_zeta0 = s.c[4][0];
    let c_x1_zeta1 = s.c[1][1];
    let c_x4_zeta1 = s.c[4][1];
    let c_x1_zeta0 = s.c[1][0];
    s.d[0].0[0] = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
    s.d[0].0[1] = c_x4_zeta1 ^ c_x1_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_d_x1(s: &mut KeccakState) {
    let c_x0_zeta0 = s.c[0][0];
    let c_x2_zeta1 = s.c[2][1];
    let c_x0_zeta1 = s.c[0][1];
    let c_x2_zeta0 = s.c[2][0];
    s.d[1].0[0] = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
    s.d[1].0[1] = c_x0_zeta1 ^ c_x2_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_d_x2(s: &mut KeccakState) {
    let c_x1_zeta0 = s.c[1][0];
    let c_x3_zeta1 = s.c[3][1];
    let c_x1_zeta1 = s.c[1][1];
    let c_x3_zeta0 = s.c[3][0];
    s.d[2].0[0] = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
    s.d[2].0[1] = c_x1_zeta1 ^ c_x3_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_d_x3(s: &mut KeccakState) {
    let c_x2_zeta0 = s.c[2][0];
    let c_x4_zeta1 = s.c[4][1];
    let c_x2_zeta1 = s.c[2][1];
    let c_x4_zeta0 = s.c[4][0];
    s.d[3].0[0] = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
    s.d[3].0[1] = c_x2_zeta1 ^ c_x4_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_d_x4(s: &mut KeccakState) {
    let c_x3_zeta0 = s.c[3][0];
    let c_x0_zeta1 = s.c[0][1];
    let c_x3_zeta1 = s.c[3][1];
    let c_x0_zeta0 = s.c[0][0];
    s.d[4].0[0] = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
    s.d[4].0[1] = c_x3_zeta1 ^ c_x0_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta_d(s: &mut KeccakState) {
    keccakf1600_round1_theta_d_x0(s);
    keccakf1600_round1_theta_d_x1(s);
    keccakf1600_round1_theta_d_x2(s);
    keccakf1600_round1_theta_d_x3(s);
    keccakf1600_round1_theta_d_x4(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_theta(s: &mut KeccakState) {
    keccakf1600_round1_theta_c_x0_z0(s);
    keccakf1600_round1_theta_c_x0_z1(s);
    keccakf1600_round1_theta_c_x1_z0(s);
    keccakf1600_round1_theta_c_x1_z1(s);
    keccakf1600_round1_theta_c_x2_z0(s);
    keccakf1600_round1_theta_c_x2_z1(s);
    keccakf1600_round1_theta_c_x3_z0(s);
    keccakf1600_round1_theta_c_x3_z1(s);
    keccakf1600_round1_theta_c_x4_z0(s);
    keccakf1600_round1_theta_c_x4_z1(s);
    keccakf1600_round1_theta_d(s);
}

#[inline(always)]
#[hax_lib::requires(BASE_ROUND < 254)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_1a<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = bx_2(s, BxArg(0, 0, 0, 0, 0), BxArg(3, 1, 1, 0, 22));
    let (bx2, bx3, bx4) = bx_3(
        s,
        BxArg(1, 2, 1, 1, 22),
        BxArg(4, 3, 1, 1, 11),
        BxArg(2, 4, 1, 0, 7),
    );

    let ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 1];

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

#[inline(always)]
#[hax_lib::requires(BASE_ROUND < 254)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_1b<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = bx_2(s, BxArg(0, 0, 1, 1, 0), BxArg(3, 1, 0, 1, 22));
    let (bx2, bx3, bx4) = bx_3(
        s,
        BxArg(1, 2, 0, 0, 21),
        BxArg(4, 3, 0, 0, 10),
        BxArg(2, 4, 0, 1, 7),
    );

    let ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 1];
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

#[inline(always)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_1c(s: &mut KeccakState) {
    let (bx4, bx0, bx1) = bx_3(
        s,
        BxArg(0, 2, 1, 1, 31),
        BxArg(3, 3, 1, 0, 14),
        BxArg(1, 4, 0, 0, 10),
    );
    let (bx2, bx3) = bx_2(s, BxArg(4, 0, 1, 1, 2), BxArg(2, 1, 1, 1, 23));
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

#[inline(always)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_1d(s: &mut KeccakState) {
    let (bx4, bx0, bx1) = bx_3(
        s,
        BxArg(0, 2, 0, 0, 30),
        BxArg(3, 3, 0, 1, 14),
        BxArg(1, 4, 1, 1, 10),
    );
    let (bx2, bx3) = bx_2(s, BxArg(4, 0, 0, 0, 1), BxArg(2, 1, 0, 0, 22));
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

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
#[hax_lib::requires(BASE_ROUND < 254)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round1_pi_rho_chi_1a::<BASE_ROUND>(s);
    keccakf1600_round1_pi_rho_chi_1b::<BASE_ROUND>(s);
    keccakf1600_round1_pi_rho_chi_1c(s);
    keccakf1600_round1_pi_rho_chi_1d(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_2a(s: &mut KeccakState) {
    let (bx4, bx0) = bx_2(s, BxArg(3, 0, 1, 0, 9), BxArg(1, 1, 1, 1, 1));
    let (bx1, bx2, bx3) = bx_3(
        s,
        BxArg(4, 2, 1, 0, 3),
        BxArg(2, 3, 0, 1, 13),
        BxArg(0, 4, 1, 0, 4),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_2b(s: &mut KeccakState) {
    let (bx4, bx0) = bx_2(s, BxArg(3, 0, 0, 1, 9), BxArg(1, 1, 0, 0, 0));
    let (bx1, bx2, bx3) = bx_3(
        s,
        BxArg(4, 2, 0, 1, 3),
        BxArg(2, 3, 1, 0, 12),
        BxArg(0, 4, 0, 1, 4),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_2c(s: &mut KeccakState) {
    let (bx1, bx2) = bx_2(s, BxArg(2, 0, 1, 0, 18), BxArg(0, 1, 1, 0, 5));
    let (bx3, bx4, bx0) = bx_3(
        s,
        BxArg(3, 2, 0, 1, 8),
        BxArg(1, 3, 1, 0, 28),
        BxArg(4, 4, 1, 1, 14),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_2d(s: &mut KeccakState) {
    let (bx1, bx2) = bx_2(s, BxArg(2, 0, 0, 1, 18), BxArg(0, 1, 0, 1, 5));
    let (bx3, bx4, bx0) = bx_3(
        s,
        BxArg(3, 2, 1, 0, 7),
        BxArg(1, 3, 0, 1, 28),
        BxArg(4, 4, 0, 0, 13),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_2e(s: &mut KeccakState) {
    let (bx0, bx1, bx2) = bx_3(
        s,
        BxArg(2, 2, 1, 0, 31),
        BxArg(0, 3, 1, 1, 28),
        BxArg(3, 4, 1, 1, 20),
    );
    let (bx3, bx4) = bx_2(s, BxArg(1, 0, 1, 1, 21), BxArg(4, 1, 0, 0, 1));
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

#[inline(always)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_2f(s: &mut KeccakState) {
    let (bx0, bx1, bx2) = bx_3(
        s,
        BxArg(2, 2, 0, 1, 31),
        BxArg(0, 3, 0, 0, 27),
        BxArg(3, 4, 0, 0, 19),
    );
    let (bx3, bx4) = bx_2(s, BxArg(1, 0, 0, 0, 20), BxArg(4, 1, 1, 1, 1));
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

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1500 in")
)]
pub(crate) fn keccakf1600_round1_pi_rho_chi_2(s: &mut KeccakState) {
    keccakf1600_round1_pi_rho_chi_2a(s);
    keccakf1600_round1_pi_rho_chi_2b(s);
    keccakf1600_round1_pi_rho_chi_2c(s);
    keccakf1600_round1_pi_rho_chi_2d(s);
    keccakf1600_round1_pi_rho_chi_2e(s);
    keccakf1600_round1_pi_rho_chi_2f(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x0_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 0);
    let ax_4 = s.get_with_zeta(4, 0, 1);
    let ax_3 = s.get_with_zeta(3, 0, 1);
    let ax_2 = s.get_with_zeta(2, 0, 1);
    let ax_1 = s.get_with_zeta(1, 0, 1);
    s.set_lane_value(0, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x0_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 1);
    let ax_4 = s.get_with_zeta(4, 0, 0);
    let ax_3 = s.get_with_zeta(3, 0, 0);
    let ax_2 = s.get_with_zeta(2, 0, 0);
    let ax_1 = s.get_with_zeta(1, 0, 0);
    s.set_lane_value(0, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x1_z0(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 1, 1);
    let ax_2 = s.get_with_zeta(2, 1, 1);
    let ax_1 = s.get_with_zeta(1, 1, 1);
    let ax_0 = s.get_with_zeta(0, 1, 1);
    let ax_4 = s.get_with_zeta(4, 1, 0);
    s.set_lane_value(1, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x1_z1(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 1, 0);
    let ax_2 = s.get_with_zeta(2, 1, 0);
    let ax_1 = s.get_with_zeta(1, 1, 0);
    let ax_0 = s.get_with_zeta(0, 1, 0);
    let ax_4 = s.get_with_zeta(4, 1, 1);
    s.set_lane_value(1, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x2_z0(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 2, 1);
    let ax_0 = s.get_with_zeta(0, 2, 1);
    let ax_4 = s.get_with_zeta(4, 2, 1);
    let ax_3 = s.get_with_zeta(3, 2, 0);
    let ax_2 = s.get_with_zeta(2, 2, 1);
    s.set_lane_value(2, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x2_z1(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 2, 0);
    let ax_0 = s.get_with_zeta(0, 2, 0);
    let ax_4 = s.get_with_zeta(4, 2, 0);
    let ax_3 = s.get_with_zeta(3, 2, 1);
    let ax_2 = s.get_with_zeta(2, 2, 0);
    s.set_lane_value(2, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x3_z0(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 3, 1);
    let ax_3 = s.get_with_zeta(3, 3, 1);
    let ax_2 = s.get_with_zeta(2, 3, 0);
    let ax_1 = s.get_with_zeta(1, 3, 1);
    let ax_0 = s.get_with_zeta(0, 3, 1);
    s.set_lane_value(3, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x3_z1(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 3, 0);
    let ax_3 = s.get_with_zeta(3, 3, 0);
    let ax_2 = s.get_with_zeta(2, 3, 1);
    let ax_1 = s.get_with_zeta(1, 3, 0);
    let ax_0 = s.get_with_zeta(0, 3, 0);
    s.set_lane_value(3, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x4_z0(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 4, 1);
    let ax_1 = s.get_with_zeta(1, 4, 0);
    let ax_0 = s.get_with_zeta(0, 4, 1);
    let ax_4 = s.get_with_zeta(4, 4, 1);
    let ax_3 = s.get_with_zeta(3, 4, 1);
    s.set_lane_value(4, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_c_x4_z1(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 4, 0);
    let ax_1 = s.get_with_zeta(1, 4, 1);
    let ax_0 = s.get_with_zeta(0, 4, 0);
    let ax_4 = s.get_with_zeta(4, 4, 0);
    let ax_3 = s.get_with_zeta(3, 4, 0);
    s.set_lane_value(4, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_d_x0(s: &mut KeccakState) {
    let c_x4_zeta0 = s.c[4][0];
    let c_x1_zeta1 = s.c[1][1];
    let c_x4_zeta1 = s.c[4][1];
    let c_x1_zeta0 = s.c[1][0];
    s.d[0].0[0] = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
    s.d[0].0[1] = c_x4_zeta1 ^ c_x1_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_d_x1(s: &mut KeccakState) {
    let c_x0_zeta0 = s.c[0][0];
    let c_x2_zeta1 = s.c[2][1];
    let c_x0_zeta1 = s.c[0][1];
    let c_x2_zeta0 = s.c[2][0];
    s.d[1].0[0] = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
    s.d[1].0[1] = c_x0_zeta1 ^ c_x2_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_d_x2(s: &mut KeccakState) {
    let c_x1_zeta0 = s.c[1][0];
    let c_x3_zeta1 = s.c[3][1];
    let c_x1_zeta1 = s.c[1][1];
    let c_x3_zeta0 = s.c[3][0];
    s.d[2].0[0] = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
    s.d[2].0[1] = c_x1_zeta1 ^ c_x3_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_d_x3(s: &mut KeccakState) {
    let c_x2_zeta0 = s.c[2][0];
    let c_x4_zeta1 = s.c[4][1];
    let c_x2_zeta1 = s.c[2][1];
    let c_x4_zeta0 = s.c[4][0];
    s.d[3].0[0] = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
    s.d[3].0[1] = c_x2_zeta1 ^ c_x4_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_d_x4(s: &mut KeccakState) {
    let c_x3_zeta0 = s.c[3][0];
    let c_x0_zeta1 = s.c[0][1];
    let c_x3_zeta1 = s.c[3][1];
    let c_x0_zeta0 = s.c[0][0];
    s.d[4].0[0] = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
    s.d[4].0[1] = c_x3_zeta1 ^ c_x0_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta_d(s: &mut KeccakState) {
    keccakf1600_round2_theta_d_x0(s);
    keccakf1600_round2_theta_d_x1(s);
    keccakf1600_round2_theta_d_x2(s);
    keccakf1600_round2_theta_d_x3(s);
    keccakf1600_round2_theta_d_x4(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_theta(s: &mut KeccakState) {
    keccakf1600_round2_theta_c_x0_z0(s);
    keccakf1600_round2_theta_c_x0_z1(s);
    keccakf1600_round2_theta_c_x1_z0(s);
    keccakf1600_round2_theta_c_x1_z1(s);
    keccakf1600_round2_theta_c_x2_z0(s);
    keccakf1600_round2_theta_c_x2_z1(s);
    keccakf1600_round2_theta_c_x3_z0(s);
    keccakf1600_round2_theta_c_x3_z1(s);
    keccakf1600_round2_theta_c_x4_z0(s);
    keccakf1600_round2_theta_c_x4_z1(s);
    keccakf1600_round2_theta_d(s);
}

#[inline(always)]
#[hax_lib::requires(BASE_ROUND < 253)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_1a<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = bx_2(s, BxArg(0, 0, 0, 0, 0), BxArg(2, 1, 1, 0, 22));
    let (bx2, bx3, bx4) = bx_3(
        s,
        BxArg(4, 2, 0, 1, 22),
        BxArg(1, 3, 0, 1, 11),
        BxArg(3, 4, 1, 0, 7),
    );

    let ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 2];

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

#[inline(always)]
#[hax_lib::requires(BASE_ROUND < 253)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_1b<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = bx_2(s, BxArg(0, 0, 1, 1, 0), BxArg(2, 1, 0, 1, 22));
    let (bx2, bx3, bx4) = bx_3(
        s,
        BxArg(4, 2, 1, 0, 21),
        BxArg(1, 3, 1, 0, 10),
        BxArg(3, 4, 0, 1, 7),
    );

    let ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 2];
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

#[inline(always)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_1c(s: &mut KeccakState) {
    let (bx4, bx0, bx1) = bx_3(
        s,
        BxArg(2, 2, 0, 1, 31),
        BxArg(4, 3, 1, 0, 14),
        BxArg(1, 4, 0, 0, 10),
    );
    let (bx2, bx3) = bx_2(s, BxArg(3, 0, 0, 1, 2), BxArg(0, 1, 0, 1, 23));
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

#[inline(always)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_1d(s: &mut KeccakState) {
    let (bx4, bx0, bx1) = bx_3(
        s,
        BxArg(2, 2, 1, 0, 30),
        BxArg(4, 3, 0, 1, 14),
        BxArg(1, 4, 1, 1, 10),
    );
    let (bx2, bx3) = bx_2(s, BxArg(3, 0, 1, 0, 1), BxArg(0, 1, 1, 0, 22));
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

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
#[hax_lib::requires(BASE_ROUND < 253)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round2_pi_rho_chi_1a::<BASE_ROUND>(s);
    keccakf1600_round2_pi_rho_chi_1b::<BASE_ROUND>(s);
    keccakf1600_round2_pi_rho_chi_1c(s);
    keccakf1600_round2_pi_rho_chi_1d(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_2a(s: &mut KeccakState) {
    let (bx4, bx0) = bx_2(s, BxArg(1, 0, 1, 0, 9), BxArg(3, 1, 0, 1, 1));
    let (bx1, bx2, bx3) = bx_3(
        s,
        BxArg(0, 2, 1, 0, 3),
        BxArg(2, 3, 1, 1, 13),
        BxArg(4, 4, 1, 0, 4),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_2b(s: &mut KeccakState) {
    let (bx4, bx0) = bx_2(s, BxArg(1, 0, 0, 1, 9), BxArg(3, 1, 1, 0, 0));
    let (bx1, bx2, bx3) = bx_3(
        s,
        BxArg(0, 2, 0, 1, 3),
        BxArg(2, 3, 0, 0, 12),
        BxArg(4, 4, 0, 1, 4),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_2c(s: &mut KeccakState) {
    let (bx1, bx2) = bx_2(s, BxArg(4, 0, 1, 0, 18), BxArg(1, 1, 1, 0, 5));
    let (bx3, bx4, bx0) = bx_3(
        s,
        BxArg(3, 2, 1, 1, 8),
        BxArg(0, 3, 1, 0, 28),
        BxArg(2, 4, 0, 1, 14),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_2d(s: &mut KeccakState) {
    let (bx1, bx2) = bx_2(s, BxArg(4, 0, 0, 1, 18), BxArg(1, 1, 0, 1, 5));
    let (bx3, bx4, bx0) = bx_3(
        s,
        BxArg(3, 2, 0, 0, 7),
        BxArg(0, 3, 0, 1, 28),
        BxArg(2, 4, 1, 0, 13),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_2e(s: &mut KeccakState) {
    let (bx0, bx1, bx2) = bx_3(
        s,
        BxArg(1, 2, 1, 0, 31),
        BxArg(3, 3, 0, 1, 28),
        BxArg(0, 4, 0, 1, 20),
    );
    let (bx3, bx4) = bx_2(s, BxArg(2, 0, 0, 1, 21), BxArg(4, 1, 0, 0, 1));
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

#[inline(always)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_2f(s: &mut KeccakState) {
    let (bx0, bx1, bx2) = bx_3(
        s,
        BxArg(1, 2, 0, 1, 31),
        BxArg(3, 3, 1, 0, 27),
        BxArg(0, 4, 1, 0, 19),
    );
    let (bx3, bx4) = bx_2(s, BxArg(2, 0, 1, 0, 20), BxArg(4, 1, 1, 1, 1));
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

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1500 in")
)]
pub(crate) fn keccakf1600_round2_pi_rho_chi_2(s: &mut KeccakState) {
    keccakf1600_round2_pi_rho_chi_2a(s);
    keccakf1600_round2_pi_rho_chi_2b(s);
    keccakf1600_round2_pi_rho_chi_2c(s);
    keccakf1600_round2_pi_rho_chi_2d(s);
    keccakf1600_round2_pi_rho_chi_2e(s);
    keccakf1600_round2_pi_rho_chi_2f(s);
}

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
pub(crate) fn keccakf1600_round3_theta_c_x0_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 0);
    let ax_3 = s.get_with_zeta(3, 0, 0);
    let ax_1 = s.get_with_zeta(1, 0, 1);
    let ax_4 = s.get_with_zeta(4, 0, 1);
    let ax_2 = s.get_with_zeta(2, 0, 0);
    s.set_lane_value(0, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_c_x0_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 1);
    let ax_3 = s.get_with_zeta(3, 0, 1);
    let ax_1 = s.get_with_zeta(1, 0, 0);
    let ax_4 = s.get_with_zeta(4, 0, 0);
    let ax_2 = s.get_with_zeta(2, 0, 1);
    s.set_lane_value(0, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_c_x1_z0(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 1, 1);
    let ax_0 = s.get_with_zeta(0, 1, 0);
    let ax_3 = s.get_with_zeta(3, 1, 0);
    let ax_1 = s.get_with_zeta(1, 1, 1);
    let ax_4 = s.get_with_zeta(4, 1, 0);
    s.set_lane_value(1, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_c_x1_z1(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 1, 0);
    let ax_0 = s.get_with_zeta(0, 1, 1);
    let ax_3 = s.get_with_zeta(3, 1, 1);
    let ax_1 = s.get_with_zeta(1, 1, 0);
    let ax_4 = s.get_with_zeta(4, 1, 1);
    s.set_lane_value(1, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_c_x2_z0(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 2, 0);
    let ax_2 = s.get_with_zeta(2, 2, 0);
    let ax_0 = s.get_with_zeta(0, 2, 1);
    let ax_3 = s.get_with_zeta(3, 2, 1);
    let ax_1 = s.get_with_zeta(1, 2, 1);
    s.set_lane_value(2, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_c_x2_z1(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 2, 1);
    let ax_2 = s.get_with_zeta(2, 2, 1);
    let ax_0 = s.get_with_zeta(0, 2, 0);
    let ax_3 = s.get_with_zeta(3, 2, 0);
    let ax_1 = s.get_with_zeta(1, 2, 0);
    s.set_lane_value(2, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_c_x3_z0(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 3, 0);
    let ax_4 = s.get_with_zeta(4, 3, 1);
    let ax_2 = s.get_with_zeta(2, 3, 1);
    let ax_0 = s.get_with_zeta(0, 3, 1);
    let ax_3 = s.get_with_zeta(3, 3, 0);
    s.set_lane_value(3, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_c_x3_z1(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 3, 1);
    let ax_4 = s.get_with_zeta(4, 3, 0);
    let ax_2 = s.get_with_zeta(2, 3, 0);
    let ax_0 = s.get_with_zeta(0, 3, 0);
    let ax_3 = s.get_with_zeta(3, 3, 1);
    s.set_lane_value(3, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_c_x4_z0(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 4, 1);
    let ax_1 = s.get_with_zeta(1, 4, 0);
    let ax_4 = s.get_with_zeta(4, 4, 1);
    let ax_2 = s.get_with_zeta(2, 4, 0);
    let ax_0 = s.get_with_zeta(0, 4, 0);
    s.set_lane_value(4, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_c_x4_z1(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 4, 0);
    let ax_1 = s.get_with_zeta(1, 4, 1);
    let ax_4 = s.get_with_zeta(4, 4, 0);
    let ax_2 = s.get_with_zeta(2, 4, 1);
    let ax_0 = s.get_with_zeta(0, 4, 1);
    s.set_lane_value(4, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_d_x0(s: &mut KeccakState) {
    let c_x4_zeta0 = s.c[4][0];
    let c_x1_zeta1 = s.c[1][1];
    let c_x4_zeta1 = s.c[4][1];
    let c_x1_zeta0 = s.c[1][0];
    s.d[0].0[0] = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
    s.d[0].0[1] = c_x4_zeta1 ^ c_x1_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_d_x1(s: &mut KeccakState) {
    let c_x0_zeta0 = s.c[0][0];
    let c_x2_zeta1 = s.c[2][1];
    let c_x0_zeta1 = s.c[0][1];
    let c_x2_zeta0 = s.c[2][0];
    s.d[1].0[0] = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
    s.d[1].0[1] = c_x0_zeta1 ^ c_x2_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_d_x2(s: &mut KeccakState) {
    let c_x1_zeta0 = s.c[1][0];
    let c_x3_zeta1 = s.c[3][1];
    let c_x1_zeta1 = s.c[1][1];
    let c_x3_zeta0 = s.c[3][0];
    s.d[2].0[0] = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
    s.d[2].0[1] = c_x1_zeta1 ^ c_x3_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_d_x3(s: &mut KeccakState) {
    let c_x2_zeta0 = s.c[2][0];
    let c_x4_zeta1 = s.c[4][1];
    let c_x2_zeta1 = s.c[2][1];
    let c_x4_zeta0 = s.c[4][0];
    s.d[3].0[0] = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
    s.d[3].0[1] = c_x2_zeta1 ^ c_x4_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_d_x4(s: &mut KeccakState) {
    let c_x3_zeta0 = s.c[3][0];
    let c_x0_zeta1 = s.c[0][1];
    let c_x3_zeta1 = s.c[3][1];
    let c_x0_zeta0 = s.c[0][0];
    s.d[4].0[0] = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
    s.d[4].0[1] = c_x3_zeta1 ^ c_x0_zeta0;
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta_d(s: &mut KeccakState) {
    keccakf1600_round3_theta_d_x0(s);
    keccakf1600_round3_theta_d_x1(s);
    keccakf1600_round3_theta_d_x2(s);
    keccakf1600_round3_theta_d_x3(s);
    keccakf1600_round3_theta_d_x4(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_theta(s: &mut KeccakState) {
    keccakf1600_round3_theta_c_x0_z0(s);
    keccakf1600_round3_theta_c_x0_z1(s);
    keccakf1600_round3_theta_c_x1_z0(s);
    keccakf1600_round3_theta_c_x1_z1(s);
    keccakf1600_round3_theta_c_x2_z0(s);
    keccakf1600_round3_theta_c_x2_z1(s);
    keccakf1600_round3_theta_c_x3_z0(s);
    keccakf1600_round3_theta_c_x3_z1(s);
    keccakf1600_round3_theta_c_x4_z0(s);
    keccakf1600_round3_theta_c_x4_z1(s);
    keccakf1600_round3_theta_d(s);
}

#[inline(always)]
#[hax_lib::requires(BASE_ROUND < 252)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_1a<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = bx_2(s, BxArg(0, 0, 0, 0, 0), BxArg(0, 1, 0, 0, 22));
    let (bx2, bx3, bx4) = bx_3(
        s,
        BxArg(0, 2, 0, 1, 22),
        BxArg(0, 3, 0, 1, 11),
        BxArg(0, 4, 0, 0, 7),
    );

    let ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 3];
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

#[inline(always)]
#[hax_lib::requires(BASE_ROUND < 252)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_1b<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = bx_2(s, BxArg(0, 0, 1, 1, 0), BxArg(0, 1, 1, 1, 22));
    let (bx2, bx3, bx4) = bx_3(
        s,
        BxArg(0, 2, 1, 0, 21),
        BxArg(0, 3, 1, 0, 10),
        BxArg(0, 4, 1, 1, 7),
    );

    let ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 3];
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

#[inline(always)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_1c(s: &mut KeccakState) {
    let (bx4, bx0, bx1) = bx_3(
        s,
        BxArg(1, 2, 0, 1, 31),
        BxArg(1, 3, 0, 0, 14),
        BxArg(1, 4, 0, 0, 10),
    );
    let (bx2, bx3) = bx_2(s, BxArg(1, 0, 0, 1, 2), BxArg(1, 1, 0, 1, 23));
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

#[inline(always)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_1d(s: &mut KeccakState) {
    let (bx4, bx0, bx1) = bx_3(
        s,
        BxArg(1, 2, 1, 0, 30),
        BxArg(1, 3, 1, 1, 14),
        BxArg(1, 4, 1, 1, 10),
    );
    let (bx2, bx3) = bx_2(s, BxArg(1, 0, 1, 0, 1), BxArg(1, 1, 1, 0, 22));
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

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
#[hax_lib::requires(BASE_ROUND < 252)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round3_pi_rho_chi_1a::<BASE_ROUND>(s);
    keccakf1600_round3_pi_rho_chi_1b::<BASE_ROUND>(s);
    keccakf1600_round3_pi_rho_chi_1c(s);
    keccakf1600_round3_pi_rho_chi_1d(s);
}

#[inline(always)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_2a(s: &mut KeccakState) {
    let (bx4, bx0) = bx_2(s, BxArg(2, 0, 0, 0, 9), BxArg(2, 1, 0, 1, 1));
    let (bx1, bx2, bx3) = bx_3(
        s,
        BxArg(2, 2, 0, 0, 3),
        BxArg(2, 3, 0, 1, 13),
        BxArg(2, 4, 0, 0, 4),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_2b(s: &mut KeccakState) {
    let (bx4, bx0) = bx_2(s, BxArg(2, 0, 1, 1, 9), BxArg(2, 1, 1, 0, 0));
    let (bx1, bx2, bx3) = bx_3(
        s,
        BxArg(2, 2, 1, 1, 3),
        BxArg(2, 3, 1, 0, 12),
        BxArg(2, 4, 1, 1, 4),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_2c(s: &mut KeccakState) {
    let (bx1, bx2) = bx_2(s, BxArg(3, 0, 0, 0, 18), BxArg(3, 1, 0, 0, 5));
    let (bx3, bx4, bx0) = bx_3(
        s,
        BxArg(3, 2, 0, 1, 8),
        BxArg(3, 3, 0, 0, 28),
        BxArg(3, 4, 0, 1, 14),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_2d(s: &mut KeccakState) {
    let (bx1, bx2) = bx_2(s, BxArg(3, 0, 1, 1, 18), BxArg(3, 1, 1, 1, 5));
    let (bx3, bx4, bx0) = bx_3(
        s,
        BxArg(3, 2, 1, 0, 7),
        BxArg(3, 3, 1, 1, 28),
        BxArg(3, 4, 1, 0, 13),
    );
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

#[inline(always)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_2e(s: &mut KeccakState) {
    let (bx0, bx1, bx2) = bx_3(
        s,
        BxArg(4, 2, 0, 0, 31),
        BxArg(4, 3, 0, 1, 28),
        BxArg(4, 4, 0, 1, 20),
    );
    let (bx3, bx4) = bx_2(s, BxArg(4, 0, 0, 1, 21), BxArg(4, 1, 0, 0, 1));
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

#[inline(always)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_2f(s: &mut KeccakState) {
    let (bx0, bx1, bx2) = bx_3(
        s,
        BxArg(4, 2, 1, 1, 31),
        BxArg(4, 3, 1, 0, 27),
        BxArg(4, 4, 1, 0, 19),
    );
    let (bx3, bx4) = bx_2(s, BxArg(4, 0, 1, 0, 20), BxArg(4, 1, 1, 1, 1));
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

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1500 in")
)]
pub(crate) fn keccakf1600_round3_pi_rho_chi_2(s: &mut KeccakState) {
    keccakf1600_round3_pi_rho_chi_2a(s);
    keccakf1600_round3_pi_rho_chi_2b(s);
    keccakf1600_round3_pi_rho_chi_2c(s);
    keccakf1600_round3_pi_rho_chi_2d(s);
    keccakf1600_round3_pi_rho_chi_2e(s);
    keccakf1600_round3_pi_rho_chi_2f(s);
}

// What is interesting is that I assumed that not inlining here should be relatively cheap, because
// it's just 6 calls more per permutation, but commenting out the inline here gives a 10%
// performance hit, e.g.
//   [CYCLE_MEASUREMENT libcrux SHAKE256 (PRF_ETA1_RANDOMNESS_1024)] : + 21535 cycles
// vs
//   [CYCLE_MEASUREMENT libcrux SHAKE256 (PRF_ETA1_RANDOMNESS_1024)] : + 19139 cycles
#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 60")]
#[hax_lib::requires(BASE_ROUND < 21)]
// #[hax_lib::requires(
//     BASE_ROUND == 0 || BASE_ROUND == 4 || BASE_ROUND == 8 || BASE_ROUND == 12||
//     BASE_ROUND == 16 || BASE_ROUND == 20
// )]
pub(crate) fn keccakf1600_4rounds<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round0::<BASE_ROUND>(s);
    keccakf1600_round1::<BASE_ROUND>(s);
    keccakf1600_round2::<BASE_ROUND>(s);
    keccakf1600_round3::<BASE_ROUND>(s);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 60")]
#[hax_lib::requires(BASE_ROUND < 255)]
pub(crate) fn keccakf1600_round0<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round0_theta(s);
    keccakf1600_round0_pi_rho_chi_1::<BASE_ROUND>(s);
    keccakf1600_round0_pi_rho_chi_2(s);
}

#[inline(always)]
// #[hax_lib::fstar::options("--z3rlimit 60")]
#[hax_lib::requires(BASE_ROUND < 254)]
pub(crate) fn keccakf1600_round1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round1_theta(s);
    keccakf1600_round1_pi_rho_chi_1::<BASE_ROUND>(s);
    keccakf1600_round1_pi_rho_chi_2(s);
}

#[inline(always)]
// #[hax_lib::fstar::options("--z3rlimit 60")]
#[hax_lib::requires(BASE_ROUND < 253)]
pub(crate) fn keccakf1600_round2<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round2_theta(s);
    keccakf1600_round2_pi_rho_chi_1::<BASE_ROUND>(s);
    keccakf1600_round2_pi_rho_chi_2(s);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 60")]
#[hax_lib::requires(BASE_ROUND < 252)]
pub(crate) fn keccakf1600_round3<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round3_theta(s);
    keccakf1600_round3_pi_rho_chi_1::<BASE_ROUND>(s);
    keccakf1600_round3_pi_rho_chi_2(s);
}

#[inline(never)]
#[hax_lib::fstar::options("--z3rlimit 60")]
pub(crate) fn keccakf1600(s: &mut KeccakState) {
    keccakf1600_4rounds0(s);
    keccakf1600_4rounds4(s);
    keccakf1600_4rounds8(s);
    keccakf1600_4rounds12(s);
    keccakf1600_4rounds16(s);
    keccakf1600_4rounds20(s);
}

#[inline(always)]
fn keccakf1600_4rounds0(s: &mut KeccakState) {
    keccakf1600_4rounds::<0>(s)
}

#[inline(always)]
fn keccakf1600_4rounds4(s: &mut KeccakState) {
    keccakf1600_4rounds::<4>(s)
}

#[inline(always)]
fn keccakf1600_4rounds8(s: &mut KeccakState) {
    keccakf1600_4rounds::<8>(s)
}

#[inline(always)]
fn keccakf1600_4rounds12(s: &mut KeccakState) {
    keccakf1600_4rounds::<12>(s)
}

#[inline(always)]
fn keccakf1600_4rounds16(s: &mut KeccakState) {
    keccakf1600_4rounds::<16>(s)
}

#[inline(always)]
fn keccakf1600_4rounds20(s: &mut KeccakState) {
    keccakf1600_4rounds::<20>(s)
}

#[inline(always)]
#[hax_lib::requires(
    RATE % 8 == 0
    && RATE <= 168
    && start.to_int() + RATE.to_int() <= blocks.len().to_int()
)]
pub(crate) fn absorb_block<const RATE: usize>(s: &mut KeccakState, blocks: &[U8], start: usize) {
    s.load_block::<RATE>(blocks, start);
    keccakf1600(s)
}

#[inline(always)]
#[hax_lib::requires(
    RATE > 0
    && RATE % 8 == 0
    && RATE <= 168
    && len < RATE
    && start.to_int() + len.to_int() <= last.len().to_int()
)]
pub(crate) fn absorb_final<const RATE: usize, const DELIM: u8>(
    s: &mut KeccakState,
    last: &[U8],
    start: usize,
    len: usize,
) {
    #[cfg(not(eurydice))]
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
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && RATE <= out.len())]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn squeeze_first_block<const RATE: usize>(s: &KeccakState, out: &mut [U8]) {
    s.store_block::<RATE>(out)
}

#[inline(always)]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && RATE <= out.len())]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn squeeze_next_block<const RATE: usize>(s: &mut KeccakState, out: &mut [U8]) {
    keccakf1600(s);
    s.store_block::<RATE>(out)
}

#[inline(always)]
#[cfg(feature = "unbuffered-xof")]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && 3 * RATE <= out.len())]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(s: &mut KeccakState, out: &mut [U8]) {
    squeeze_first_block::<RATE>(s, out);
    squeeze_next_block::<RATE>(s, &mut out[RATE..]);
    squeeze_next_block::<RATE>(s, &mut out[2 * RATE..]);
}

#[inline(always)]
#[cfg(feature = "unbuffered-xof")]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && 5 * RATE <= out.len())]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(s: &mut KeccakState, out: &mut [U8]) {
    squeeze_first_block::<RATE>(s, out);
    squeeze_next_block::<RATE>(s, &mut out[RATE..]);
    squeeze_next_block::<RATE>(s, &mut out[2 * RATE..]);
    squeeze_next_block::<RATE>(s, &mut out[3 * RATE..]);
    squeeze_next_block::<RATE>(s, &mut out[4 * RATE..]);
}

#[inline(always)]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && out.len() <= 200)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn squeeze_last<const RATE: usize>(mut s: KeccakState, out: &mut [U8]) {
    keccakf1600(&mut s);
    let mut b = [0u8; 200].classify();
    s.store_block_full::<RATE>(&mut b);
    out.copy_from_slice(&b[0..out.len()]);
}

#[inline(always)]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && out.len() <= 200)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn squeeze_first_and_last<const RATE: usize>(s: &KeccakState, out: &mut [U8]) {
    let mut b = [0u8; 200].classify();
    s.store_block_full::<RATE>(&mut b);
    out.copy_from_slice(&b[0..out.len()]);
}

// in bytes; this is the 1600 (in bits) in keccak-f[1600]
const WIDTH: usize = 200;

#[inline(always)]
#[hax_lib::requires(
    RATE > 0 && RATE % 8 == 0 && RATE <= 168
)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn keccak<const RATE: usize, const DELIM: u8>(data: &[U8], out: &mut [U8]) {
    let n = data.len() / RATE;
    let rem = data.len() % RATE;

    let outlen = out.len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    let mut s = KeccakState::new();

    let mut start = 0;
    for _i in 0..n {
        hax_lib::loop_invariant!(|_i: usize| { start.to_int() == _i.to_int() * RATE.to_int() });

        absorb_block::<RATE>(&mut s, &data, start);
        start += RATE;
    }

    absorb_final::<RATE, DELIM>(&mut s, data, data.len() - rem, rem);

    if blocks == 0 {
        squeeze_first_and_last::<RATE>(&s, out)
    } else {
        squeeze_first_block::<RATE>(&s, out);
        let mut offset = RATE;
        for _i in 1..blocks {
            hax_lib::loop_invariant!(|_i: usize| {
                out.len() == outlen && offset.to_int() == _i.to_int() * RATE.to_int()
            });
            squeeze_next_block::<RATE>(&mut s, &mut out[offset..]);
            offset += RATE;
        }
        if last < outlen {
            debug_assert_eq!(last, offset);
            squeeze_last::<RATE>(s, &mut out[offset..])
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
