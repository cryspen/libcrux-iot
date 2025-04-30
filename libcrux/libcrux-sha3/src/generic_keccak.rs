//! The generic SHA3 implementation that uses portable or platform specific
//! sub-routines.

use crate::traits::*;

#[cfg_attr(hax, hax_lib::opaque)]
#[derive(Clone, Copy)]
pub(crate) struct KeccakState<const N: usize, T: KeccakStateItem<N>> {
    st: [T; 25],
}

impl<const N: usize, T: KeccakStateItem<N>> KeccakState<N, T> {
    fn get(&self, i: usize, j: usize) -> T {
        get_ij(&self.st, i, j)
    }
    fn set(&mut self, i: usize, j: usize, v: T) {
        set_ij(&mut self.st, i, j, v);
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
pub(crate) struct KeccakXofState<
    const PARALLEL_LANES: usize,
    const RATE: usize,
    STATE: KeccakStateItem<PARALLEL_LANES>,
> {
    inner: KeccakState<PARALLEL_LANES, STATE>,

    // Buffer inputs on absorb.
    buf: [[u8; RATE]; PARALLEL_LANES],

    // Buffered length.
    buf_len: usize,

    // Needs sponge.
    sponge: bool,
}

impl<const PARALLEL_LANES: usize, const RATE: usize, STATE: KeccakStateItem<PARALLEL_LANES>>
    KeccakXofState<PARALLEL_LANES, RATE, STATE>
{
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

const ROUNDCONSTANTS: [u64; 24] = [
    0x0000_0000_0000_0001u64,
    0x0000_0000_0000_8082u64,
    0x8000_0000_0000_808au64,
    0x8000_0000_8000_8000u64,
    0x0000_0000_0000_808bu64,
    0x0000_0000_8000_0001u64,
    0x8000_0000_8000_8081u64,
    0x8000_0000_0000_8009u64,
    0x0000_0000_0000_008au64,
    0x0000_0000_0000_0088u64,
    0x0000_0000_8000_8009u64,
    0x0000_0000_8000_000au64,
    0x0000_0000_8000_808bu64,
    0x8000_0000_0000_008bu64,
    0x8000_0000_0000_8089u64,
    0x8000_0000_0000_8003u64,
    0x8000_0000_0000_8002u64,
    0x8000_0000_0000_0080u64,
    0x0000_0000_0000_800au64,
    0x8000_0000_8000_000au64,
    0x8000_0000_8000_8081u64,
    0x8000_0000_0000_8080u64,
    0x0000_0000_8000_0001u64,
    0x8000_0000_8000_8008u64,
];

/// N^i(x, y) from Alg. 4
macro_rules! ni_y {
    (0, $x:literal, $y: literal) => {
        $y
    };
    (1, $x:literal, $y: literal) => {
        ($x + 2 * $y) % 5
    };
    (2, $x:literal, $y: literal) => {
        (3 * $x + 4 * $y) % 5
    };
    (3, $x:literal, $y: literal) => {
        (2 * $x + 3 * $y) % 5
    };

    (3 + 1, $x:literal, $y: literal) => {
        ni_y!(0, $x, $y)
    };
    (0 + 1, $x:literal, $y: literal) => {
        ni_y!(1, $x, $y)
    };
    (1 + 1, $x:literal, $y: literal) => {
        ni_y!(2, $x, $y)
    };
    (2 + 1, $x:literal, $y: literal) => {
        ni_y!(3, $x, $y)
    };
}

///  This chooses the r[(x, y)] and r[N(x, y)^T] from Alg.4
macro_rules! r {
    (3, 2) => {
        25
    };
    (4, 2) => {
        39
    };
    (0, 2) => {
        3
    };
    (1, 2) => {
        10
    };
    (2, 2) => {
        43
    };

    (3, 1) => {
        55
    };
    (4, 1) => {
        20
    };
    (0, 1) => {
        36
    };
    (1, 1) => {
        44
    };
    (2, 1) => {
        6
    };

    (3, 0) => {
        28
    };
    (4, 0) => {
        27
    };
    (0, 0) => {
        0
    };
    (1, 0) => {
        1
    };
    (2, 0) => {
        62
    };

    (3, 4) => {
        56
    };
    (4, 4) => {
        14
    };
    (0, 4) => {
        18
    };
    (1, 4) => {
        2
    };
    (2, 4) => {
        61
    };

    (3, 3) => {
        21
    };
    (4, 3) => {
        8
    };
    (0, 3) => {
        41
    };
    (1, 3) => {
        45
    };
    (2, 3) => {
        15
    };

    // n(x, y) -> (x, x+2*y mod 5)
    (n(0, 0)) => {
        r!(0, 0)
    };
    (n(0, 1)) => {
        r!(0, 2)
    };
    (n(0, 2)) => {
        r!(0, 4)
    };
    (n(0, 3)) => {
        r!(0, 1)
    };
    (n(0, 4)) => {
        r!(0, 3)
    };

    (n(1, 0)) => {
        r!(1, 1)
    };
    (n(1, 1)) => {
        r!(1, 3)
    };
    (n(1, 2)) => {
        r!(1, 0)
    };
    (n(1, 3)) => {
        r!(1, 2)
    };
    (n(1, 4)) => {
        r!(1, 4)
    };

    (n(2, 0)) => {
        r!(2, 2)
    };
    (n(2, 1)) => {
        r!(2, 4)
    };
    (n(2, 2)) => {
        r!(2, 1)
    };
    (n(2, 3)) => {
        r!(2, 3)
    };
    (n(2, 4)) => {
        r!(2, 0)
    };

    (n(3, 0)) => {
        r!(3, 3)
    };
    (n(3, 1)) => {
        r!(3, 0)
    };
    (n(3, 2)) => {
        r!(3, 2)
    };
    (n(3, 3)) => {
        r!(3, 4)
    };
    (n(3, 4)) => {
        r!(3, 1)
    };

    (n(4, 0)) => {
        r!(4, 4)
    };
    (n(4, 1)) => {
        r!(4, 1)
    };
    (n(4, 2)) => {
        r!(4, 3)
    };
    (n(4, 3)) => {
        r!(4, 0)
    };
    (n(4, 4)) => {
        r!(4, 2)
    };
}

macro_rules! xor_and_rotate {
    ($x:tt, $y:tt, $t:ty) => {
        <$t>::xor_and_rotate::<{ r!(n($x, $y)) }, { 64 - r!(n($x, $y)) }>
    };
}

macro_rules! c_loop {
    ($s:expr, $c:expr, $i:tt) => {
        let t0 = $s.get(ni_y!($i, 0, 0), 0);
        let t1 = $s.get(ni_y!($i, 0, 1), 0);
        let t2 = $s.get(ni_y!($i, 0, 2), 0);
        let t3 = $s.get(ni_y!($i, 0, 3), 0);
        let t4 = $s.get(ni_y!($i, 0, 4), 0);
        $c[0] = T::xor5(t0, t1, t2, t3, t4);

        let t0 = $s.get(ni_y!($i, 1, 0), 1);
        let t1 = $s.get(ni_y!($i, 1, 1), 1);
        let t2 = $s.get(ni_y!($i, 1, 2), 1);
        let t3 = $s.get(ni_y!($i, 1, 3), 1);
        let t4 = $s.get(ni_y!($i, 1, 4), 1);
        $c[1] = T::xor5(t0, t1, t2, t3, t4);

        let t0 = $s.get(ni_y!($i, 2, 0), 2);
        let t1 = $s.get(ni_y!($i, 2, 1), 2);
        let t2 = $s.get(ni_y!($i, 2, 2), 2);
        let t3 = $s.get(ni_y!($i, 2, 3), 2);
        let t4 = $s.get(ni_y!($i, 2, 4), 2);
        $c[2] = T::xor5(t0, t1, t2, t3, t4);

        let t0 = $s.get(ni_y!($i, 3, 0), 3);
        let t1 = $s.get(ni_y!($i, 3, 1), 3);
        let t2 = $s.get(ni_y!($i, 3, 2), 3);
        let t3 = $s.get(ni_y!($i, 3, 3), 3);
        let t4 = $s.get(ni_y!($i, 3, 4), 3);
        $c[3] = T::xor5(t0, t1, t2, t3, t4);

        let t0 = $s.get(ni_y!($i, 4, 0), 4);
        let t1 = $s.get(ni_y!($i, 4, 1), 4);
        let t2 = $s.get(ni_y!($i, 4, 2), 4);
        let t3 = $s.get(ni_y!($i, 4, 3), 4);
        let t4 = $s.get(ni_y!($i, 4, 4), 4);
        $c[4] = T::xor5(t0, t1, t2, t3, t4);
    };
}

macro_rules! b_inner_loop {
    ($s:expr, $b:expr, $d:expr, $i:tt, $y:tt) => {{
        let t0_s = $s.get(ni_y!($i + 1, 0, $y), 0);
        let t0_d = $d[0];
        $b[(0 + 2 * $y) % 5] = xor_and_rotate!(0, $y, T)(t0_s, t0_d);

        let t1_s = $s.get(ni_y!($i + 1, 1, $y), 1);
        let t1_d = $d[1];
        $b[(1 + 2 * $y) % 5] = xor_and_rotate!(1, $y, T)(t1_s, t1_d);

        let t2_s = $s.get(ni_y!($i + 1, 2, $y), 2);
        let t2_d = $d[2];
        $b[(2 + 2 * $y) % 5] = xor_and_rotate!(2, $y, T)(t2_s, t2_d);

        let t3_s = $s.get(ni_y!($i + 1, 3, $y), 3);
        let t3_d = $d[3];
        $b[(3 + 2 * $y) % 5] = xor_and_rotate!(3, $y, T)(t3_s, t3_d);

        let t4_s = $s.get(ni_y!($i + 1, 4, $y), 4);
        let t4_d = $d[4];
        $b[(4 + 2 * $y) % 5] = xor_and_rotate!(4, $y, T)(t4_s, t4_d);
    }};
}

macro_rules! a_loop {
    ($s:expr, $b:expr, $i:tt, $y:tt) => {{
        let b0 = $b[0];
        let b1 = $b[1];
        let b2 = $b[2];
        let b3 = $b[3];
        let b4 = $b[4];

        $s.set(ni_y!($i + 1, 0, $y), 0, T::and_not_xor(b0, b2, b1));
        $s.set(ni_y!($i + 1, 1, $y), 1, T::and_not_xor(b1, b3, b2));
        $s.set(ni_y!($i + 1, 2, $y), 2, T::and_not_xor(b2, b4, b3));
        $s.set(ni_y!($i + 1, 3, $y), 3, T::and_not_xor(b3, b0, b4));
        $s.set(ni_y!($i + 1, 4, $y), 4, T::and_not_xor(b4, b1, b0));
    }};
}

macro_rules! defn_keccak_round {
    ($name:ident, $i:tt) => {
        #[inline(always)]
        fn $name<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>, i: usize) {
            let mut bc = [T::zero(); 5];
            let mut d = [T::zero(); 5];

            c_loop!(s, bc, $i);
            d_loop(&bc, &mut d);

            // for y in 0..5 {
            // y=0
            b_inner_loop!(s, &mut bc, &d, $i, 0);
            a_loop!(s, bc, $i, 0);

            // y=1
            b_inner_loop!(s, &mut bc, &d, $i, 1);
            a_loop!(s, bc, $i, 1);

            // y=2
            b_inner_loop!(s, &mut bc, &d, $i, 2);
            a_loop!(s, bc, $i, 2);

            // y=3
            b_inner_loop!(s, &mut bc, &d, $i, 3);
            a_loop!(s, bc, $i, 3);

            // y=4
            b_inner_loop!(s, &mut bc, &d, $i, 4);
            a_loop!(s, bc, $i, 4);
            // }

            s.set(0, 0, T::xor_constant(s.get(0, 0), ROUNDCONSTANTS[i]));
        }
    };
}

defn_keccak_round!(keccakf1600_round_i0, 0);
defn_keccak_round!(keccakf1600_round_i1, 1);
defn_keccak_round!(keccakf1600_round_i2, 2);
defn_keccak_round!(keccakf1600_round_i3, 3);

#[inline(always)]
fn d_loop<const N: usize, T: KeccakStateItem<N>>(c: &[T; 5], d: &mut [T; 5]) {
    let c0 = c[0];
    let c2 = c[2];
    let c4 = c[4];
    d[1] = T::rotate_left1_and_xor(c0, c2);
    d[3] = T::rotate_left1_and_xor(c2, c4);

    let c1 = c[1];
    let c3 = c[3];

    d[0] = T::rotate_left1_and_xor(c4, c1);
    d[2] = T::rotate_left1_and_xor(c1, c3);
    d[4] = T::rotate_left1_and_xor(c3, c0);
}

#[inline(always)]
pub(crate) fn keccakf1600<const N: usize, T: KeccakStateItem<N>>(s: &mut KeccakState<N, T>) {
    for rd in 0..6 {
        keccakf1600_round_i0::<N, T>(s, rd * 4);
        keccakf1600_round_i1::<N, T>(s, rd * 4 + 1);
        keccakf1600_round_i2::<N, T>(s, rd * 4 + 2);
        keccakf1600_round_i3::<N, T>(s, rd * 4 + 3);
    }
}
#[inline(always)]
pub(crate) fn keccakf1600_4rounds<const N: usize, T: KeccakStateItem<N>>(
    s: &mut KeccakState<N, T>,
) {
    keccakf1600_round_i0::<N, T>(s, 0);
    keccakf1600_round_i1::<N, T>(s, 1);
    keccakf1600_round_i2::<N, T>(s, 2);
    keccakf1600_round_i3::<N, T>(s, 3);
}

#[inline(always)]
pub(crate) fn absorb_block<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &mut KeccakState<N, T>,
    blocks: &[&[u8]; N],
    start: usize,
) {
    T::load_block::<RATE>(&mut s.st, blocks, start);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn absorb_final<
    const N: usize,
    T: KeccakStateItem<N>,
    const RATE: usize,
    const DELIM: u8,
>(
    s: &mut KeccakState<N, T>,
    last: &[&[u8]; N],
    start: usize,
    len: usize,
) {
    debug_assert!(N > 0 && len < RATE); // && last[0].len() < RATE

    let mut blocks = [[0u8; WIDTH]; N];
    for i in 0..N {
        if len > 0 {
            blocks[i][0..len].copy_from_slice(&last[i][start..start + len]);
        }
        blocks[i][len] = DELIM;
        blocks[i][RATE - 1] |= 0x80;
    }
    T::load_block_full::<RATE>(&mut s.st, &blocks, 0);
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn squeeze_first_block<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &KeccakState<N, T>,
    out: &mut [&mut [u8]; N],
) {
    T::store_block::<RATE>(&s.st, out)
}

#[inline(always)]
pub(crate) fn squeeze_next_block<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &mut KeccakState<N, T>,
    out: &mut [&mut [u8]; N],
) {
    keccakf1600(s);
    T::store_block::<RATE>(&s.st, out)
}

#[inline(always)]
pub(crate) fn squeeze_first_three_blocks<
    const N: usize,
    T: KeccakStateItem<N>,
    const RATE: usize,
>(
    s: &mut KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    let (mut o0, o1) = T::split_at_mut_n(out, RATE);
    squeeze_first_block::<N, T, RATE>(s, &mut o0);
    let (mut o1, mut o2) = T::split_at_mut_n(o1, RATE);
    squeeze_next_block::<N, T, RATE>(s, &mut o1);
    squeeze_next_block::<N, T, RATE>(s, &mut o2);
}

#[inline(always)]
pub(crate) fn squeeze_first_five_blocks<
    const N: usize,
    T: KeccakStateItem<N>,
    const RATE: usize,
>(
    s: &mut KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    let (mut o0, o1) = T::split_at_mut_n(out, RATE);
    squeeze_first_block::<N, T, RATE>(s, &mut o0);
    let (mut o1, o2) = T::split_at_mut_n(o1, RATE);

    squeeze_next_block::<N, T, RATE>(s, &mut o1);
    let (mut o2, o3) = T::split_at_mut_n(o2, RATE);

    squeeze_next_block::<N, T, RATE>(s, &mut o2);
    let (mut o3, mut o4) = T::split_at_mut_n(o3, RATE);

    squeeze_next_block::<N, T, RATE>(s, &mut o3);
    squeeze_next_block::<N, T, RATE>(s, &mut o4);
}

#[inline(always)]
pub(crate) fn squeeze_last<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    mut s: KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    keccakf1600(&mut s);
    let mut b = [[0u8; 200]; N];
    T::store_block_full::<RATE>(&s.st, &mut b);
    for i in 0..N {
        out[i].copy_from_slice(&b[i][0..out[i].len()]);
    }
}

#[inline(always)]
pub(crate) fn squeeze_first_and_last<const N: usize, T: KeccakStateItem<N>, const RATE: usize>(
    s: &KeccakState<N, T>,
    out: [&mut [u8]; N],
) {
    let mut b = [[0u8; 200]; N];
    T::store_block_full::<RATE>(&s.st, &mut b);
    for i in 0..N {
        out[i].copy_from_slice(&b[i][0..out[i].len()]);
    }
}

// in bytes; this is the 1600 (in bits) in keccak-f[1600]
const WIDTH: usize = 200;

#[inline(always)]
pub(crate) fn keccak<const N: usize, T: KeccakStateItem<N>, const RATE: usize, const DELIM: u8>(
    data: &[&[u8]; N],
    out: [&mut [u8]; N],
) {
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
    let mut s = KeccakState::<N, T>::new();

    // 6. For i from 0 to n-1,
    for i in 0..n {
        // T::slice_n(data, i * RATE, RATE)

        // 6. (cont.) Let S = f(S XOR (P_i || 0^c))
        absorb_block::<N, T, RATE>(&mut s, &data, i * RATE);
    }

    // Handle remaining data, padding
    let rem = data[0].len() % RATE;
    // T::slice_n(data, data[0].len() - rem, rem)
    absorb_final::<N, T, RATE, DELIM>(&mut s, data, data[0].len() - rem, rem);

    let outlen = out[0].len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    if blocks == 0 {
        squeeze_first_and_last::<N, T, RATE>(&s, out)
    } else {
        let (mut o0, mut o1) = T::split_at_mut_n(out, RATE);
        squeeze_first_block::<N, T, RATE>(&s, &mut o0);
        for _i in 1..blocks {
            let (mut o, orest) = T::split_at_mut_n(o1, RATE);
            squeeze_next_block::<N, T, RATE>(&mut s, &mut o);
            o1 = orest;
        }
        if last < outlen {
            squeeze_last::<N, T, RATE>(s, o1)
        }
    }
}
