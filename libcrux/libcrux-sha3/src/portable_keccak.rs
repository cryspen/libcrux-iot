//! A portable SHA3 implementation using the generic implementation.

use crate::traits::{internal::*, *};

#[inline(always)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: u64) -> u64 {
    debug_assert!(LEFT + RIGHT == 64);
    x.rotate_left(LEFT as u32)
}

#[inline(always)]
fn _veor5q_u64(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {
    a ^ b ^ c ^ d ^ e
}

#[inline(always)]
fn _vrax1q_u64(a: u64, b: u64) -> u64 {
    a ^ rotate_left::<1, 63>(b)
}

#[inline(always)]
fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: u64, b: u64) -> u64 {
    rotate_left::<LEFT, RIGHT>(a ^ b)
}

#[inline(always)]
fn _vbcaxq_u64(a: u64, b: u64, c: u64) -> u64 {
    a ^ (b & !c)
}

#[inline(always)]
fn _veorq_n_u64(a: u64, c: u64) -> u64 {
    a ^ c
}

#[inline(always)]
pub(crate) fn load_block<const RATE: usize>(state: &mut [u64; 25], blocks: &[u8], start: usize) {
    debug_assert!(RATE <= blocks.len() && RATE % 8 == 0);
    let mut state_flat = [0u64; 25];

    let mut offset_a: usize;
    let mut offset_b: usize;
    let mut offset_c: usize;
    let mut offset_d: usize;
    let mut offset_e: usize;
    let mut offset_f: usize;

    /*
     * What a good factor is here depends on several things:
     * - we can't make it too high, because we don't want to waste registers
     * - we want to squeeze in the most consecutive loads we can get, so they pipeline nicely
     * - it's fine if we do something in between the stores - it's not pipelined, but we have to to
     *   the stores at some point.
     * - for some reason this gets slower if we make it longer. My guess is that our register
     *   budget is very limited, because the surrounding code keeps some state in there, and if we
     *   overspend, then some other part of the code has to spill.
     * */
    const UNROLL_FACTOR: usize = 6;

    for i in 0..RATE / 8 / UNROLL_FACTOR {
        let i = UNROLL_FACTOR * i;
        offset_a = start + 8 * (i + 0);
        offset_b = start + 8 * (i + 1);
        offset_c = start + 8 * (i + 2);
        offset_d = start + 8 * (i + 3);
        offset_e = start + 8 * (i + 4);
        offset_f = start + 8 * (i + 5);

        let v_a = blocks[offset_a..offset_a + 8].try_into().unwrap();
        let v_b = blocks[offset_b..offset_b + 8].try_into().unwrap();
        let v_c = blocks[offset_c..offset_c + 8].try_into().unwrap();
        let v_d = blocks[offset_d..offset_d + 8].try_into().unwrap();
        let v_e = blocks[offset_e..offset_e + 8].try_into().unwrap();
        let v_f = blocks[offset_f..offset_f + 8].try_into().unwrap();

        state_flat[i + 0] = u64::from_le_bytes(v_a);
        state_flat[i + 1] = u64::from_le_bytes(v_b);
        state_flat[i + 2] = u64::from_le_bytes(v_c);
        state_flat[i + 3] = u64::from_le_bytes(v_d);
        state_flat[i + 4] = u64::from_le_bytes(v_e);
        state_flat[i + 5] = u64::from_le_bytes(v_f);
    }

    // load remaining blocks
    for i in RATE / 8 / UNROLL_FACTOR..RATE / 8 {
        let offset = start + 8 * i;
        let v = blocks[offset..offset + 8].try_into().unwrap();
        state_flat[i] = u64::from_le_bytes(v);
    }

    // I tried unrolling and pipelining this, but that made things worse
    for i in 0..RATE / 8 {
        {
            let offset = 5 * (i % 5) + (i / 5);
            state[offset] ^= state_flat[i];
        };
    }
}

#[inline(always)]
pub(crate) fn load_block_full<const RATE: usize>(
    state: &mut [u64; 25],
    blocks: &[u8; 200],
    start: usize,
) {
    load_block::<RATE>(state, blocks, start);
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(s: &[u64; 25], out: &mut [u8]) {
    // I tried the unroll-andgroup technhique here, didn't do anything. Tried groups of 5, since
    // that lets us get rid of the divisions as well
    for i in 0..RATE / 8 {
        out[8 * i..8 * i + 8].copy_from_slice(&get_ij(s, i / 5, i % 5).to_le_bytes());
    }
}

#[inline(always)]
pub(crate) fn store_block_full<const RATE: usize>(s: &[u64; 25], out: &mut [u8; 200]) {
    store_block::<RATE>(s, out);
}

#[inline(always)]
fn split_at_mut_1(out: &mut [u8], mid: usize) -> (&mut [u8], &mut [u8]) {
    out.split_at_mut(mid)
}

impl KeccakItem<1> for u64 {
    #[inline(always)]
    fn zero() -> Self {
        0
    }
    #[inline(always)]
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
        _veor5q_u64(a, b, c, d, e)
    }
    #[inline(always)]
    fn rotate_left1_and_xor(a: Self, b: Self) -> Self {
        _vrax1q_u64(a, b)
    }
    #[inline(always)]
    fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self {
        _vxarq_u64::<LEFT, RIGHT>(a, b)
    }
    #[inline(always)]
    fn and_not_xor(a: Self, b: Self, c: Self) -> Self {
        _vbcaxq_u64(a, b, c)
    }
    #[inline(always)]
    fn xor_constant(a: Self, c: u64) -> Self {
        _veorq_n_u64(a, c)
    }
    #[inline(always)]
    fn xor(a: Self, b: Self) -> Self {
        a ^ b
    }
    #[inline(always)]
    fn load_block<const RATE: usize>(state: &mut [Self; 25], blocks: &[&[u8]; 1], start: usize) {
        load_block::<RATE>(state, blocks[0], start)
    }
    #[inline(always)]
    fn store_block<const RATE: usize>(state: &[Self; 25], out: &mut [&mut [u8]; 1]) {
        store_block::<RATE>(state, out[0])
    }
    #[inline(always)]
    fn load_block_full<const RATE: usize>(
        state: &mut [Self; 25],
        blocks: &[[u8; 200]; 1],
        start: usize,
    ) {
        load_block_full::<RATE>(state, &blocks[0], start)
    }
    #[inline(always)]
    fn store_block_full<const RATE: usize>(state: &[Self; 25], out: &mut [[u8; 200]; 1]) {
        store_block_full::<RATE>(state, &mut out[0]);
    }

    #[inline(always)]
    fn split_at_mut_n(a: [&mut [u8]; 1], mid: usize) -> ([&mut [u8]; 1], [&mut [u8]; 1]) {
        let (x, y) = split_at_mut_1(a[0], mid);
        ([x], [y])
    }

    /// `out` has the exact size we want here. It must be less than or equal to `RATE`.
    #[inline(always)]
    fn store<const RATE: usize>(state: &[Self; 25], out: [&mut [u8]; 1]) {
        debug_assert!(out.len() <= RATE / 8, "{} > {}", out.len(), RATE);

        let num_full_blocks = out[0].len() / 8;
        let last_block_len = out[0].len() % 8;

        for i in 0..num_full_blocks {
            out[0][i * 8..i * 8 + 8].copy_from_slice(&get_ij(state, i / 5, i % 5).to_le_bytes());
        }
        if last_block_len != 0 {
            out[0][num_full_blocks * 8..num_full_blocks * 8 + last_block_len].copy_from_slice(
                &get_ij(state, num_full_blocks / 5, num_full_blocks % 5).to_le_bytes()
                    [0..last_block_len],
            );
        }
    }
}
