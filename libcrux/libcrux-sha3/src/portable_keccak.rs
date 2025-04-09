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

fn interleave_lane(lane: Lane2U32) -> Lane2U32 {
    let lane_u64 = lane[0] as u64 | (lane[1] as u64) << 32;
    let mut even_bits = lane_u64 & 0x5555_5555_5555_5555;
    even_bits = (even_bits ^ (even_bits >> 1)) & 0x3333_3333_3333_3333;
    even_bits = (even_bits ^ (even_bits >> 2)) & 0x0f0f_0f0f_0f0f_0f0f;
    even_bits = (even_bits ^ (even_bits >> 4)) & 0x00ff_00ff_00ff_00ff;
    even_bits = (even_bits ^ (even_bits >> 8)) & 0x0000_ffff_0000_ffff;
    even_bits = (even_bits ^ (even_bits >> 16)) & 0x0000_0000_ffff_ffff;

    let mut odd_bits = (lane_u64 >> 1) & 0x5555_5555_5555_5555;
    odd_bits = (odd_bits ^ (odd_bits >> 1)) & 0x3333_3333_3333_3333;
    odd_bits = (odd_bits ^ (odd_bits >> 2)) & 0x0f0f_0f0f_0f0f_0f0f;
    odd_bits = (odd_bits ^ (odd_bits >> 4)) & 0x00ff_00ff_00ff_00ff;
    odd_bits = (odd_bits ^ (odd_bits >> 8)) & 0x0000_ffff_0000_ffff;
    odd_bits = (odd_bits ^ (odd_bits >> 16)) & 0x0000_0000_ffff_ffff;

    [even_bits as u32, odd_bits as u32]
}

fn deinterleave_lane([even_bits, odd_bits]: Lane2U32) -> Lane2U32 {
    let mut even_spaced_lo = even_bits & 0xffff;
    even_spaced_lo = (even_spaced_lo ^ (even_spaced_lo << 16)) & 0x0000_ffff;
    even_spaced_lo = (even_spaced_lo ^ (even_spaced_lo << 8)) & 0x00ff_00ff;
    even_spaced_lo = (even_spaced_lo ^ (even_spaced_lo << 4)) & 0x0f0f_0f0f;
    even_spaced_lo = (even_spaced_lo ^ (even_spaced_lo << 2)) & 0x3333_3333;
    even_spaced_lo = (even_spaced_lo ^ (even_spaced_lo << 1)) & 0x5555_5555;

    let mut even_spaced_hi = even_bits >> 16;
    even_spaced_hi = (even_spaced_hi ^ (even_spaced_hi << 16)) & 0x0000_ffff;
    even_spaced_hi = (even_spaced_hi ^ (even_spaced_hi << 8)) & 0x00ff_00ff;
    even_spaced_hi = (even_spaced_hi ^ (even_spaced_hi << 4)) & 0x0f0f_0f0f;
    even_spaced_hi = (even_spaced_hi ^ (even_spaced_hi << 2)) & 0x3333_3333;
    even_spaced_hi = (even_spaced_hi ^ (even_spaced_hi << 1)) & 0x5555_5555;

    let mut odd_spaced_lo = odd_bits & 0xffff;
    odd_spaced_lo = (odd_spaced_lo ^ (odd_spaced_lo << 16)) & 0x0000_ffff;
    odd_spaced_lo = (odd_spaced_lo ^ (odd_spaced_lo << 8)) & 0x00ff_00ff;
    odd_spaced_lo = (odd_spaced_lo ^ (odd_spaced_lo << 4)) & 0x0f0f_0f0f;
    odd_spaced_lo = (odd_spaced_lo ^ (odd_spaced_lo << 2)) & 0x3333_3333;
    odd_spaced_lo = (odd_spaced_lo ^ (odd_spaced_lo << 1)) & 0x5555_5555;

    let mut odd_spaced_hi = odd_bits >> 16;
    odd_spaced_hi = (odd_spaced_hi ^ (odd_spaced_hi << 16)) & 0x0000_ffff;
    odd_spaced_hi = (odd_spaced_hi ^ (odd_spaced_hi << 8)) & 0x00ff_00ff;
    odd_spaced_hi = (odd_spaced_hi ^ (odd_spaced_hi << 4)) & 0x0f0f_0f0f;
    odd_spaced_hi = (odd_spaced_hi ^ (odd_spaced_hi << 2)) & 0x3333_3333;
    odd_spaced_hi = (odd_spaced_hi ^ (odd_spaced_hi << 1)) & 0x5555_5555;

    [
        even_spaced_lo | (odd_spaced_lo << 1),
        even_spaced_hi | (odd_spaced_hi << 1),
    ]
}

#[cfg(test)]
mod interleave_tests {
    use crate::portable_keccak::{deinterleave_lane, interleave_lane};

    #[test]
    fn identity() {
        let lanes = [[0x800001, 43]];

        for lane in lanes {
            let lane_ = deinterleave_lane(interleave_lane(lane));
            assert_eq!(lane, lane_, "lane_: {lane_:x?}, lane: {lane:x?}")
        }
    }
}

#[inline(always)]
fn shuffle(mut x: u32) -> u32 {
    let mut t: u32;
    t = (x ^ (x >> 8)) & 0x0000FF00;
    x = x ^ t ^ (t << 8);
    t = (x ^ (x >> 4)) & 0x00F000F0;
    x = x ^ t ^ (t << 4);
    t = (x ^ (x >> 2)) & 0x0C0C0C0C;
    x = x ^ t ^ (t << 2);
    t = (x ^ (x >> 1)) & 0x22222222;
    x = x ^ t ^ (t << 1);
    x
}

fn unshuffle(mut x: u32) -> u32 {
    let mut t: u32;
    t = (x ^ (x >> 1)) & 0x22222222;
    x = x ^ t ^ (t << 1);
    t = (x ^ (x >> 2)) & 0x0C0C0C0C;
    x = x ^ t ^ (t << 2);
    t = (x ^ (x >> 4)) & 0x00F000F0;
    x = x ^ t ^ (t << 4);
    t = (x ^ (x >> 8)) & 0x0000FF00;
    x = x ^ t ^ (t << 8);
    x
}

#[inline(always)]
fn shuffle_lane(lane: Lane2U32) -> Lane2U32 {
    let [a, b] = lane;
    let hi = (a & 0xffff0000) | ((b & 0xffff0000) >> 16);
    let lo = ((a & 0x0000ffff) << 16) | (b & 0x0000ffff);
    [shuffle(hi), shuffle(lo)]
}

#[inline(always)]
fn unshuffle_lane(lane: Lane2U32) -> Lane2U32 {
    let (hi, lo) = (unshuffle(lane[0]), unshuffle(lane[1]));
    let a = (hi & 0xffff) | ((lo & 0xffff0000) >> 16);
    let b = ((hi & 0x0000ffff) << 16) | (lo & 0x0000ffff);
    [a, b]
}

#[inline(always)]
pub(crate) fn load_block<const RATE: usize>(state: &mut [u64; 25], blocks: &[u8], start: usize) {
    debug_assert!(RATE <= blocks.len() && RATE % 8 == 0);
    let mut state_flat = [0u64; 25];
    for i in 0..RATE / 8 {
        let offset = start + 8 * i;
        state_flat[i] = u64::from_le_bytes(blocks[offset..offset + 8].try_into().unwrap());
    }
    for i in 0..RATE / 8 {
        set_ij(
            state,
            i / 5,
            i % 5,
            get_ij(state, i / 5, i % 5) ^ state_flat[i],
        );
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

pub type Lane2U32 = [u32; 2];

#[inline(always)]
fn rotate_left_2u32<const LEFT: i32, const RIGHT: i32>(x: Lane2U32) -> Lane2U32 {
    debug_assert!(LEFT + RIGHT == 64);

    // NB: this only works in the interleaved representation!
    [x[0].rotate_left(LEFT as u32), x[1].rotate_left(LEFT as u32)]
}

#[inline(always)]
fn _veor5q_2u32(a: Lane2U32, b: Lane2U32, c: Lane2U32, d: Lane2U32, e: Lane2U32) -> Lane2U32 {
    let mut u = a[0];
    u ^= b[0];
    u ^= c[0];
    u ^= d[0];
    u ^= e[0];

    let mut v = a[1];
    v ^= b[1];
    v ^= c[1];
    v ^= d[1];
    v ^= e[1];

    [u, v]
}

#[inline(always)]
fn _vrax1q_2u32(a: Lane2U32, b: Lane2U32) -> Lane2U32 {
    let r = rotate_left_2u32::<1, 63>(b);
    [a[0] ^ r[0], a[1] ^ r[1]]
}

#[inline(always)]
fn _vxarq_2u32<const LEFT: i32, const RIGHT: i32>(a: Lane2U32, b: Lane2U32) -> Lane2U32 {
    rotate_left_2u32::<LEFT, RIGHT>([a[0] ^ b[0], a[1] ^ b[1]])
}

#[inline(always)]
fn _vbcaxq_2u32(a: Lane2U32, b: Lane2U32, c: Lane2U32) -> Lane2U32 {
    [a[0] ^ (b[0] & !c[0]), a[1] ^ (b[1] & !c[1])]
}

#[inline(always)]
fn _veorq_n_2u32(a: Lane2U32, c: u64) -> Lane2U32 {
    [a[0] ^ ((c >> 32) as u32), a[1] ^ (c as u32)]
}

impl KeccakItem<1> for Lane2U32 {
    #[inline(always)]
    fn zero() -> Self {
        [0, 0]
    }
    #[inline(always)]
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
        _veor5q_2u32(a, b, c, d, e)
    }
    #[inline(always)]
    fn rotate_left1_and_xor(a: Self, b: Self) -> Self {
        _vrax1q_2u32(a, b)
    }
    #[inline(always)]
    fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self {
        _vxarq_2u32::<LEFT, RIGHT>(a, b)
    }
    #[inline(always)]
    fn and_not_xor(a: Self, b: Self, c: Self) -> Self {
        _vbcaxq_2u32(a, b, c)
    }
    #[inline(always)]
    fn xor_constant(a: Self, c: u64) -> Self {
        _veorq_n_2u32(a, c)
    }
    #[inline(always)]
    fn xor(a: Self, b: Self) -> Self {
        [a[0] ^ b[0], a[1] ^ b[1]]
    }
    #[inline(always)]
    fn load_block<const RATE: usize>(state: &mut [Self; 25], blocks: &[&[u8]; 1], start: usize) {
        load_block_2u32::<RATE>(state, blocks[0], start)
    }
    #[inline(always)]
    fn store_block<const RATE: usize>(state: &[Self; 25], out: &mut [&mut [u8]; 1]) {
        store_block_2u32::<RATE>(state, out[0])
    }
    #[inline(always)]
    fn load_block_full<const RATE: usize>(
        state: &mut [Self; 25],
        blocks: &[[u8; 200]; 1],
        start: usize,
    ) {
        load_block_full_2u32::<RATE>(state, &blocks[0], start)
    }
    #[inline(always)]
    fn store_block_full<const RATE: usize>(state: &[Self; 25], out: &mut [[u8; 200]; 1]) {
        store_block_full_2u32::<RATE>(state, &mut out[0]);
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
            let lane = get_ij(state, i / 5, i % 5);
            let lane = deinterleave_lane(lane);
            out[0][i * 8..i * 8 + 4].copy_from_slice(&lane[0].to_le_bytes());
            out[0][i * 8 + 4..i * 8 + 8].copy_from_slice(&lane[1].to_le_bytes());
        }

        if last_block_len > 4 {
            let lane = get_ij(state, num_full_blocks / 5, num_full_blocks % 5);
            let lane = deinterleave_lane(lane);
            let last_half_block_len = last_block_len - 4;

            out[0][num_full_blocks * 8..num_full_blocks * 8 + 4]
                .copy_from_slice(&lane[0].to_le_bytes());
            out[0][num_full_blocks * 8 + 4..num_full_blocks * 8 + last_block_len]
                .copy_from_slice(&lane[1].to_le_bytes()[0..last_half_block_len]);
        } else if last_block_len > 0 {
            let lane = get_ij(state, num_full_blocks / 5, num_full_blocks % 5);
            let lane = deinterleave_lane(lane);

            out[0][num_full_blocks * 8..num_full_blocks * 8 + last_block_len]
                .copy_from_slice(&lane[0].to_le_bytes()[0..last_block_len]);
        }
    }
}

#[inline(always)]
pub(crate) fn load_block_2u32<const RATE: usize>(
    state: &mut [Lane2U32; 25],
    blocks: &[u8],
    start: usize,
) {
    debug_assert!(RATE <= blocks.len() && RATE % 8 == 0);
    let mut state_flat = [[0u32; 2]; 25];
    for i in 0..RATE / 8 {
        let offset = start + 8 * i;
        let a = u32::from_le_bytes(blocks[offset..offset + 4].try_into().unwrap());
        let b = u32::from_le_bytes(blocks[offset + 4..offset + 8].try_into().unwrap());
        state_flat[i] = interleave_lane([a, b]);
    }
    for i in 0..RATE / 8 {
        let got = get_ij(state, i / 5, i % 5);
        set_ij(
            state,
            i / 5,
            i % 5,
            [got[0] ^ state_flat[i][0], got[1] ^ state_flat[i][1]],
        );
    }
}

#[inline(always)]
pub(crate) fn load_block_full_2u32<const RATE: usize>(
    state: &mut [Lane2U32; 25],
    blocks: &[u8; 200],
    start: usize,
) {
    load_block_2u32::<RATE>(state, blocks, start);
}

#[inline(always)]
pub(crate) fn store_block_2u32<const RATE: usize>(s: &[Lane2U32; 25], out: &mut [u8]) {
    for i in 0..RATE / 8 {
        let lane = get_ij(s, i / 5, i % 5);
        let lane = deinterleave_lane(lane);
        out[8 * i..8 * i + 4].copy_from_slice(&lane[0].to_le_bytes());
        out[8 * i + 4..8 * i + 8].copy_from_slice(&lane[1].to_le_bytes());
    }
}

#[inline(always)]
pub(crate) fn store_block_full_2u32<const RATE: usize>(s: &[Lane2U32; 25], out: &mut [u8; 200]) {
    store_block_2u32::<RATE>(s, out);
}

#[cfg(test)]
mod shuffle_test {
    use super::{shuffle, shuffle_lane, unshuffle, unshuffle_lane};

    #[test]
    fn test_identity() {
        for i in 0..0x1000 {
            assert_eq!(i, unshuffle(shuffle(i)));
        }
        for i in 0x7fff_ff00..0x1000_ffff {
            assert_eq!(i, unshuffle(shuffle(i)));
        }

        for i in 0..0x100 {
            for j in 0..0x100 {
                assert_eq!([i, j], unshuffle_lane(shuffle_lane([i, j])));
            }
        }

        for i in 0..0x100 {
            for j in 0x7fff_ff00..0x100 {
                assert_eq!([i, j], unshuffle_lane(shuffle_lane([i, j])));
            }
        }

        for i in 0x7fff_ff00..0x1000_0100 {
            for j in 0..0x100 {
                assert_eq!([i, j], unshuffle_lane(shuffle_lane([i, j])));
            }
        }

        for i in 0x7fff_ff00..0x1000_0100 {
            for j in 0x7fff_ff00..0x1000_0100 {
                assert_eq!([i, j], unshuffle_lane(shuffle_lane([i, j])));
            }
        }
    }

    #[test]
    fn test_known() {
        // 00001111 -> 01010101
        assert_eq!(shuffle(0x00ff), 0x5555);

        // 11111111 00001111 -> 10101010 01010101
        assert_eq!(shuffle(0xff0000ff), 0xaaaa5555);

        assert_eq!(
            shuffle_lane([0xffff_ff00, 0x0000_ffff]),
            [0xaaaa_aaaa, 0xffff5555]
        )
    }
}
