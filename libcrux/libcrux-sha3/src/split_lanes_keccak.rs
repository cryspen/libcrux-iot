//! A portable SHA3 implementation using the generic implementation.

use crate::traits::internal::*;

#[inline(always)]
fn rotate_left_interleaved_packed<const LEFT: i32, const RIGHT: i32>(x: u64) -> u64 {
    debug_assert!(LEFT + RIGHT == 64);
    let (x0, x1) = to_split(x);
    let x = if LEFT == 1 {
        (x1 << 1, x0)
    } else if LEFT % 2 == 0 {
        (x0 << LEFT % 32, x1 << LEFT % 32)
    } else {
        let tau = (LEFT - 1) / 2;
        (x1 << (tau + 1) % 32, x0 << tau % 32)
    };
    from_split(x)
}

#[inline(always)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: (u32, u32)) -> (u32, u32) {
    debug_assert!(LEFT + RIGHT == 64);
    if LEFT == 1 {
        (x.1 << 1, x.0)
    } else if LEFT % 2 == 0 {
        (x.0 << LEFT % 32, x.1 << LEFT % 32)
    } else {
        let tau = (LEFT - 1) / 2;
        (x.1 << (tau + 1) % 32, x.0 << tau % 32)
    }
}

#[inline(always)]
fn rotate_left_naive<const LEFT: i32, const RIGHT: i32>(x: (u32, u32)) -> (u32, u32) {
    debug_assert!(LEFT + RIGHT == 64);
    if LEFT == RIGHT {
        (x.1, x.0)
    } else if LEFT < RIGHT {
        (
            x.0 << LEFT | x.1 >> (RIGHT % 32),
            x.1 << LEFT | x.0 >> (RIGHT % 32),
        )
    } else {
        (
            x.0 >> RIGHT | x.1 << (LEFT % 32),
            x.1 >> RIGHT | x.0 << (LEFT % 32),
        )
    }
}

#[inline(always)]
fn _veor5q_split(
    a: (u32, u32),
    b: (u32, u32),
    c: (u32, u32),
    d: (u32, u32),
    e: (u32, u32),
) -> (u32, u32) {
    let ab0 = a.0 ^ b.0;
    let cd0 = c.0 ^ d.0;
    let abcd0 = ab0 ^ cd0;

    let ab1 = a.1 ^ b.1;
    let cd1 = c.1 ^ d.1;
    let abcd1 = ab1 ^ cd1;

    (abcd0 ^ e.0, abcd1 ^ e.1)
}

#[inline(always)]
fn _vrax1q_split(a: (u32, u32), b: (u32, u32)) -> (u32, u32) {
    let rot_b = rotate_left::<1, 63>(b);
    (a.0 ^ rot_b.0, a.1 ^ rot_b.1)
}

#[inline(always)]
fn _vxarq_split<const LEFT: i32, const RIGHT: i32>(a: (u32, u32), b: (u32, u32)) -> (u32, u32) {
    let ab0 = a.0 ^ b.0;
    let ab1 = a.1 ^ b.1;
    rotate_left::<LEFT, RIGHT>((ab0, ab1))
}

#[inline(always)]
fn _vbcaxq_split(a: (u32, u32), b: (u32, u32), c: (u32, u32)) -> (u32, u32) {
    (a.0 ^ (b.0 & !c.0), a.1 ^ (b.1 & !c.1))
}

#[inline(always)]
fn _veorq_n_split(a: (u32, u32), c: u64) -> (u32, u32) {
    // XXX: This could be precomputed, but breaks generality of
    // `generic_keccak`. Instead modify fn in trait to take `c`s
    // index.
    let (c0, c1) = deinterleave(c); 
    (a.0 ^ c0, a.1 ^ c1)
}

fn deinterleave(a: u64) -> (u32, u32) {
    let mut even_bits = a & 0x5555_5555_5555_5555;
    even_bits = (even_bits ^ (even_bits >> 1)) & 0x3333_3333_3333_3333;
    even_bits = (even_bits ^ (even_bits >> 2)) & 0x0f0f_0f0f_0f0f_0f0f;
    even_bits = (even_bits ^ (even_bits >> 4)) & 0x00ff_00ff_00ff_00ff;
    even_bits = (even_bits ^ (even_bits >> 8)) & 0x0000_ffff_0000_ffff;
    even_bits = (even_bits ^ (even_bits >> 16)) & 0x0000_0000_ffff_ffff;

    let mut odd_bits = (a >> 1) & 0x5555_5555_5555_5555;
    odd_bits = (odd_bits ^ (odd_bits >> 1)) & 0x3333_3333_3333_3333;
    odd_bits = (odd_bits ^ (odd_bits >> 2)) & 0x0f0f_0f0f_0f0f_0f0f;
    odd_bits = (odd_bits ^ (odd_bits >> 4)) & 0x00ff_00ff_00ff_00ff;
    odd_bits = (odd_bits ^ (odd_bits >> 8)) & 0x0000_ffff_0000_ffff;
    odd_bits = (odd_bits ^ (odd_bits >> 16)) & 0x0000_0000_ffff_ffff;

    (even_bits as u32, odd_bits as u32)
}

fn interleave(even_bits: u32, odd_bits: u32) -> u64 {
    let mut even_spaced = even_bits as u64;
    even_spaced = (even_spaced ^ (even_spaced << 16)) & 0x0000_ffff_0000_ffff;
    even_spaced = (even_spaced ^ (even_spaced << 8)) & 0x00ff_00ff_00ff_00ff;
    even_spaced = (even_spaced ^ (even_spaced << 4)) & 0x0f0f_0f0f_0f0f_0f0f;
    even_spaced = (even_spaced ^ (even_spaced << 2)) & 0x3333_3333_3333_3333;
    even_spaced = (even_spaced ^ (even_spaced << 1)) & 0x5555_5555_5555_5555;
    

    let mut odd_spaced = odd_bits as u64;                                   
    odd_spaced = (odd_spaced ^ (odd_spaced << 16)) & 0x0000_ffff_0000_ffff;
    odd_spaced = (odd_spaced ^ (odd_spaced << 8)) & 0x00ff_00ff_00ff_00ff;
    odd_spaced = (odd_spaced ^ (odd_spaced << 4)) & 0x0f0f_0f0f_0f0f_0f0f;
    odd_spaced = (odd_spaced ^ (odd_spaced << 2)) & 0x3333_3333_3333_3333;
    odd_spaced = (odd_spaced ^ (odd_spaced << 1)) & 0x5555_5555_5555_5555;
        
    even_spaced | (odd_spaced << 1)
}

#[inline(always)]
pub(crate) fn load_block<const RATE: usize>(s: &mut [[(u32, u32); 5]; 5], blocks: [&[u8]; 1]) {
    debug_assert!(RATE <= blocks[0].len() && RATE % 8 == 0);
    for i in 0..RATE / 8 {
        let (lane0, lane1) = deinterleave(u64::from_le_bytes(blocks[0][8 * i..8 * i + 8].try_into().unwrap()));
        (s[i / 5][i % 5]).0 ^= lane0;
        (s[i / 5][i % 5]).1 ^= lane1;
    }
}

#[inline(always)]
pub(crate) fn load_block_full<const RATE: usize>(
    s: &mut [[(u32, u32); 5]; 5],
    blocks: [[u8; 200]; 1],
) {
    load_block::<RATE>(s, [&blocks[0] as &[u8]]);
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(s: &[[(u32, u32); 5]; 5], out: [&mut [u8]; 1]) {
    for i in 0..RATE / 8 {
        out[0][8 * i..8 * i + 8].copy_from_slice(&interleave(s[i / 5][i % 5].0, s[i / 5][i % 5].1).to_le_bytes());
    }
}

#[inline(always)]
pub(crate) fn store_block_full<const RATE: usize>(s: &[[(u32, u32); 5]; 5]) -> [[u8; 200]; 1] {
    let mut out = [0u8; 200];
    store_block::<RATE>(s, [&mut out]);
    [out]
}

#[inline(always)]
fn slice_1(a: [&[u8]; 1], start: usize, len: usize) -> [&[u8]; 1] {
    [&a[0][start..start + len]]
}

#[inline(always)]
fn split_at_mut_1(out: [&mut [u8]; 1], mid: usize) -> ([&mut [u8]; 1], [&mut [u8]; 1]) {
    let (out00, out01) = out[0].split_at_mut(mid);
    ([out00], [out01])
}

impl KeccakItem<1> for (u32, u32) {
    #[inline(always)]
    fn zero() -> Self {
        (0, 0)
    }
    #[inline(always)]
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
        _veor5q_split(a, b, c, d, e)
    }
    #[inline(always)]
    fn rotate_left1_and_xor(a: Self, b: Self) -> Self {
        _vrax1q_split(a, b)
    }
    #[inline(always)]
    fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self {
        _vxarq_split::<LEFT, RIGHT>(a, b)
    }
    #[inline(always)]
    fn and_not_xor(a: Self, b: Self, c: Self) -> Self {
        _vbcaxq_split(a, b, c)
    }
    #[inline(always)]
    fn xor_constant(a: Self, c: u64) -> Self {
        _veorq_n_split(a, c)
    }
    #[inline(always)]
    fn xor(a: Self, b: Self) -> Self {
        (a.0 ^ b.0, a.1 ^ b.1)
    }
    #[inline(always)]
    fn load_block<const RATE: usize>(a: &mut [[Self; 5]; 5], b: [&[u8]; 1]) {
        load_block::<RATE>(a, b)
    }
    #[inline(always)]
    fn store_block<const RATE: usize>(a: &[[Self; 5]; 5], b: [&mut [u8]; 1]) {
        store_block::<RATE>(a, b)
    }
    #[inline(always)]
    fn load_block_full<const RATE: usize>(a: &mut [[Self; 5]; 5], b: [[u8; 200]; 1]) {
        load_block_full::<RATE>(a, b)
    }
    #[inline(always)]
    fn store_block_full<const RATE: usize>(a: &[[Self; 5]; 5]) -> [[u8; 200]; 1] {
        store_block_full::<RATE>(a)
    }
    #[inline(always)]
    fn slice_n(a: [&[u8]; 1], start: usize, len: usize) -> [&[u8]; 1] {
        slice_1(a, start, len)
    }
    #[inline(always)]
    fn split_at_mut_n(a: [&mut [u8]; 1], mid: usize) -> ([&mut [u8]; 1], [&mut [u8]; 1]) {
        split_at_mut_1(a, mid)
    }

    /// `out` has the exact size we want here. It must be less than or equal to `RATE`.
    #[inline(always)]
    fn store<const RATE: usize>(state: &[[Self; 5]; 5], out: [&mut [u8]; 1]) {
        debug_assert!(out.len() <= RATE / 8, "{} > {}", out.len(), RATE);

        let num_full_blocks = out[0].len() / 8;
        let last_block_len = out[0].len() % 8;

        for i in 0..num_full_blocks {
            out[0][8 * i..8 * i + 8].copy_from_slice(&interleave(state[i / 5][i % 5].0, state[i / 5][i % 5].1).to_le_bytes());
        }
        if last_block_len != 0 {
            // TODO: Store de-interleaved
            if last_block_len <= 4 {
                out[0][num_full_blocks * 8..num_full_blocks * 8 + last_block_len].copy_from_slice(
                    &state[num_full_blocks / 5][num_full_blocks % 5]
                        .1
                        .to_le_bytes()[0..last_block_len],
                );
            } else {
                out[0][num_full_blocks * 8..num_full_blocks * 8 + 4].copy_from_slice(
                    &state[num_full_blocks / 5][num_full_blocks % 5]
                        .1
                        .to_le_bytes(),
                );
                out[0][num_full_blocks * 8 + 4..num_full_blocks * 8 + last_block_len]
                    .copy_from_slice(
                        &state[num_full_blocks / 5][num_full_blocks % 5]
                            .0
                            .to_le_bytes()[0..last_block_len - 4],
                    );
            }
        }
    }
}

#[inline(always)]
fn to_split(a: u64) -> (u32, u32) {
    ((a >> 32) as u32, a as u32)
}

#[inline(always)]
fn from_split(a: (u32, u32)) -> u64 {
    (a.0 as u64) << 32 | (a.1 as u64)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn ops() {
        let a: u32 = 0x09807908;
        let b: u32 = 0x1234;
        let ab_split = (a, b);

        let con1: u64 = u64::MAX - 12;
        let con2: u64 = 12;

        let ab = from_split(ab_split);

        // assert_eq!(
        //     rotate_left::<1, 63>(ab_split),
        //     to_split(crate::portable_keccak::rotate_left::<1, 63>(ab))
        // );
        // assert_eq!(
        //     rotate_left::<63, 1>(ab_split),
        //     to_split(crate::portable_keccak::rotate_left::<63, 1>(ab))
        // );
        // assert_eq!(
        //     rotate_left::<32, 32>(ab_split),
        //     to_split(crate::portable_keccak::rotate_left::<32, 32>(ab))
        // );

        assert_eq!(
            (a,b), deinterleave(interleave(a, b))
        )
    }
}


