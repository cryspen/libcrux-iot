//! A portable SHA3 implementation using the generic implementation.

use crate::traits::internal::*;

#[inline(always)]
fn to_split(a: u64) -> (u32, u32) {
    ((a >> 32) as u32, a as u32)
}

#[inline(always)]
fn from_split(a: (u32, u32)) -> u64 {
    (a.0 as u64) << 32 | (a.1 as u64)
}


#[inline(always)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: u64) -> u64 {
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
pub(crate) fn _veor5q_u64(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64 {
    let ab = a ^ b;
    let cd = c ^ d;
    let abcd = ab ^ cd;
    abcd ^ e
}

#[inline(always)]
fn _vrax1q_u64(a: u64, b: u64) -> u64 {
    a ^ rotate_left::<1, 63>(b)
}

#[inline(always)]
fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: u64, b: u64) -> u64 {
    let ab = a ^ b;
    rotate_left::<LEFT, RIGHT>(ab)
}

#[inline(always)]
fn _vbcaxq_u64(a: u64, b: u64, c: u64) -> u64 {
    a ^ (b & !c)
}

#[inline(always)]
fn _veorq_n_u64(a: u64, c: u64) -> u64 {
    a ^ c
}

/// Separate even and odd bits of `a`.
///
/// deinterleave(a) = a_even || a_odd
#[inline(always)]
fn deinterleave(a: u64) -> u64 {
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

    from_split((even_bits as u32, odd_bits as u32))
}

/// Interleave bits from the top and bottom halves of `input`.
#[inline(always)]
fn interleave(input: u64) -> u64 {
    let (even_bits, odd_bits) = to_split(input);
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
pub(crate) fn load_block<const RATE: usize>(s: &mut [[u64; 5]; 5], blocks: [&[u8]; 1]) {
    debug_assert!(RATE <= blocks[0].len() && RATE % 8 == 0);
    let mut out = [0u64; RATE];

    for i in 0..RATE / 8 {
        out[i] = deinterleave(u64::from_le_bytes(blocks[0][8 * i..8 * i + 8].try_into().unwrap()));
    }

    for i in 0..RATE / 8 {
        s[i / 5][i % 5] ^= out[i]
    }
}

#[inline(always)]
pub(crate) fn load_block_full<const RATE: usize>(s: &mut [[u64; 5]; 5], blocks: [[u8; 200]; 1]) {
    load_block::<RATE>(s, [&blocks[0] as &[u8]]);
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(s: &[[u64; 5]; 5], out: [&mut [u8]; 1]) {
    for i in 0..RATE / 8 {
        out[0][8 * i..8 * i + 8].copy_from_slice(&interleave(s[i / 5][i % 5]).to_le_bytes());
    }
}

#[inline(always)]
pub(crate) fn store_block_full<const RATE: usize>(s: &[[u64; 5]; 5]) -> [[u8; 200]; 1] {
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
            out[0][i * 8..i * 8 + 8].copy_from_slice(&interleave(state[i / 5][i % 5]).to_le_bytes());
        }
        if last_block_len != 0 {
            out[0][num_full_blocks * 8..num_full_blocks * 8 + last_block_len].copy_from_slice(
                &interleave(state[num_full_blocks / 5][num_full_blocks % 5]).to_le_bytes()[0..last_block_len],
            );
        }
    }
}
