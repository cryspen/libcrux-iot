use crate::traits::{internal::*, *};
use libcrux_intrinsics::avx2::*;

#[inline(always)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: Vec256) -> Vec256 {
    debug_assert!(LEFT + RIGHT == 64);
    // XXX: This could be done more efficiently, if the shift values are multiples of 8.
    mm256_xor_si256(mm256_slli_epi64::<LEFT>(x), mm256_srli_epi64::<RIGHT>(x))
}

#[inline(always)]
fn _veor5q_u64(a: Vec256, b: Vec256, c: Vec256, d: Vec256, e: Vec256) -> Vec256 {
    let ab = mm256_xor_si256(a, b);
    let cd = mm256_xor_si256(c, d);
    let abcd = mm256_xor_si256(ab, cd);
    mm256_xor_si256(abcd, e)
}

#[inline(always)]
fn _vrax1q_u64(a: Vec256, b: Vec256) -> Vec256 {
    mm256_xor_si256(a, rotate_left::<1, 63>(b))
}

#[inline(always)]
fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: Vec256, b: Vec256) -> Vec256 {
    let ab = mm256_xor_si256(a, b);
    rotate_left::<LEFT, RIGHT>(ab)
}

#[inline(always)]
fn _vbcaxq_u64(a: Vec256, b: Vec256, c: Vec256) -> Vec256 {
    mm256_xor_si256(a, mm256_andnot_si256(c, b))
}

#[inline(always)]
fn _veorq_n_u64(a: Vec256, c: u64) -> Vec256 {
    // Casting here is required, doesn't change the value.
    let c = mm256_set1_epi64x(c as i64);
    mm256_xor_si256(a, c)
}

#[inline(always)]
pub(crate) fn load_block<const RATE: usize>(
    state: &mut [Vec256; 25],
    blocks: &[&[u8]; 4],
    offset: usize,
) {
    debug_assert!(RATE <= blocks[0].len() && RATE % 8 == 0 && (RATE % 32 == 8 || RATE % 32 == 16));
    for i in 0..RATE / 32 {
        let start = offset + 32 * i;
        let v0 = mm256_loadu_si256_u8(&blocks[0][start..start + 32]);
        let v1 = mm256_loadu_si256_u8(&blocks[1][start..start + 32]);
        let v2 = mm256_loadu_si256_u8(&blocks[2][start..start + 32]);
        let v3 = mm256_loadu_si256_u8(&blocks[3][start..start + 32]);

        let v0l = mm256_unpacklo_epi64(v0, v1); // 0 0 2 2
        let v1h = mm256_unpackhi_epi64(v0, v1); // 1 1 3 3
        let v2l = mm256_unpacklo_epi64(v2, v3); // 0 0 2 2
        let v3h = mm256_unpackhi_epi64(v2, v3); // 1 1 3 3

        let v0 = mm256_permute2x128_si256::<0x20>(v0l, v2l); // 0 0 0 0
        let v1 = mm256_permute2x128_si256::<0x20>(v1h, v3h); // 1 1 1 1
        let v2 = mm256_permute2x128_si256::<0x31>(v0l, v2l); // 2 2 2 2
        let v3 = mm256_permute2x128_si256::<0x31>(v1h, v3h); // 3 3 3 3

        let i0 = (4 * i) / 5;
        let j0 = (4 * i) % 5;
        let i1 = (4 * i + 1) / 5;
        let j1 = (4 * i + 1) % 5;
        let i2 = (4 * i + 2) / 5;
        let j2 = (4 * i + 2) % 5;
        let i3 = (4 * i + 3) / 5;
        let j3 = (4 * i + 3) % 5;

        set_ij(state, i0, j0, mm256_xor_si256(get_ij(state, i0, j0), v0));
        set_ij(state, i1, j1, mm256_xor_si256(get_ij(state, i1, j1), v1));
        set_ij(state, i2, j2, mm256_xor_si256(get_ij(state, i2, j2), v2));
        set_ij(state, i3, j3, mm256_xor_si256(get_ij(state, i3, j3), v3));
    }

    let rem = RATE % 32; // has to be 8 or 16
    let start = offset + 32 * (RATE / 32);
    let mut u8s = [0u8; 32];
    u8s[0..8].copy_from_slice(&blocks[0][start..start + 8]);
    u8s[8..16].copy_from_slice(&blocks[1][start..start + 8]);
    u8s[16..24].copy_from_slice(&blocks[2][start..start + 8]);
    u8s[24..32].copy_from_slice(&blocks[3][start..start + 8]);
    let u = mm256_loadu_si256_u8(u8s.as_slice());
    let i = (4 * (RATE / 32)) / 5;
    let j = (4 * (RATE / 32)) % 5;
    set_ij(state, i, j, mm256_xor_si256(get_ij(state, i, j), u));
    if rem == 16 {
        let mut u8s = [0u8; 32];
        u8s[0..8].copy_from_slice(&blocks[0][start + 8..start + 16]);
        u8s[8..16].copy_from_slice(&blocks[1][start + 8..start + 16]);
        u8s[16..24].copy_from_slice(&blocks[2][start + 8..start + 16]);
        u8s[24..32].copy_from_slice(&blocks[3][start + 8..start + 16]);
        let u = mm256_loadu_si256_u8(u8s.as_slice());
        let i = (4 * (RATE / 32) + 1) / 5;
        let j = (4 * (RATE / 32) + 1) % 5;
        set_ij(state, i, j, mm256_xor_si256(get_ij(state, i, j), u));
    }
}

#[inline(always)]
pub(crate) fn load_block_full<const RATE: usize>(
    state: &mut [Vec256; 25],
    blocks: &[[u8; 200]; 4],
    start: usize,
) {
    load_block::<RATE>(
        state,
        &[
            &blocks[0] as &[u8],
            &blocks[1] as &[u8],
            &blocks[2] as &[u8],
            &blocks[3] as &[u8],
        ],
        start,
    );
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(s: &[Vec256; 25], out: &mut [&mut [u8]; 4]) {
    for i in 0..RATE / 32 {
        let i0 = (4 * i) / 5;
        let j0 = (4 * i) % 5;
        let i1 = (4 * i + 1) / 5;
        let j1 = (4 * i + 1) % 5;
        let i2 = (4 * i + 2) / 5;
        let j2 = (4 * i + 2) % 5;
        let i3 = (4 * i + 3) / 5;
        let j3 = (4 * i + 3) % 5;

        let v0l = mm256_permute2x128_si256::<0x20>(get_ij(s, i0, j0), get_ij(s, i2, j2));
        // 0 0 2 2
        let v1h = mm256_permute2x128_si256::<0x20>(get_ij(s, i1, j1), get_ij(s, i3, j3)); // 1 1 3 3
        let v2l = mm256_permute2x128_si256::<0x31>(get_ij(s, i0, j0), get_ij(s, i2, j2)); // 0 0 2 2
        let v3h = mm256_permute2x128_si256::<0x31>(get_ij(s, i1, j1), get_ij(s, i3, j3)); // 1 1 3 3

        let v0 = mm256_unpacklo_epi64(v0l, v1h); // 0 1 2 3
        let v1 = mm256_unpackhi_epi64(v0l, v1h); // 0 1 2 3
        let v2 = mm256_unpacklo_epi64(v2l, v3h); // 0 1 2 3
        let v3 = mm256_unpackhi_epi64(v2l, v3h); // 0 1 2 3

        mm256_storeu_si256_u8(&mut out[0][32 * i..32 * (i + 1)], v0);
        mm256_storeu_si256_u8(&mut out[1][32 * i..32 * (i + 1)], v1);
        mm256_storeu_si256_u8(&mut out[2][32 * i..32 * (i + 1)], v2);
        mm256_storeu_si256_u8(&mut out[3][32 * i..32 * (i + 1)], v3);
    }

    let rem = RATE % 32; // has to be 8 or 16
    let start = 32 * (RATE / 32);
    let mut u8s = [0u8; 32];
    let i = (4 * (RATE / 32)) / 5;
    let j = (4 * (RATE / 32)) % 5;
    mm256_storeu_si256_u8(&mut u8s, get_ij(s, i, j));
    out[0][start..start + 8].copy_from_slice(&u8s[0..8]);
    out[1][start..start + 8].copy_from_slice(&u8s[8..16]);
    out[2][start..start + 8].copy_from_slice(&u8s[16..24]);
    out[3][start..start + 8].copy_from_slice(&u8s[24..32]);
    if rem == 16 {
        let mut u8s = [0u8; 32];
        let i = (4 * (RATE / 32) + 1) / 5;
        let j = (4 * (RATE / 32) + 1) % 5;
        mm256_storeu_si256_u8(&mut u8s, get_ij(s, i, j));
        out[0][start + 8..start + 16].copy_from_slice(&u8s[0..8]);
        out[1][start + 8..start + 16].copy_from_slice(&u8s[8..16]);
        out[2][start + 8..start + 16].copy_from_slice(&u8s[16..24]);
        out[3][start + 8..start + 16].copy_from_slice(&u8s[24..32]);
    }
}

#[inline(always)]
pub(crate) fn store_block_full<const RATE: usize>(state: &[Vec256; 25], out: &mut [[u8; 200]; 4]) {
    let (out0, rest) = out.split_at_mut(1);
    let (out1, rest) = rest.split_at_mut(1);
    let (out2, out3) = rest.split_at_mut(1);

    store_block::<RATE>(
        state,
        &mut [&mut out0[0], &mut out1[0], &mut out2[0], &mut out3[0]],
    );
}

#[inline(always)]
fn split_at_mut_4(out: [&mut [u8]; 4], mid: usize) -> ([&mut [u8]; 4], [&mut [u8]; 4]) {
    let [out0, out1, out2, out3] = out;
    let (out00, out01) = out0.split_at_mut(mid);
    let (out10, out11) = out1.split_at_mut(mid);
    let (out20, out21) = out2.split_at_mut(mid);
    let (out30, out31) = out3.split_at_mut(mid);
    ([out00, out10, out20, out30], [out01, out11, out21, out31])
}

impl KeccakItem<4> for Vec256 {
    #[inline(always)]
    fn zero() -> Self {
        mm256_set1_epi64x(0)
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
        mm256_xor_si256(a, b)
    }
    #[inline(always)]
    fn load_block<const RATE: usize>(state: &mut [Self; 25], blocks: &[&[u8]; 4], start: usize) {
        load_block::<RATE>(state, blocks, start)
    }
    #[inline(always)]
    fn store_block<const RATE: usize>(a: &[Self; 25], b: &mut [&mut [u8]; 4]) {
        store_block::<RATE>(a, b)
    }
    #[inline(always)]
    fn load_block_full<const RATE: usize>(
        state: &mut [Self; 25],
        blocks: &[[u8; 200]; 4],
        start: usize,
    ) {
        load_block_full::<RATE>(state, blocks, start)
    }
    #[inline(always)]
    fn store_block_full<const RATE: usize>(state: &[Self; 25], out: &mut [[u8; 200]; 4]) {
        store_block_full::<RATE>(state, out)
    }

    #[inline(always)]
    fn split_at_mut_n(a: [&mut [u8]; 4], mid: usize) -> ([&mut [u8]; 4], [&mut [u8]; 4]) {
        split_at_mut_4(a, mid)
    }

    // TODO: Do we need this, or not? cf. https://github.com/cryspen/libcrux/issues/482
    fn store<const RATE: usize>(_state: &[Self; 25], _out: [&mut [u8]; 4]) {
        todo!()
    }
}
