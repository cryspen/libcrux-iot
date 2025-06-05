use crate::lane::Lane2U32;

#[cfg_attr(hax, hax_lib::opaque)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct KeccakState {
    pub(super) st: [Lane2U32; 25],
    pub(super) c: [Lane2U32; 5],
    pub(super) d: [Lane2U32; 5],
    pub(super) i: usize,
}

impl KeccakState {
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {
            st: [Lane2U32::zero(); 25],
            c: [Lane2U32::zero(); 5],
            d: [Lane2U32::zero(); 5],
            i: 0,
        }
    }

    #[inline(always)]
    pub(crate) fn get_with_zeta(&self, i: usize, j: usize, zeta: usize) -> u32 {
        self.st[5 * j + i][zeta]
    }

    #[inline(always)]
    pub(crate) fn set_with_zeta(&mut self, i: usize, j: usize, zeta: usize, v: u32) {
        self.st[5 * j + i][zeta] = v
    }

    #[inline(always)]
    pub(crate) fn get_lane(&self, i: usize, j: usize) -> Lane2U32 {
        self.st[5 * j + i]
    }

    #[inline(always)]
    pub(crate) fn set_lane(&mut self, i: usize, j: usize, lane: Lane2U32) {
        self.st[5 * j + i] = lane
    }

    #[inline(always)]
    pub(crate) fn load_block<const RATE: usize>(&mut self, blocks: &[u8], start: usize) {
        load_block_2u32::<RATE>(self, blocks, start)
    }

    #[inline(always)]
    pub(crate) fn store_block<const RATE: usize>(&self, out: &mut [u8]) {
        store_block_2u32::<RATE>(self, out)
    }

    #[inline(always)]
    pub(crate) fn load_block_full<const RATE: usize>(&mut self, blocks: &[u8; 200], start: usize) {
        load_block_full_2u32::<RATE>(self, blocks, start)
    }

    #[inline(always)]
    pub(crate) fn store_block_full<const RATE: usize>(&self, out: &mut [u8; 200]) {
        store_block_full_2u32::<RATE>(self, out);
    }

    /// `out` has the exact size we want here. It must be less than or equal to `RATE`.
    #[inline(always)]
    pub(crate) fn store<const RATE: usize>(self, out: &mut [u8]) {
        debug_assert!(out.len() <= RATE, "{} > {}", out.len(), RATE);

        let num_full_blocks = out.len() / 8;
        let last_block_len = out.len() % 8;

        for i in 0..num_full_blocks {
            let lane = self.get_lane(i / 5, i % 5).deinterleave();
            out[i * 8..i * 8 + 4].copy_from_slice(&lane[0].to_le_bytes());
            out[i * 8 + 4..i * 8 + 8].copy_from_slice(&lane[1].to_le_bytes());
        }

        if last_block_len > 4 {
            let lane = self
                .get_lane(num_full_blocks / 5, num_full_blocks % 5)
                .deinterleave();
            let last_half_block_len = last_block_len - 4;

            out[num_full_blocks * 8..num_full_blocks * 8 + 4]
                .copy_from_slice(&lane[0].to_le_bytes());
            out[num_full_blocks * 8 + 4..num_full_blocks * 8 + last_block_len]
                .copy_from_slice(&lane[1].to_le_bytes()[0..last_half_block_len]);
        } else if last_block_len > 0 {
            let lane = self
                .get_lane(num_full_blocks / 5, num_full_blocks % 5)
                .deinterleave();

            out[num_full_blocks * 8..num_full_blocks * 8 + last_block_len]
                .copy_from_slice(&lane[0].to_le_bytes()[0..last_block_len]);
        }
    }
}

#[inline(always)]
fn load_block_2u32<const RATE: usize>(state: &mut KeccakState, blocks: &[u8], start: usize) {
    debug_assert!(RATE <= blocks.len() && RATE % 8 == 0);
    let mut state_flat = [Lane2U32::zero(); 25];
    for i in 0..RATE / 8 {
        let offset = start + 8 * i;
        let a = u32::from_le_bytes(blocks[offset..offset + 4].try_into().unwrap());
        let b = u32::from_le_bytes(blocks[offset + 4..offset + 8].try_into().unwrap());
        state_flat[i] = Lane2U32::from([a, b]).interleave();
    }
    for i in 0..RATE / 8 {
        let got = state.get_lane(i / 5, i % 5);
        state.set_lane(
            i / 5,
            i % 5,
            [got[0] ^ state_flat[i][0], got[1] ^ state_flat[i][1]].into(),
        );
    }
}

#[inline(always)]
fn load_block_full_2u32<const RATE: usize>(
    state: &mut KeccakState,
    blocks: &[u8; 200],
    start: usize,
) {
    load_block_2u32::<RATE>(state, blocks, start);
}

#[inline(always)]
fn store_block_2u32<const RATE: usize>(s: &KeccakState, out: &mut [u8]) {
    for i in 0..RATE / 8 {
        let lane = s.get_lane(i / 5, i % 5).deinterleave();
        out[8 * i..8 * i + 4].copy_from_slice(&lane[0].to_le_bytes());
        out[8 * i + 4..8 * i + 8].copy_from_slice(&lane[1].to_le_bytes());
    }
}

#[inline(always)]
fn store_block_full_2u32<const RATE: usize>(s: &KeccakState, out: &mut [u8; 200]) {
    store_block_2u32::<RATE>(s, out);
}
