use core::ops::{Index, IndexMut};

/// A lane of the Keccak state,
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lane2U32([u32; 2]);

impl Lane2U32 {
    #[inline(always)]
    pub(crate) fn zero() -> Self {
        [0, 0].into()
    }

    #[inline(always)]
    pub(crate) fn split_at_mut_n(a: &mut [u8], mid: usize) -> (&mut [u8], &mut [u8]) {
        split_at_mut_1(a, mid)
    }

    // NOTE: it would be a bit nicer if we used separate types for the interleaved and
    // noninterleaved representation
    #[inline(always)]
    pub(crate) fn interleave(self) -> Self {
        let lane_u64 = self[0] as u64 | (self[1] as u64) << 32;
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

        [even_bits as u32, odd_bits as u32].into()
    }

    #[inline(always)]
    pub(crate) fn deinterleave(self) -> Lane2U32 {
        let Lane2U32([even_bits, odd_bits]) = self;
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
        .into()
    }
}

impl Index<usize> for Lane2U32 {
    type Output = u32;

    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl IndexMut<usize> for Lane2U32 {
    #[inline(always)]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl From<[u32; 2]> for Lane2U32 {
    #[inline(always)]
    fn from(value: [u32; 2]) -> Self {
        Self(value)
    }
}

#[inline(always)]
fn split_at_mut_1(out: &mut [u8], mid: usize) -> (&mut [u8], &mut [u8]) {
    out.split_at_mut(mid)
}

#[cfg(test)]
mod interleave_tests {
    use super::*;

    #[test]
    fn identity() {
        let lanes: [Lane2U32; 1] = [[0x800001, 43].into()];

        for lane in lanes {
            let lane_ = lane.interleave().deinterleave();
            assert_eq!(lane, lane_, "lane_: {lane_:x?}, lane: {lane:x?}")
        }
    }
}
