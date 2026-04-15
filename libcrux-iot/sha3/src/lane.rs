use core::ops::Index;

use libcrux_secrets::{CastOps, Classify as _, U32};

/// A lane of the Keccak state,
///
/// [spec](http://github.com/cryspen/libcrux-iot/blob/franziskus/proofs-and-reqs/libcrux-iot/sha3/specs/api.md#EQ-01)
#[derive(Clone, Copy)]
pub struct Lane2U32(pub(crate) [U32; 2]);

impl Lane2U32 {
    #[inline(always)]
    pub(crate) fn from_ints(value: [U32; 2]) -> Self {
        Self(value)
    }

    #[inline(always)]
    pub(crate) fn zero() -> Self {
        Self::from_ints([0, 0].classify())
    }

    // NOTE: it would be a bit nicer if we used separate types for the interleaved and
    // noninterleaved representation
    #[inline(always)]
    pub(crate) fn interleave(self) -> Self {
        let lane_u64 = self[0].as_u64() | (self[1].as_u64()) << 32;
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

        Self::from_ints([even_bits.as_u32(), odd_bits.as_u32()])
    }

    #[inline(always)]
    pub(crate) fn deinterleave(self) -> Lane2U32 {
        let even_bits = self.0[0];
        let odd_bits = self.0[1];
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

        Self([
            even_spaced_lo | (odd_spaced_lo << 1),
            even_spaced_hi | (odd_spaced_hi << 1),
        ])
    }
}

impl Index<usize> for Lane2U32 {
    type Output = U32;

    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl From<[U32; 2]> for Lane2U32 {
    #[inline(always)]
    fn from(value: [U32; 2]) -> Self {
        Self(value)
    }
}

// XXX: This impl will panic Charon at rev 667d2fc98984ff7f3df989c2367e6c1fa4a000e7, so the derivations of
//      `Debug` which build on it have to be switched off for Eurydice.
#[cfg(not(eurydice))]
#[cfg_attr(hax, hax_lib::opaque)]
impl core::fmt::Debug for Lane2U32 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        use libcrux_secrets::Declassify;
        f.debug_tuple("Lane2U32")
            .field(&self.0.declassify())
            .finish()
    }
}

#[cfg(all(not(eurydice), test))]
mod interleave_tests {
    use libcrux_secrets::Declassify;

    use super::*;

    #[test]
    fn identity() {
        let lanes: [Lane2U32; 1] = [[0x800001, 43].classify().into()];

        for lane in lanes {
            let lane_ = lane.interleave().deinterleave();
            assert_eq!(
                lane.0.declassify(),
                lane_.0.declassify(),
                "lane_: {lane_:x?}, lane: {lane:x?}",
            )
        }
    }
}
