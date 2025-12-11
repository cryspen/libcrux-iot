use libcrux_secrets::{CastOps as _, Classify as _, Declassify as _, I32, U8};

use crate::{constants::FIELD_MODULUS, helper::cloop};

#[inline(always)]
pub fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;

    cloop! {
        for bytes in randomness.chunks_exact(3) {
            let b0 = bytes[0] as i32;
            let b1 = bytes[1] as i32;
            let b2 = bytes[2] as i32;

            let coefficient = ((b2 << 16) | (b1 << 8) | b0) & 0x00_7F_FF_FF;

            if coefficient < FIELD_MODULUS {
                out[sampled] = coefficient;
                sampled += 1;
            }
        }
    }

    sampled
}

#[inline(always)]
pub fn rejection_sample_less_than_eta_equals_2(randomness: &[U8], out: &mut [I32]) -> usize {
    let mut sampled = 0;

    cloop! {
        for byte in randomness.iter() {
            let try_0 = *byte & 0xF;
            let try_1 = *byte >> 4;

            // Declassification: This reveals only the index of the
            // coefficient that was sampled.
            if try_0.declassify() < 15 {
                let try_0 = try_0.as_i32();

                // (try_0 * 26) >> 7 computes ⌊try_0 / 5⌋
                let try_0_mod_5 = try_0 - ((try_0 * 26) >> 7) * 5;

                out[sampled] = 2.classify() - try_0_mod_5;

                sampled += 1;
            }

            // Declassification: This reveals only the index of the
            // coefficient that was sampled.
            if try_1.declassify() < 15 {
                let try_1 = try_1.as_i32();
                let try_1_mod_5 = try_1 - ((try_1 * 26) >> 7) * 5;

                out[sampled] = 2.classify() - try_1_mod_5;

                sampled += 1;
            }
        }
    }

    sampled
}

#[inline(always)]
pub fn rejection_sample_less_than_eta_equals_4(randomness: &[U8], out: &mut [I32]) -> usize {
    let mut sampled = 0;

    cloop! {
        for byte in randomness.iter() {
            let try_0 = *byte & 0xF;
            let try_1 = *byte >> 4;

            // Declassification: This reveals only the index of the
            // coefficient that was sampled.
            if try_0.declassify() < 9 {
                out[sampled] = 4.classify() - (try_0.as_i32());
                sampled += 1;
            }

            // Declassification: This reveals only the index of the
            // coefficient that was sampled.
            if try_1.declassify() < 9 {
                out[sampled] = 4.classify() - (try_1.as_i32());
                sampled += 1;
            }
        }
    }

    sampled
}
