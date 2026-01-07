//! # Spec Functions
//!
//! This module implements general purpose spec helpers.

/// -bound <= x <= bound
pub(crate) fn bounded_i32(x: i32, bound: i32) -> bool {
    bound >= 0 && x >= -bound && x <= bound
}

/// -bound <= x <= bound
pub(crate) fn bounded_i16(x: i16, bound: i16) -> bool {
    bound >= 0 && x >= -bound && x <= bound
}

pub(crate) fn bounded_i16x16(x: &[i16; 16], b: i16) -> bool {
    bounded_i16(x[0], b)
        && bounded_i16(x[1], b)
        && bounded_i16(x[2], b)
        && bounded_i16(x[3], b)
        && bounded_i16(x[4], b)
        && bounded_i16(x[5], b)
        && bounded_i16(x[6], b)
        && bounded_i16(x[7], b)
        && bounded_i16(x[8], b)
        && bounded_i16(x[9], b)
        && bounded_i16(x[10], b)
        && bounded_i16(x[11], b)
        && bounded_i16(x[12], b)
        && bounded_i16(x[13], b)
        && bounded_i16(x[14], b)
        && bounded_i16(x[15], b)
}
