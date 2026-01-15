use super::Operations;
use libcrux_secrets::*;

mod arithmetic;
mod compress;
mod ntt;
mod sampling;
mod serialize;
mod vector_type;

use arithmetic::*;
use compress::*;
use ntt::*;
use sampling::*;
use serialize::*;
use vector_type::*;

pub(crate) use vector_type::PortableVector;

#[cfg(hax)]
impl crate::vector::traits::Repr for PortableVector {
    fn repr(&self) -> [i16; 16] {
        let mut out = [0i16; 16];
        to_i16_array(self, &mut out);
        out
    }
}

#[cfg(any(eurydice, not(hax)))]
impl crate::vector::traits::Repr for PortableVector {}

#[hax_lib::attributes]
impl Operations for PortableVector {
    #[inline(always)]
    fn ZERO() -> Self {
        zero()
    }

    #[requires(array.len() == 16)]
    #[inline(always)]
    fn from_i16_array(array: &[I16], out: &mut Self) {
        from_i16_array(array, out)
    }

    #[requires(array.len() == 16)]
    #[inline(always)]
    fn reducing_from_i32_array(array: &[I32], out: &mut Self) {
        reducing_from_i32_array(array, out)
    }

    #[inline(always)]
    fn add(lhs: &mut Self, rhs: &Self) {
        add(lhs, rhs)
    }

    #[inline(always)]
    fn sub(lhs: &mut Self, rhs: &Self) {
        sub(lhs, rhs)
    }

    #[inline(always)]
    fn negate(vec: &mut Self) {
        negate(vec)
    }

    #[inline(always)]
    fn multiply_by_constant(vec: &mut Self, c: i16) {
        multiply_by_constant(vec, c)
    }

    #[inline(always)]
    fn bitwise_and_with_constant(vec: &mut Self, c: i16) {
        bitwise_and_with_constant(vec, c)
    }

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[inline(always)]
    fn shift_right<const SHIFT_BY: i32>(vec: &mut Self) {
        shift_right::<{ SHIFT_BY }>(vec)
    }

    #[inline(always)]
    fn cond_subtract_3329(vec: &mut Self) {
        cond_subtract_3329(vec)
    }

    #[inline(always)]
    fn barrett_reduce(vec: &mut Self) {
        barrett_reduce(vec)
    }

    #[inline(always)]
    fn montgomery_multiply_by_constant(vec: &mut Self, r: i16) {
        montgomery_multiply_by_constant(vec, r.classify())
    }

    #[inline(always)]
    fn compress_1(a: &mut Self) {
        compress_1(a)
    }

    #[requires(COEFFICIENT_BITS >= 0 && COEFFICIENT_BITS <= 16)]
    #[inline(always)]
    fn compress<const COEFFICIENT_BITS: i32>(a: &mut Self) {
        compress::<COEFFICIENT_BITS>(a)
    }

    #[requires(0 <= COEFFICIENT_BITS && COEFFICIENT_BITS < 31)]
    #[inline(always)]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(a: &mut Self) {
        decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(a)
    }

    #[inline(always)]
    fn ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) {
        ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    #[inline(always)]
    fn ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16) {
        ntt_layer_2_step(a, zeta0, zeta1)
    }

    #[inline(always)]
    fn ntt_layer_3_step(a: &mut Self, zeta: i16) {
        ntt_layer_3_step(a, zeta)
    }

    #[inline(always)]
    fn inv_ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) {
        inv_ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    #[inline(always)]
    fn inv_ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16) {
        inv_ntt_layer_2_step(a, zeta0, zeta1)
    }

    #[inline(always)]
    fn inv_ntt_layer_3_step(a: &mut Self, zeta: i16) {
        inv_ntt_layer_3_step(a, zeta)
    }

    #[requires(out.len() >= 16)]
    #[ensures(|_| future(out).len() == out.len())]
    #[inline(always)]
    fn accumulating_ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        out: &mut [I32],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) {
        accumulating_ntt_multiply(lhs, rhs, out, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(out.len() >= 16)]
    #[ensures(|_| future(out).len() == out.len())]
    #[inline(always)]
    fn accumulating_ntt_multiply_fill_cache(
        lhs: &Self,
        rhs: &Self,
        out: &mut [I32],
        cache: &mut Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) {
        accumulating_ntt_multiply_fill_cache(lhs, rhs, out, cache, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(out.len() >= 16)]
    #[ensures(|_| future(out).len() == out.len())]
    #[inline(always)]
    fn accumulating_ntt_multiply_use_cache(lhs: &Self, rhs: &Self, out: &mut [I32], cache: &Self) {
        accumulating_ntt_multiply_use_cache(lhs, rhs, out, cache)
    }

    #[requires(out.len() == 2)]
    #[ensures(|_| future(out).len() == 2)]
    #[inline(always)]
    fn serialize_1(a: &Self, out: &mut [U8]) {
        serialize_1(a, out)
    }

    #[requires(a.len() == 2)]
    #[inline(always)]
    fn deserialize_1(a: &[U8], out: &mut Self) {
        deserialize_1(a, out)
    }

    #[requires(out.len() == 8)]
    #[ensures(|_| future(out).len() == 8)]
    #[inline(always)]
    fn serialize_4(a: &Self, out: &mut [u8]) {
        serialize_4(a, out)
    }

    #[requires(a.len() == 8)]
    #[inline(always)]
    fn deserialize_4(a: &[u8], out: &mut Self) {
        deserialize_4(a.classify_ref(), out)
    }

    #[inline(always)]
    #[requires(out.len() == 10)]
    #[ensures(|_| future(out).len() == 10)]
    fn serialize_5(a: &Self, out: &mut [u8]) {
        serialize_5(a, out)
    }

    #[requires(a.len() == 10)]
    #[inline(always)]
    fn deserialize_5(a: &[u8], out: &mut Self) {
        deserialize_5(a.classify_ref(), out)
    }

    #[requires(out.len() == 20)]
    #[ensures(|_| future(out).len() == 20)]
    #[inline(always)]
    fn serialize_10(a: &Self, out: &mut [u8]) {
        serialize_10(a, out)
    }

    #[requires(a.len() == 20)]
    #[inline(always)]
    fn deserialize_10(a: &[u8], out: &mut Self) {
        deserialize_10(a.classify_ref(), out)
    }

    #[requires(out.len() == 22)]
    #[ensures(|_| future(out).len() == 22)]
    #[inline(always)]
    fn serialize_11(a: &Self, out: &mut [u8]) {
        serialize_11(a, out)
    }

    #[requires(a.len() == 22)]
    #[inline(always)]
    fn deserialize_11(a: &[u8], out: &mut Self) {
        deserialize_11(a.classify_ref(), out)
    }

    #[requires(out.len() == 24)]
    #[ensures(|_| future(out).len() == 24)]
    #[inline(always)]
    fn serialize_12(a: &Self, out: &mut [U8]) {
        serialize_12(a, out)
    }

    #[requires(a.len() == 24)]
    #[inline(always)]
    fn deserialize_12(a: &[U8], out: &mut Self) {
        deserialize_12(a, out)
    }

    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result| result <= 16 && future(out).len() == 16)]
    #[inline(always)]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize {
        rej_sample(a, out)
    }
}
