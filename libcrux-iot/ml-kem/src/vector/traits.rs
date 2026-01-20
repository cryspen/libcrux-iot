use libcrux_secrets::{I16, I32, U8};

pub const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;
pub const FIELD_MODULUS: i16 = 3329;
pub const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const BARRETT_SHIFT: i32 = 26;
pub const BARRETT_R: i32 = 1 << BARRETT_SHIFT;

// We define a trait that allows us to talk about the contents of a vector.
// This is used extensively in pre- and post-conditions to reason about the code.
// The trait is duplicated for Eurydice to avoid the trait inheritance between Operations and Repr
// This is needed because of this issue: https://github.com/AeneasVerif/eurydice/issues/111
#[cfg(hax)]
#[hax_lib::attributes]
pub trait Repr: Copy + Clone {
    #[requires(true)]
    fn repr(&self) -> [i16; 16];
}

#[cfg(any(eurydice, not(hax)))]
pub trait Repr {}

#[hax_lib::attributes]
pub trait Operations: Copy + Clone + Repr {
    #[requires(true)]
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    #[requires(array.len() == 16)]
    fn from_i16_array(array: &[I16], out: &mut Self);

    #[requires(out.len() == 16)]
    #[cfg(hax)]
    fn to_i16_array(x: &Self, out: &mut [i16]);

    #[requires(array.len() == 16)]
    fn reducing_from_i32_array(array: &[I32], out: &mut Self);

    // Basic arithmetic
    #[requires(true)]
    fn add(lhs: &mut Self, rhs: &Self);

    #[requires(true)]
    fn sub(lhs: &mut Self, rhs: &Self);

    #[requires(true)]
    fn negate(vec: &mut Self);

    #[requires(true)]
    fn multiply_by_constant(vec: &mut Self, c: i16);

    // Bitwise operations
    #[requires(true)]
    fn bitwise_and_with_constant(vec: &mut Self, c: i16);

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    fn shift_right<const SHIFT_BY: i32>(vec: &mut Self);

    // Modular operations
    #[requires(true)]
    fn cond_subtract_3329(vec: &mut Self);

    #[requires(true)]
    fn barrett_reduce(vec: &mut Self);

    #[requires(true)]
    fn montgomery_multiply_by_constant(vec: &mut Self, c: i16);

    // Compression
    #[requires(true)]
    fn compress_1(vec: &mut Self);

    #[requires(COEFFICIENT_BITS >= 0 && COEFFICIENT_BITS <= 16)]
    fn compress<const COEFFICIENT_BITS: i32>(vec: &mut Self);

    #[requires(0 <= COEFFICIENT_BITS && COEFFICIENT_BITS < 31)]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(vec: &mut Self);

    // NTT
    #[requires(true)]
    fn ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16);
    #[requires(true)]
    fn ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16);
    #[requires(true)]
    fn ntt_layer_3_step(a: &mut Self, zeta: i16);

    #[requires(true)]
    fn inv_ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16);
    #[requires(true)]
    fn inv_ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16);
    #[requires(true)]
    fn inv_ntt_layer_3_step(a: &mut Self, zeta: i16);

    #[requires(out.len() >= 16)]
    #[ensures(|_| future(out).len() == out.len())]
    fn accumulating_ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        out: &mut [I32],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    );

    #[requires(out.len() >= 16)]
    #[ensures(|_| future(out).len() == out.len())]
    fn accumulating_ntt_multiply_fill_cache(
        lhs: &Self,
        rhs: &Self,
        out: &mut [I32],
        cache: &mut Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    );

    #[requires(out.len() >= 16)]
    #[ensures(|_| future(out).len() == out.len())]
    fn accumulating_ntt_multiply_use_cache(lhs: &Self, rhs: &Self, out: &mut [I32], cache: &Self);

    // Serialization and deserialization
    #[requires(out.len() == 2)]
    #[ensures(|_| future(out).len() == 2)]
    fn serialize_1(a: &Self, out: &mut [U8]);
    #[requires(a.len() == 2)]
    fn deserialize_1(a: &[U8], out: &mut Self);

    #[requires(out.len() == 8)]
    #[ensures(|_| future(out).len() == 8)]
    fn serialize_4(a: &Self, out: &mut [u8]);
    #[requires(a.len() == 8)]
    fn deserialize_4(a: &[u8], out: &mut Self);

    #[requires(out.len() == 10)]
    #[ensures(|_| future(out).len() == 10)]
    fn serialize_5(a: &Self, out: &mut [u8]);
    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8], out: &mut Self);

    #[requires(out.len() == 20)]
    #[ensures(|_| future(out).len() == 20)]
    fn serialize_10(a: &Self, out: &mut [u8]);
    #[requires(a.len() == 20)]
    fn deserialize_10(a: &[u8], out: &mut Self);

    #[requires(out.len() == 22)]
    #[ensures(|_| future(out).len() == 22)]
    fn serialize_11(a: &Self, out: &mut [u8]);
    #[requires(a.len() == 22)]
    fn deserialize_11(a: &[u8], out: &mut Self);

    #[requires(out.len() == 24)]
    #[ensures(|_| future(out).len() == 24)]
    fn serialize_12(a: &Self, out: &mut [U8]);
    #[requires(a.len() == 24)]
    fn deserialize_12(a: &[U8], out: &mut Self);

    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result| result <= 16 && future(out).len() == 16)]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize;
}

// hax does not support trait with default implementations, so we use the following pattern
#[inline(always)]
pub fn montgomery_multiply_fe<T: Operations>(v: &mut T, fer: i16) {
    T::montgomery_multiply_by_constant(v, fer)
}

#[inline(always)]
pub fn to_standard_domain<T: Operations>(v: &mut T) {
    T::montgomery_multiply_by_constant(v, MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS as i16)
}

#[inline(always)]
pub fn to_unsigned_representative<T: Operations>(a: &T, out: &mut T) {
    *out = *a; // XXX: We need a copy of `a` here. At least
               // the allocation becomes apparent on the
               // outside.
    T::shift_right::<15>(out);
    T::bitwise_and_with_constant(out, FIELD_MODULUS);
    T::add(out, a)
}

#[inline(always)]
pub fn decompress_1<T: Operations>(vec: &mut T) {
    T::negate(vec);
    T::bitwise_and_with_constant(vec, 1665);
}
