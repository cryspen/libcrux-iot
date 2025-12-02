/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 637a6bc8a4c2a79875af5aa4e413c7ef3aa7f391
 * Eurydice: 5ca42bdb4309a18e332321ca9ae66607824428eb
 * Karamel: 4e64d915da3c172d1dfad805b8e1a46beff938bc
 * F*: unset
 * Libcrux: 1bf38a701c22669699956643df22dd9ff22c0456
 */

#include "internal/libcrux_iot_core.h"

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t classify_27_de(uint16_t self) { return self; }

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_declassify_d8_90(uint8_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE uint16_t as_u16_59(uint8_t self) {
  return classify_27_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_classify_27_90(uint8_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t declassify_d8_de(uint16_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE uint8_t as_u8_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)declassify_d8_de(self));
}

/**
 Return 1 if `value` is not zero and 0 otherwise.
*/
static KRML_NOINLINE uint8_t inz(uint8_t value) {
  uint16_t value0 = as_u16_59(value);
  uint8_t result =
      as_u8_ca((uint32_t)core_num__u16__wrapping_add(~value0, 1U) >> 8U);
  return (uint32_t)result & 1U;
}

static KRML_NOINLINE uint8_t is_non_zero(uint8_t value) { return inz(value); }

/**
 Return 1 if the bytes of `lhs` and `rhs` do not exactly
 match and 0 otherwise.
*/
static KRML_NOINLINE uint8_t compare(Eurydice_borrow_slice_u8 lhs,
                                     Eurydice_borrow_slice_u8 rhs) {
  uint8_t r = libcrux_secrets_int_public_integers_classify_27_90(0U);
  for (size_t i = (size_t)0U; i < lhs.meta; i++) {
    size_t i0 = i;
    uint8_t nr = (uint32_t)r | ((uint32_t)lhs.ptr[i0] ^ (uint32_t)rhs.ptr[i0]);
    r = nr;
  }
  return is_non_zero(r);
}

static KRML_NOINLINE uint8_t compare_ciphertexts_in_constant_time(
    Eurydice_borrow_slice_u8 lhs, Eurydice_borrow_slice_u8 rhs) {
  return compare(lhs, rhs);
}

/**
 If `selector` is not zero, return the bytes in `rhs`; return the bytes in
 `lhs` otherwise.
*/
static KRML_NOINLINE void select_ct(Eurydice_borrow_slice_u8 lhs,
                                    Eurydice_borrow_slice_u8 rhs,
                                    uint8_t selector,
                                    Eurydice_mut_borrow_slice_u8 out) {
  uint8_t mask = core_num__u8__wrapping_sub(is_non_zero(selector), 1U);
  for (size_t i = (size_t)0U; i < lhs.meta; i++) {
    size_t i0 = i;
    uint8_t outi = ((uint32_t)lhs.ptr[i0] & (uint32_t)mask) |
                   ((uint32_t)rhs.ptr[i0] & (uint32_t)~mask);
    out.ptr[i0] = outi;
  }
}

static KRML_NOINLINE void select_shared_secret_in_constant_time(
    Eurydice_borrow_slice_u8 lhs, Eurydice_borrow_slice_u8 rhs,
    uint8_t selector, Eurydice_mut_borrow_slice_u8 out) {
  select_ct(lhs, rhs, selector, out);
}

KRML_NOINLINE void
libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_borrow_slice_u8 lhs_c, Eurydice_borrow_slice_u8 rhs_c,
    Eurydice_borrow_slice_u8 lhs_s, Eurydice_borrow_slice_u8 rhs_s,
    Eurydice_mut_borrow_slice_u8 out) {
  uint8_t selector = compare_ciphertexts_in_constant_time(lhs_c, rhs_c);
  select_shared_secret_in_constant_time(lhs_s, rhs_s, selector, out);
}

/**
 K * BITS_PER_RING_ELEMENT / 8

 [eurydice] Note that we can't use const generics here because that breaks
            C extraction with eurydice.
*/
size_t libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(size_t rank) {
  return rank * LIBCRUX_IOT_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t classify_27_49(uint64_t self) { return self; }

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t declassify_d8_df(uint32_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
uint64_t libcrux_secrets_int_as_u64_b8(uint32_t self) {
  return classify_27_49((uint64_t)declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t

*/
uint32_t libcrux_secrets_int_public_integers_classify_27_df(uint32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t declassify_d8_49(uint64_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
uint32_t libcrux_secrets_int_as_u32_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_classify_27_39(int16_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int16_t libcrux_secrets_int_as_i16_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int32_t

*/
static KRML_MUSTINLINE int32_t declassify_d8_a8(int32_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
int16_t libcrux_secrets_int_as_i16_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int32_t

*/
int32_t libcrux_secrets_int_public_integers_classify_27_a8(int32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_declassify_d8_39(int16_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int32_t libcrux_secrets_int_as_i32_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int32_t libcrux_secrets_int_as_i32_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      (int32_t)declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
int16_t libcrux_secrets_int_as_i16_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint8_t libcrux_secrets_int_as_u8_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint16_t libcrux_secrets_int_as_u16_f5(int16_t self) {
  return classify_27_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
int16_t libcrux_secrets_int_as_i16_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
uint64_t libcrux_secrets_int_as_u64_ca(uint16_t self) {
  return classify_27_49((uint64_t)declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int16_t libcrux_secrets_int_as_i16_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_6e1(
    const Eurydice_arr_00 *a, size_t r) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = r;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 3168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_3612(
    const Eurydice_arr_17 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_18
with const generics
- SIZE= 1568
*/
Eurydice_arr_00 libcrux_iot_ml_kem_types_from_18_af(Eurydice_arr_00 value) {
  return value;
}

/**
This function found in impl
{libcrux_iot_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_d9
with const generics
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_f7 libcrux_iot_ml_kem_types_from_d9_94(
    Eurydice_arr_17 sk, Eurydice_arr_00 pk) {
  return (KRML_CLITERAL(libcrux_iot_ml_kem_types_MlKemKeyPair_f7){.sk = sk,
                                                                  .pk = pk});
}

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_56
with const generics
- SIZE= 3168
*/
Eurydice_arr_17 libcrux_iot_ml_kem_types_from_56_39(Eurydice_arr_17 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1536
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_c9(
    const Eurydice_arr_38 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1536U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 3168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_368(
    Eurydice_arr_17 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1536
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_c9(
    Eurydice_arr_38 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1536U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_e5 Eurydice_array_to_slice_mut_302(Eurydice_arr_e00 *a) {
  Eurydice_dst_ref_mut_e5 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_06 Eurydice_array_to_slice_mut_4d(Eurydice_arr_33 *a) {
  Eurydice_dst_ref_mut_06 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_cc Eurydice_array_to_slice_shared_c72(
    const Eurydice_arr_c5 *a) {
  Eurydice_dst_ref_shared_cc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_a1 Eurydice_array_to_slice_shared_e72(
    const Eurydice_arr_b3 *a) {
  Eurydice_dst_ref_shared_a1 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_a1 Eurydice_array_to_slice_mut_e72(Eurydice_arr_b3 *a) {
  Eurydice_dst_ref_mut_a1 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_1a Eurydice_array_to_slice_shared_e92(
    const Eurydice_arr_e0 *a) {
  Eurydice_dst_ref_shared_1a lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_1a Eurydice_array_to_slice_mut_e92(Eurydice_arr_e0 *a) {
  Eurydice_dst_ref_mut_1a lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_9d
with const generics
- SIZE= 1568
*/
Eurydice_arr_00 libcrux_iot_ml_kem_types_from_9d_af(Eurydice_arr_00 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_4e(
    const Eurydice_arr_00 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1568U;
  return lit;
}

/**
This function found in impl {libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.as_slice_63
with const generics
- SIZE= 1568
*/
const Eurydice_arr_00 *libcrux_iot_ml_kem_types_as_slice_63_af(
    const Eurydice_arr_00 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1568
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_4e(
    Eurydice_arr_00 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1568U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 512
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_3611(
    const Eurydice_arr_0b *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 512
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_44(
    Eurydice_arr_0b *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)512U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_de Eurydice_array_to_slice_shared_612(
    const Eurydice_arr_d5 *a) {
  Eurydice_dst_ref_shared_de lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.utils.prf_input_inc
with const generics
- K= 4
*/
uint8_t libcrux_iot_ml_kem_utils_prf_input_inc_ac(Eurydice_arr_d5 *prf_inputs,
                                                  uint8_t domain_separator) {
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    prf_inputs->data[i0].data[32U] =
        libcrux_secrets_int_public_integers_classify_27_90(domain_separator);
    domain_separator = (uint32_t)domain_separator + 1U;
  }
  return domain_separator;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1600
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_8e(
    const Eurydice_arr_e7 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1600U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1568size_t]]

*/
Eurydice_arr_00 libcrux_secrets_int_public_integers_classify_27_b7(
    Eurydice_arr_00 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1600
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_8c2(
    Eurydice_arr_e7 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){
      .ptr = a->data + r, .meta = (size_t)1600U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1600
*/
static Eurydice_mut_borrow_slice_u8 array_to_subslice_mut_367(
    Eurydice_arr_e7 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
Eurydice_arr_e7 libcrux_iot_ml_kem_utils_into_padded_array_7f(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_e7 out;
  uint8_t repeat_expression[1600U];
  for (size_t i = (size_t)0U; i < (size_t)1600U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)1600U * sizeof(uint8_t));
  Eurydice_slice_copy(array_to_subslice_mut_367(
                          &out, (KRML_CLITERAL(core_ops_range_Range_08){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c4(
    const Eurydice_arr_00 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)1568U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_3610(
    const Eurydice_arr_00 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 3168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_a6(
    const Eurydice_arr_17 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3168U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.declassify_ref_7f
with types uint8_t

*/
Eurydice_borrow_slice_u8
libcrux_secrets_int_classify_public_declassify_ref_7f_90(
    Eurydice_borrow_slice_u8 self) {
  return self;
}

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_borrow_slice_u8_x4 libcrux_iot_ml_kem_types_unpack_private_key_1f(
    Eurydice_borrow_slice_u8 private_key) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)1536U, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_secret_key = uu____0.fst;
  Eurydice_borrow_slice_u8 secret_key0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1568U, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_public_key = uu____1.fst;
  Eurydice_borrow_slice_u8 secret_key = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 implicit_rejection_value = uu____2.snd;
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8_x4){
      .fst = ind_cpa_secret_key,
      .snd = libcrux_secrets_int_classify_public_declassify_ref_7f_90(
          ind_cpa_public_key),
      .thd = libcrux_secrets_int_classify_public_declassify_ref_7f_90(
          ind_cpa_public_key_hash),
      .f3 = implicit_rejection_value});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c3(
    const Eurydice_arr_74 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)1184U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_6e0(
    const Eurydice_arr_74 *a, size_t r) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = r;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 2400
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_369(
    const Eurydice_arr_ea *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_18
with const generics
- SIZE= 1184
*/
Eurydice_arr_74 libcrux_iot_ml_kem_types_from_18_d0(Eurydice_arr_74 value) {
  return value;
}

/**
This function found in impl
{libcrux_iot_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_d9
with const generics
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_5f libcrux_iot_ml_kem_types_from_d9_74(
    Eurydice_arr_ea sk, Eurydice_arr_74 pk) {
  return (KRML_CLITERAL(libcrux_iot_ml_kem_types_MlKemKeyPair_5f){.sk = sk,
                                                                  .pk = pk});
}

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_56
with const generics
- SIZE= 2400
*/
Eurydice_arr_ea libcrux_iot_ml_kem_types_from_56_28(Eurydice_arr_ea value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1152
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_06(
    const Eurydice_arr_60 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1152U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 2400
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_366(
    Eurydice_arr_ea *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1184
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_45(
    Eurydice_arr_74 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1184U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1152
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_06(
    Eurydice_arr_60 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1152U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_e5 Eurydice_array_to_slice_mut_301(Eurydice_arr_ed *a) {
  Eurydice_dst_ref_mut_e5 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_06 Eurydice_array_to_slice_mut_92(Eurydice_arr_c8 *a) {
  Eurydice_dst_ref_mut_06 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_cc Eurydice_array_to_slice_shared_c71(
    const Eurydice_arr_c30 *a) {
  Eurydice_dst_ref_shared_cc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_a1 Eurydice_array_to_slice_shared_e71(
    const Eurydice_arr_7e *a) {
  Eurydice_dst_ref_shared_a1 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_a1 Eurydice_array_to_slice_mut_e71(Eurydice_arr_7e *a) {
  Eurydice_dst_ref_mut_a1 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_1a Eurydice_array_to_slice_shared_e91(
    const Eurydice_arr_55 *a) {
  Eurydice_dst_ref_shared_1a lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_1a Eurydice_array_to_slice_mut_e91(Eurydice_arr_55 *a) {
  Eurydice_dst_ref_mut_1a lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_9d
with const generics
- SIZE= 1088
*/
Eurydice_arr_2c libcrux_iot_ml_kem_types_from_9d_80(Eurydice_arr_2c value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_45(
    const Eurydice_arr_74 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1184U;
  return lit;
}

/**
This function found in impl {libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.as_slice_63
with const generics
- SIZE= 1184
*/
const Eurydice_arr_74 *libcrux_iot_ml_kem_types_as_slice_63_d0(
    const Eurydice_arr_74 *self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1184size_t]]

*/
Eurydice_arr_74 libcrux_secrets_int_public_integers_classify_27_aa(
    Eurydice_arr_74 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1088
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_42(
    Eurydice_arr_2c *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1088U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_de Eurydice_array_to_slice_shared_611(
    const Eurydice_arr_45 *a) {
  Eurydice_dst_ref_shared_de lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.utils.prf_input_inc
with const generics
- K= 3
*/
uint8_t libcrux_iot_ml_kem_utils_prf_input_inc_e0(Eurydice_arr_45 *prf_inputs,
                                                  uint8_t domain_separator) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    prf_inputs->data[i0].data[32U] =
        libcrux_secrets_int_public_integers_classify_27_90(domain_separator);
    domain_separator = (uint32_t)domain_separator + 1U;
  }
  return domain_separator;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1120
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_74(
    const Eurydice_arr_480 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1120U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1088size_t]]

*/
Eurydice_arr_2c libcrux_secrets_int_public_integers_classify_27_33(
    Eurydice_arr_2c self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1120
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_8c1(
    Eurydice_arr_480 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){
      .ptr = a->data + r, .meta = (size_t)1120U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1120
*/
static Eurydice_mut_borrow_slice_u8 array_to_subslice_mut_365(
    Eurydice_arr_480 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
Eurydice_arr_480 libcrux_iot_ml_kem_utils_into_padded_array_15(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_480 out;
  uint8_t repeat_expression[1120U];
  for (size_t i = (size_t)0U; i < (size_t)1120U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)1120U * sizeof(uint8_t));
  Eurydice_slice_copy(array_to_subslice_mut_365(
                          &out, (KRML_CLITERAL(core_ops_range_Range_08){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1088
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c2(
    const Eurydice_arr_2c *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)1088U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1088
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_368(
    const Eurydice_arr_2c *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2400
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ec(
    const Eurydice_arr_ea *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2400U;
  return lit;
}

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_borrow_slice_u8_x4 libcrux_iot_ml_kem_types_unpack_private_key_b4(
    Eurydice_borrow_slice_u8 private_key) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)1152U, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_secret_key = uu____0.fst;
  Eurydice_borrow_slice_u8 secret_key0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1184U, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_public_key = uu____1.fst;
  Eurydice_borrow_slice_u8 secret_key = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 implicit_rejection_value = uu____2.snd;
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8_x4){
      .fst = ind_cpa_secret_key,
      .snd = libcrux_secrets_int_classify_public_declassify_ref_7f_90(
          ind_cpa_public_key),
      .thd = libcrux_secrets_int_classify_public_declassify_ref_7f_90(
          ind_cpa_public_key_hash),
      .f3 = implicit_rejection_value});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_363(
    Eurydice_arr_48 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
Eurydice_arr_48 libcrux_iot_ml_kem_utils_into_padded_array_b6(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_48 out;
  uint8_t repeat_expression[34U];
  for (size_t i = (size_t)0U; i < (size_t)34U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)34U * sizeof(uint8_t));
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_363(
                          &out, (KRML_CLITERAL(core_ops_range_Range_08){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$34size_t]]

*/
Eurydice_arr_48 libcrux_secrets_int_public_integers_declassify_d8_2c(
    Eurydice_arr_48 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types int16_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
int16_t with const generics
- N= 272
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_subslice_to_shared_11(
    const Eurydice_arr_a0 *a, size_t r) {
  Eurydice_borrow_slice_i16 lit;
  lit.ptr = a->data;
  lit.meta = r;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types int16_t

*/
Eurydice_borrow_slice_i16
libcrux_secrets_int_classify_public_classify_ref_9b_39(
    Eurydice_borrow_slice_i16 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c0(
    const Eurydice_arr_06 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)64U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_366(
    const Eurydice_arr_06 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_from_mut_6b(
    Eurydice_mut_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = s.ptr + r,
                                                      .meta = s.meta - r});
}

/**
A monomorphic instance of Eurydice.slice_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_to_shared_c6(
    Eurydice_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr, .meta = r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_365(
    const Eurydice_arr_600 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_from_shared_6b(
    Eurydice_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr + r,
                                                  .meta = s.meta - r});
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$272size_t]]

*/
Eurydice_arr_a0 libcrux_secrets_int_public_integers_classify_27_9a(
    Eurydice_arr_a0 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_e5 Eurydice_array_to_slice_mut_30(Eurydice_arr_0a *a) {
  Eurydice_dst_ref_mut_e5 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_06 Eurydice_array_to_slice_mut_26(Eurydice_arr_e4 *a) {
  Eurydice_dst_ref_mut_06 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_cc Eurydice_array_to_slice_shared_c7(
    const Eurydice_arr_9e *a) {
  Eurydice_dst_ref_shared_cc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_a1 Eurydice_array_to_slice_shared_e7(
    const Eurydice_arr_3a *a) {
  Eurydice_dst_ref_shared_a1 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_364(
    const Eurydice_arr_27 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_a1 Eurydice_array_to_slice_mut_e7(Eurydice_arr_3a *a) {
  Eurydice_dst_ref_mut_a1 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_1a Eurydice_array_to_slice_shared_e9(
    const Eurydice_arr_19 *a) {
  Eurydice_dst_ref_shared_1a lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 272
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_subslice_mut_85(
    Eurydice_arr_a0 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_i16){
      .ptr = a->data + r.start, .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 504
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_363(
    const Eurydice_arr_b0 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_1a Eurydice_array_to_slice_mut_e9(Eurydice_arr_19 *a) {
  Eurydice_dst_ref_mut_1a lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 128
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_18(
    const Eurydice_arr_d1 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)128U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 128
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_18(
    Eurydice_arr_d1 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)128U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 33
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_610(
    const Eurydice_arr_3e *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)33U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int16_t
with const generics
- N= 256
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_slice_shared_1a(
    const Eurydice_arr_c1 *a) {
  Eurydice_borrow_slice_i16 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)256U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int16_t
with const generics
- N= 256
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_slice_mut_1a(
    Eurydice_arr_c1 *a) {
  Eurydice_mut_borrow_slice_i16 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)256U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 384
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_361(
    const Eurydice_arr_cc *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 384
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_fe(
    Eurydice_arr_cc *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)384U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 33
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_362(
    Eurydice_arr_3e *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
Eurydice_arr_3e libcrux_iot_ml_kem_utils_into_padded_array_c8(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_3e out;
  uint8_t repeat_expression[33U];
  for (size_t i = (size_t)0U; i < (size_t)33U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)33U * sizeof(uint8_t));
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_362(
                          &out, (KRML_CLITERAL(core_ops_range_Range_08){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_d8(
    const Eurydice_arr_06 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)64U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 64
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_8c(
    Eurydice_arr_06 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r,
                                                      .meta = (size_t)64U - r});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_6e(
    const Eurydice_arr_600 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)32U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 64
*/
static Eurydice_mut_borrow_slice_u8 array_to_subslice_mut_360(
    Eurydice_arr_06 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
Eurydice_arr_06 libcrux_iot_ml_kem_utils_into_padded_array_24(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_06 out;
  uint8_t repeat_expression[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)64U * sizeof(uint8_t));
  Eurydice_slice_copy(array_to_subslice_mut_360(
                          &out, (KRML_CLITERAL(core_ops_range_Range_08){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_20(
    const Eurydice_arr_c3 *a) {
  Eurydice_dst_ref_shared_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)256U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t

*/
Eurydice_dst_ref_shared_fc Eurydice_slice_subslice_shared_46(
    Eurydice_dst_ref_shared_fc s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = s.ptr + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_mut_fc Eurydice_array_to_subslice_mut_7f(
    Eurydice_arr_c3 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_mut_fc){.ptr = a->data + r.start,
                                                 .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 16
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_subslice_shared_85(
    const Eurydice_arr_e2 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_i16){.ptr = a->data + r.start,
                                                   .meta = r.end - r.start});
}

/**
 Classify a mutable slice (identity)
 We define a separate function for this because hax has limited support for
 &mut-returning functions
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_mut_slice
with types Eurydice_dst_ref_mut uint8_t size_t

*/
Eurydice_mut_borrow_slice_u8
libcrux_secrets_int_public_integers_classify_mut_slice_47(
    Eurydice_mut_borrow_slice_u8 x) {
  return x;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr int16_t[[$16size_t]]

*/
Eurydice_arr_e2 libcrux_secrets_int_public_integers_declassify_d8_3a(
    Eurydice_arr_e2 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int16_t
with const generics
- N= 16
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_slice_shared_b4(
    const Eurydice_arr_e2 *a) {
  Eurydice_borrow_slice_i16 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_mut
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t

*/
Eurydice_mut_borrow_slice_i16 Eurydice_slice_subslice_mut_76(
    Eurydice_mut_borrow_slice_i16 s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_i16){
      .ptr = s.ptr + r.start, .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t

*/
Eurydice_borrow_slice_i16 Eurydice_slice_subslice_shared_76(
    Eurydice_borrow_slice_i16 s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_i16){.ptr = s.ptr + r.start,
                                                   .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int16_t
with const generics
- N= 16
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_slice_mut_b4(
    Eurydice_arr_e2 *a) {
  Eurydice_mut_borrow_slice_i16 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$16size_t]]

*/
Eurydice_arr_e2 libcrux_secrets_int_public_integers_classify_27_3a(
    Eurydice_arr_e2 self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::ClassifyRefMut<&'a mut
(T)> for &'a mut (T)}
*/
/**
A monomorphic instance of
libcrux_secrets.int.classify_public.classify_ref_mut_a1 with types
Eurydice_dst_ref_mut uint8_t size_t

*/
Eurydice_mut_borrow_slice_u8 *
libcrux_secrets_int_classify_public_classify_ref_mut_a1_47(
    Eurydice_mut_borrow_slice_u8 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 34
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_8d(
    const Eurydice_arr_48 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)34U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 64
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_d8(
    Eurydice_arr_06 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)64U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$64size_t]]

*/
Eurydice_arr_06 libcrux_secrets_int_public_integers_classify_27_490(
    Eurydice_arr_06 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 48
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_95(
    Eurydice_arr_5f *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)48U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$48size_t]]

*/
Eurydice_arr_5f libcrux_secrets_int_public_integers_classify_27_7d(
    Eurydice_arr_5f self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 32
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_6e(
    Eurydice_arr_600 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)32U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$32size_t]]

*/
Eurydice_arr_600 libcrux_secrets_int_public_integers_classify_27_62(
    Eurydice_arr_600 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 28
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_c0(
    Eurydice_arr_f1 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)28U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$28size_t]]

*/
Eurydice_arr_f1 libcrux_secrets_int_public_integers_classify_27_4b(
    Eurydice_arr_f1 self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types uint8_t

*/
Eurydice_borrow_slice_u8 libcrux_secrets_int_classify_public_classify_ref_9b_90(
    Eurydice_borrow_slice_u8 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_36(
    const Eurydice_arr_88 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f7(
    Eurydice_arr_88 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)200U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_60(
    const Eurydice_array_u8x4 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_mut_7e(
    Eurydice_mut_borrow_slice_u8 s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = s.ptr + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f7(
    const Eurydice_arr_88 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)200U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_36(
    Eurydice_arr_88 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$200size_t]]

*/
Eurydice_arr_88 libcrux_secrets_int_public_integers_classify_27_c1(
    Eurydice_arr_88 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_shared_7e(
    Eurydice_borrow_slice_u8 s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr + r.start,
                                                  .meta = r.end - r.start});
}

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$4size_t]], core_array_TryFromSliceError

*/
Eurydice_array_u8x4 core_result_unwrap_26_84(core_result_Result_c7 self) {
  if (self.tag == core_result_Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint32_t[[$2size_t]]

*/
Eurydice_arr_b2 libcrux_secrets_int_public_integers_classify_27_54(
    Eurydice_arr_b2 self) {
  return self;
}
