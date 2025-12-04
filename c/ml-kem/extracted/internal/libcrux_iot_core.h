/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 146b7dce58cb11ca8010b1c947c3437a959dcd88
 * Eurydice: cdf02f9d8ed0d73f88c0a495c5b79359a51398fc
 * Karamel: 8e7262955105599e91f3a99c9ab3d3387f7046f2
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: f5a2e8205f49b35cb3e6b03aa25e16c26318ad09
 */

#ifndef internal_libcrux_iot_core_H
#define internal_libcrux_iot_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_iot_core.h"

static inline uint32_t core_num__u32__from_le_bytes(Eurydice_array_u8x4 x0);

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1);

static inline Eurydice_array_u8x4 core_num__u32__to_le_bytes(uint32_t x0);

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_declassify_d8_90(uint8_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_classify_27_90(uint8_t self);

void libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_borrow_slice_u8 lhs_c, Eurydice_borrow_slice_u8 rhs_c,
    Eurydice_borrow_slice_u8 lhs_s, Eurydice_borrow_slice_u8 rhs_s,
    Eurydice_mut_borrow_slice_u8 out);

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT ((size_t)12U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT \
  (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * (size_t)12U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_IOT_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE \
  ((size_t)32U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE ((size_t)32U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE ((size_t)32U)

/**
 K * BITS_PER_RING_ELEMENT / 8

 [eurydice] Note that we can't use const generics here because that breaks
            C extraction with eurydice.
*/
size_t libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(size_t rank);

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
uint64_t libcrux_secrets_int_as_u64_b8(uint32_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t

*/
uint32_t libcrux_secrets_int_public_integers_classify_27_df(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
uint32_t libcrux_secrets_int_as_u32_59(uint8_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_classify_27_39(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int16_t libcrux_secrets_int_as_i16_b8(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
int16_t libcrux_secrets_int_as_i16_36(int32_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int32_t

*/
int32_t libcrux_secrets_int_public_integers_classify_27_a8(int32_t self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_declassify_d8_39(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int32_t libcrux_secrets_int_as_i32_f5(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int32_t libcrux_secrets_int_as_i32_b8(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
int16_t libcrux_secrets_int_as_i16_59(uint8_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint8_t libcrux_secrets_int_as_u8_f5(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint16_t libcrux_secrets_int_as_u16_f5(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
int16_t libcrux_secrets_int_as_i16_ca(uint16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
uint64_t libcrux_secrets_int_as_u64_ca(uint16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int16_t libcrux_secrets_int_as_i16_f5(int16_t self);

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_6e1(
    const Eurydice_arr_00 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 3168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_3612(
    const Eurydice_arr_17 *a, core_ops_range_Range_08 r);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_18
with const generics
- SIZE= 1568
*/
Eurydice_arr_00 libcrux_iot_ml_kem_types_from_18_af(Eurydice_arr_00 value);

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
    Eurydice_arr_17 sk, Eurydice_arr_00 pk);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_56
with const generics
- SIZE= 3168
*/
Eurydice_arr_17 libcrux_iot_ml_kem_types_from_56_39(Eurydice_arr_17 value);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1536size_t
*/
typedef struct Eurydice_arr_38_s {
  uint8_t data[1536U];
} Eurydice_arr_38;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1536
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_c9(
    const Eurydice_arr_38 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 3168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_368(
    Eurydice_arr_17 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1536
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_c9(Eurydice_arr_38 *a);

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $272size_t
*/
typedef struct Eurydice_arr_a0_s {
  int16_t data[272U];
} Eurydice_arr_a0;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr int16_t[[$272size_t]], size_t

*/
typedef struct Eurydice_dst_ref_shared_1d_s {
  const Eurydice_arr_a0 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_1d;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_8a_s {
  Eurydice_arr_a0 data[4U];
} Eurydice_arr_8a;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_1d Eurydice_array_to_slice_shared_301(
    const Eurydice_arr_8a *a);

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr int16_t[[$272size_t]], size_t

*/
typedef struct Eurydice_dst_ref_mut_1d_s {
  Eurydice_arr_a0 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_1d;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_1d Eurydice_array_to_slice_mut_302(Eurydice_arr_8a *a);

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types size_t, size_t

*/
typedef struct Eurydice_dst_ref_mut_06_s {
  size_t *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_06;

/**
A monomorphic instance of Eurydice.arr
with types size_t
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_33_s {
  size_t data[4U];
} Eurydice_arr_33;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_06 Eurydice_array_to_slice_mut_4d(Eurydice_arr_33 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_78_s {
  Eurydice_arr_48 data[4U];
} Eurydice_arr_78;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_60 Eurydice_array_to_slice_shared_c72(
    const Eurydice_arr_78 *a);

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr uint8_t[[$168size_t]], size_t

*/
typedef struct Eurydice_dst_ref_shared_36_s {
  const Eurydice_arr_27 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_36;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_a6_s {
  Eurydice_arr_27 data[4U];
} Eurydice_arr_a6;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_36 Eurydice_array_to_slice_shared_e72(
    const Eurydice_arr_a6 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_36 Eurydice_array_to_slice_mut_e72(Eurydice_arr_a6 *a);

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr uint8_t[[$504size_t]], size_t

*/
typedef struct Eurydice_dst_ref_shared_ea_s {
  const Eurydice_arr_b0 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_ea;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_ec_s {
  Eurydice_arr_b0 data[4U];
} Eurydice_arr_ec;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_ea Eurydice_array_to_slice_shared_e92(
    const Eurydice_arr_ec *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_ea Eurydice_array_to_slice_mut_e92(Eurydice_arr_ec *a);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_9d
with const generics
- SIZE= 1568
*/
Eurydice_arr_00 libcrux_iot_ml_kem_types_from_9d_af(Eurydice_arr_00 value);

/**
This function found in impl {libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.as_slice_63
with const generics
- SIZE= 1568
*/
const Eurydice_arr_00 *libcrux_iot_ml_kem_types_as_slice_63_af(
    const Eurydice_arr_00 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1568
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_4e(Eurydice_arr_00 *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $512size_t
*/
typedef struct Eurydice_arr_0b_s {
  uint8_t data[512U];
} Eurydice_arr_0b;

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 512
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_3611(
    const Eurydice_arr_0b *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 512
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_44(Eurydice_arr_0b *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_65_s {
  Eurydice_arr_3e data[4U];
} Eurydice_arr_65;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_d2 Eurydice_array_to_slice_shared_612(
    const Eurydice_arr_65 *a);

/**
A monomorphic instance of libcrux_iot_ml_kem.utils.prf_input_inc
with const generics
- K= 4
*/
uint8_t libcrux_iot_ml_kem_utils_prf_input_inc_ac(Eurydice_arr_65 *prf_inputs,
                                                  uint8_t domain_separator);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1600size_t
*/
typedef struct Eurydice_arr_e7_s {
  uint8_t data[1600U];
} Eurydice_arr_e7;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1600
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_8e(
    const Eurydice_arr_e7 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1568size_t]]

*/
Eurydice_arr_00 libcrux_secrets_int_public_integers_classify_27_b7(
    Eurydice_arr_00 self);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1600
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_8c2(
    Eurydice_arr_e7 *a, size_t r);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
Eurydice_arr_e7 libcrux_iot_ml_kem_utils_into_padded_array_7f(
    Eurydice_borrow_slice_u8 slice);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c4(
    const Eurydice_arr_00 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_3610(
    const Eurydice_arr_00 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_4e(
    const Eurydice_arr_00 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 3168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_a6(
    const Eurydice_arr_17 *a);

typedef struct Eurydice_dst_ref_shared_uint8_t_size_t_x4_s {
  Eurydice_borrow_slice_u8 fst;
  Eurydice_borrow_slice_u8 snd;
  Eurydice_borrow_slice_u8 thd;
  Eurydice_borrow_slice_u8 f3;
} Eurydice_dst_ref_shared_uint8_t_size_t_x4;

typedef struct Eurydice_dst_ref_shared_uint8_t_size_t_x2_s {
  Eurydice_borrow_slice_u8 fst;
  Eurydice_borrow_slice_u8 snd;
} Eurydice_dst_ref_shared_uint8_t_size_t_x2;

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
    Eurydice_borrow_slice_u8 self);

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
Eurydice_dst_ref_shared_uint8_t_size_t_x4
libcrux_iot_ml_kem_types_unpack_private_key_1f(
    Eurydice_borrow_slice_u8 private_key);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c3(
    const Eurydice_arr_74 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_6e0(
    const Eurydice_arr_74 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 2400
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_369(
    const Eurydice_arr_ea *a, core_ops_range_Range_08 r);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_18
with const generics
- SIZE= 1184
*/
Eurydice_arr_74 libcrux_iot_ml_kem_types_from_18_d0(Eurydice_arr_74 value);

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
    Eurydice_arr_ea sk, Eurydice_arr_74 pk);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_56
with const generics
- SIZE= 2400
*/
Eurydice_arr_ea libcrux_iot_ml_kem_types_from_56_28(Eurydice_arr_ea value);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1152size_t
*/
typedef struct Eurydice_arr_60_s {
  uint8_t data[1152U];
} Eurydice_arr_60;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1152
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_06(
    const Eurydice_arr_60 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 2400
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_366(
    Eurydice_arr_ea *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1184
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_45(Eurydice_arr_74 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1152
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_06(Eurydice_arr_60 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_d4_s {
  Eurydice_arr_a0 data[3U];
} Eurydice_arr_d4;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_1d Eurydice_array_to_slice_shared_300(
    const Eurydice_arr_d4 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_1d Eurydice_array_to_slice_mut_301(Eurydice_arr_d4 *a);

/**
A monomorphic instance of Eurydice.arr
with types size_t
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_c8_s {
  size_t data[3U];
} Eurydice_arr_c8;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_06 Eurydice_array_to_slice_mut_92(Eurydice_arr_c8 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_84_s {
  Eurydice_arr_48 data[3U];
} Eurydice_arr_84;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_60 Eurydice_array_to_slice_shared_c71(
    const Eurydice_arr_84 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_d6_s {
  Eurydice_arr_27 data[3U];
} Eurydice_arr_d6;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_36 Eurydice_array_to_slice_shared_e71(
    const Eurydice_arr_d6 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_36 Eurydice_array_to_slice_mut_e71(Eurydice_arr_d6 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_35_s {
  Eurydice_arr_b0 data[3U];
} Eurydice_arr_35;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_ea Eurydice_array_to_slice_shared_e91(
    const Eurydice_arr_35 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_ea Eurydice_array_to_slice_mut_e91(Eurydice_arr_35 *a);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_iot_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_9d
with const generics
- SIZE= 1088
*/
Eurydice_arr_2c libcrux_iot_ml_kem_types_from_9d_80(Eurydice_arr_2c value);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_45(
    const Eurydice_arr_74 *a);

/**
This function found in impl {libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.as_slice_63
with const generics
- SIZE= 1184
*/
const Eurydice_arr_74 *libcrux_iot_ml_kem_types_as_slice_63_d0(
    const Eurydice_arr_74 *self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1184size_t]]

*/
Eurydice_arr_74 libcrux_secrets_int_public_integers_classify_27_aa(
    Eurydice_arr_74 self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1088
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_42(Eurydice_arr_2c *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_46_s {
  Eurydice_arr_3e data[3U];
} Eurydice_arr_46;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_d2 Eurydice_array_to_slice_shared_611(
    const Eurydice_arr_46 *a);

/**
A monomorphic instance of libcrux_iot_ml_kem.utils.prf_input_inc
with const generics
- K= 3
*/
uint8_t libcrux_iot_ml_kem_utils_prf_input_inc_e0(Eurydice_arr_46 *prf_inputs,
                                                  uint8_t domain_separator);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1120size_t
*/
typedef struct Eurydice_arr_480_s {
  uint8_t data[1120U];
} Eurydice_arr_480;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1120
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_74(
    const Eurydice_arr_480 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1088size_t]]

*/
Eurydice_arr_2c libcrux_secrets_int_public_integers_classify_27_33(
    Eurydice_arr_2c self);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1120
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_8c1(
    Eurydice_arr_480 *a, size_t r);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
Eurydice_arr_480 libcrux_iot_ml_kem_utils_into_padded_array_15(
    Eurydice_borrow_slice_u8 slice);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1088
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c2(
    const Eurydice_arr_2c *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1088
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_368(
    const Eurydice_arr_2c *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1088
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_42(
    const Eurydice_arr_2c *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2400
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ec(
    const Eurydice_arr_ea *a);

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
Eurydice_dst_ref_shared_uint8_t_size_t_x4
libcrux_iot_ml_kem_types_unpack_private_key_b4(
    Eurydice_borrow_slice_u8 private_key);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_363(
    Eurydice_arr_48 *a, core_ops_range_Range_08 r);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
Eurydice_arr_48 libcrux_iot_ml_kem_utils_into_padded_array_b6(
    Eurydice_borrow_slice_u8 slice);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$34size_t]]

*/
Eurydice_arr_48 libcrux_secrets_int_public_integers_declassify_d8_2c(
    Eurydice_arr_48 self);

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types int16_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
int16_t with const generics
- N= 272
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_subslice_to_shared_11(
    const Eurydice_arr_a0 *a, size_t r);

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
    Eurydice_borrow_slice_i16 self);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c0(
    const Eurydice_arr_06 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_366(
    const Eurydice_arr_06 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.slice_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_from_mut_6b(
    Eurydice_mut_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.slice_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_to_shared_c6(
    Eurydice_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_365(
    const Eurydice_arr_600 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.slice_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_from_shared_6b(
    Eurydice_borrow_slice_u8 s, size_t r);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$272size_t]]

*/
Eurydice_arr_a0 libcrux_secrets_int_public_integers_classify_27_9a(
    Eurydice_arr_a0 self);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_8b_s {
  Eurydice_arr_a0 data[1U];
} Eurydice_arr_8b;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_1d Eurydice_array_to_slice_mut_30(Eurydice_arr_8b *a);

/**
A monomorphic instance of Eurydice.arr
with types size_t
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_e40_s {
  size_t data[1U];
} Eurydice_arr_e40;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_06 Eurydice_array_to_slice_mut_26(Eurydice_arr_e40 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_b8_s {
  Eurydice_arr_48 data[1U];
} Eurydice_arr_b8;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_60 Eurydice_array_to_slice_shared_c7(
    const Eurydice_arr_b8 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_75_s {
  Eurydice_arr_27 data[1U];
} Eurydice_arr_75;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_36 Eurydice_array_to_slice_shared_e7(
    const Eurydice_arr_75 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_364(
    const Eurydice_arr_27 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_36 Eurydice_array_to_slice_mut_e7(Eurydice_arr_75 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_e4_s {
  Eurydice_arr_b0 data[1U];
} Eurydice_arr_e4;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_ea Eurydice_array_to_slice_shared_e9(
    const Eurydice_arr_e4 *a);

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types size_t, size_t

*/
typedef struct Eurydice_dst_ref_shared_06_s {
  const size_t *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_06;

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 272
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_subslice_mut_85(
    Eurydice_arr_a0 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 504
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_363(
    const Eurydice_arr_b0 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_ea Eurydice_array_to_slice_mut_e9(Eurydice_arr_e4 *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $128size_t
*/
typedef struct Eurydice_arr_d1_s {
  uint8_t data[128U];
} Eurydice_arr_d1;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 128
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_18(
    const Eurydice_arr_d1 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 128
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_18(Eurydice_arr_d1 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 33
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_610(
    const Eurydice_arr_3e *a);

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $256size_t
*/
typedef struct Eurydice_arr_c1_s {
  int16_t data[256U];
} Eurydice_arr_c1;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int16_t
with const generics
- N= 256
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_slice_shared_1a(
    const Eurydice_arr_c1 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int16_t
with const generics
- N= 256
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_slice_mut_1a(
    Eurydice_arr_c1 *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $384size_t
*/
typedef struct Eurydice_arr_cc_s {
  uint8_t data[384U];
} Eurydice_arr_cc;

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 384
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_361(
    const Eurydice_arr_cc *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 384
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_fe(Eurydice_arr_cc *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 33
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_362(
    Eurydice_arr_3e *a, core_ops_range_Range_08 r);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
Eurydice_arr_3e libcrux_iot_ml_kem_utils_into_padded_array_c8(
    Eurydice_borrow_slice_u8 slice);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_d8(
    const Eurydice_arr_06 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 64
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_8c(
    Eurydice_arr_06 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_6e(
    const Eurydice_arr_600 *a);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
Eurydice_arr_06 libcrux_iot_ml_kem_utils_into_padded_array_24(
    Eurydice_borrow_slice_u8 slice);

/**
A monomorphic instance of Eurydice.arr
with types int32_t
with const generics
- $256size_t
*/
typedef struct Eurydice_arr_c3_s {
  int32_t data[256U];
} Eurydice_arr_c3;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_20(
    const Eurydice_arr_c3 *a);

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t

*/
Eurydice_dst_ref_shared_fc Eurydice_slice_subslice_shared_46(
    Eurydice_dst_ref_shared_fc s, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_mut_fc Eurydice_array_to_subslice_mut_7f(
    Eurydice_arr_c3 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 16
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_subslice_shared_85(
    const Eurydice_arr_e2 *a, core_ops_range_Range_08 r);

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
    Eurydice_mut_borrow_slice_u8 x);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr int16_t[[$16size_t]]

*/
Eurydice_arr_e2 libcrux_secrets_int_public_integers_declassify_d8_3a(
    Eurydice_arr_e2 self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int16_t
with const generics
- N= 16
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_slice_shared_b4(
    const Eurydice_arr_e2 *a);

/**
A monomorphic instance of Eurydice.slice_subslice_mut
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t

*/
Eurydice_mut_borrow_slice_i16 Eurydice_slice_subslice_mut_76(
    Eurydice_mut_borrow_slice_i16 s, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t

*/
Eurydice_borrow_slice_i16 Eurydice_slice_subslice_shared_76(
    Eurydice_borrow_slice_i16 s, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int16_t
with const generics
- N= 16
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_slice_mut_b4(
    Eurydice_arr_e2 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$16size_t]]

*/
Eurydice_arr_e2 libcrux_secrets_int_public_integers_classify_27_3a(
    Eurydice_arr_e2 self);

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $128size_t
*/
typedef struct Eurydice_arr_49_s {
  int16_t data[128U];
} Eurydice_arr_49;

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
    Eurydice_mut_borrow_slice_u8 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 34
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_8d(
    const Eurydice_arr_48 *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $136size_t
*/
typedef struct Eurydice_arr_3d_s {
  uint8_t data[136U];
} Eurydice_arr_3d;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 64
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_d8(Eurydice_arr_06 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$64size_t]]

*/
Eurydice_arr_06 libcrux_secrets_int_public_integers_classify_27_490(
    Eurydice_arr_06 self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 48
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_95(Eurydice_arr_5f *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$48size_t]]

*/
Eurydice_arr_5f libcrux_secrets_int_public_integers_classify_27_7d(
    Eurydice_arr_5f self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 32
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_6e(
    Eurydice_arr_600 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$32size_t]]

*/
Eurydice_arr_600 libcrux_secrets_int_public_integers_classify_27_62(
    Eurydice_arr_600 self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 28
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_c0(Eurydice_arr_f1 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$28size_t]]

*/
Eurydice_arr_f1 libcrux_secrets_int_public_integers_classify_27_4b(
    Eurydice_arr_f1 self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types uint8_t

*/
Eurydice_borrow_slice_u8 libcrux_secrets_int_classify_public_classify_ref_9b_90(
    Eurydice_borrow_slice_u8 self);

typedef struct Eurydice_dst_ref_mut_uint8_t_size_t_x2_s {
  Eurydice_mut_borrow_slice_u8 fst;
  Eurydice_mut_borrow_slice_u8 snd;
} Eurydice_dst_ref_mut_uint8_t_size_t_x2;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $200size_t
*/
typedef struct Eurydice_arr_88_s {
  uint8_t data[200U];
} Eurydice_arr_88;

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_36(
    const Eurydice_arr_88 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f7(Eurydice_arr_88 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_60(
    const Eurydice_array_u8x4 *a);

/**
A monomorphic instance of Eurydice.slice_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_mut_7e(
    Eurydice_mut_borrow_slice_u8 s, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f7(
    const Eurydice_arr_88 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_36(
    Eurydice_arr_88 *a, core_ops_range_Range_08 r);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$200size_t]]

*/
Eurydice_arr_88 libcrux_secrets_int_public_integers_classify_27_c1(
    Eurydice_arr_88 self);

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_shared_7e(
    Eurydice_borrow_slice_u8 s, core_ops_range_Range_08 r);

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_44_tags;

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$4size_t]], core_array_TryFromSliceError

*/
typedef struct core_result_Result_44_s {
  core_result_Result_44_tags tag;
  union {
    Eurydice_array_u8x4 case_Ok;
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_44;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$4size_t]], core_array_TryFromSliceError

*/
Eurydice_array_u8x4 core_result_unwrap_26_84(core_result_Result_44 self);

/**
A monomorphic instance of Eurydice.arr
with types uint32_t
with const generics
- $255size_t
*/
typedef struct Eurydice_arr_000_s {
  uint32_t data[255U];
} Eurydice_arr_000;

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint32_t[[$2size_t]]

*/
Eurydice_arr_b2 libcrux_secrets_int_public_integers_classify_27_54(
    Eurydice_arr_b2 self);

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_core_H_DEFINED
#endif /* internal_libcrux_iot_core_H */
