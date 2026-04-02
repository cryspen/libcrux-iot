/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 377317d6b25702c46ffff072fa00a3e32095e46f
 * Eurydice: b227478b67c6a6e2ff611f978f10d6b7f26472ac
 * Karamel: 4e64d915da3c172d1dfad805b8e1a46beff938bc
 * F*: 89901492c020c74b82d811d27f3149c222d9b8b5
 * Libcrux: 0ab0448a17b81dc787e95a2c646c27ae75247f7b
 */

#ifndef internal_libcrux_iot_mldsa_core_H
#define internal_libcrux_iot_mldsa_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_iot_mldsa_core.h"

static inline uint32_t core_num__u32__from_le_bytes(Eurydice_array_u8x4 x0);

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1);

static inline Eurydice_array_u8x4 core_num__u32__to_le_bytes(uint32_t x0);

static inline uint64_t core_num__u64__from_le_bytes(Eurydice_array_u8x8 x0);

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

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
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int64_t

*/
int64_t libcrux_secrets_int_public_integers_classify_27_b8(int64_t self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int32_t

*/
int32_t libcrux_secrets_int_public_integers_declassify_d8_a8(int32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
int64_t libcrux_secrets_int_as_i64_36(int32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i64}
*/
uint64_t libcrux_secrets_int_as_u64_60(int64_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int32_t

*/
int32_t libcrux_secrets_int_public_integers_classify_27_a8(int32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
int32_t libcrux_secrets_int_as_i32_a3(uint64_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i64}
*/
int32_t libcrux_secrets_int_as_i32_60(int64_t self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_declassify_d8_90(uint8_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
int32_t libcrux_secrets_int_as_i32_59(uint8_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_classify_27_90(uint8_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
uint8_t libcrux_secrets_int_as_u8_36(int32_t self);

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASignature
with const generics
- $4627size_t
*/
typedef Eurydice_arr_380 libcrux_iot_ml_dsa_types_MLDSASignature_9b;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_ad
with const generics
- SIZE= 4627
*/
const Eurydice_arr_380 *libcrux_iot_ml_dsa_types_as_ref_ad_c2(
    const Eurydice_arr_380 *self);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_e9
with const generics
- SIZE= 2592
*/
const Eurydice_arr_51 *libcrux_iot_ml_dsa_types_as_ref_e9_d8(
    const Eurydice_arr_51 *self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$64size_t]]

*/
const Eurydice_arr_06 *libcrux_secrets_int_public_integers_classify_ref_c5_49(
    const Eurydice_arr_06 *self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$2592size_t]]

*/
const Eurydice_arr_51 *libcrux_secrets_int_public_integers_classify_ref_c5_fc(
    const Eurydice_arr_51 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4627
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_24(
    const Eurydice_arr_380 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2592
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f70(
    const Eurydice_arr_51 *a);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_f8
with const generics
- SIZE= 4896
*/
const Eurydice_arr_180 *libcrux_iot_ml_dsa_types_as_ref_f8_32(
    const Eurydice_arr_180 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4896
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_e2(
    const Eurydice_arr_180 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4627
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_24(
    Eurydice_arr_380 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_c3
with const generics
- $8size_t
*/
typedef struct Eurydice_arr_fb_s {
  Eurydice_arr_c3 data[8U];
} Eurydice_arr_fb;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 8
*/
Eurydice_dst_ref_shared_22 Eurydice_array_to_slice_shared_6d1(
    const Eurydice_arr_fb *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 8
*/
Eurydice_dst_ref_mut_22 Eurydice_array_to_slice_mut_6d1(Eurydice_arr_fb *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1024size_t
*/
typedef struct Eurydice_arr_9e_s {
  uint8_t data[1024U];
} Eurydice_arr_9e;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1024
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_fd(
    const Eurydice_arr_9e *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1024
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_fd(Eurydice_arr_9e *a);

/**
 Init with zero
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.zero_ad
with const generics
- SIZE= 4627
*/
Eurydice_arr_380 libcrux_iot_ml_dsa_types_zero_ad_c2(void);

/**
 Build
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_e9
with const generics
- SIZE= 2592
*/
Eurydice_arr_51 libcrux_iot_ml_dsa_types_new_e9_d8(Eurydice_arr_51 value);

/**
 Build
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_f8
with const generics
- SIZE= 4896
*/
Eurydice_arr_180 libcrux_iot_ml_dsa_types_new_f8_32(Eurydice_arr_180 value);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2592
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f70(
    Eurydice_arr_51 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4896
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_e2(
    Eurydice_arr_180 *a);

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASignature
with const generics
- $3309size_t
*/
typedef Eurydice_arr_96 libcrux_iot_ml_dsa_types_MLDSASignature_8f;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_ad
with const generics
- SIZE= 3309
*/
const Eurydice_arr_96 *libcrux_iot_ml_dsa_types_as_ref_ad_fa(
    const Eurydice_arr_96 *self);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_e9
with const generics
- SIZE= 1952
*/
const Eurydice_arr_4a *libcrux_iot_ml_dsa_types_as_ref_e9_97(
    const Eurydice_arr_4a *self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$48size_t]]

*/
const Eurydice_arr_5f *libcrux_secrets_int_public_integers_classify_ref_c5_7d(
    const Eurydice_arr_5f *self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$1952size_t]]

*/
const Eurydice_arr_4a *libcrux_secrets_int_public_integers_classify_ref_c5_3d(
    const Eurydice_arr_4a *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 3309
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ee0(
    const Eurydice_arr_96 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1952
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_5b(
    const Eurydice_arr_4a *a);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_f8
with const generics
- SIZE= 4032
*/
const Eurydice_arr_d10 *libcrux_iot_ml_dsa_types_as_ref_f8_09(
    const Eurydice_arr_d10 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4032
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ef(
    const Eurydice_arr_d10 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 3309
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ee0(
    Eurydice_arr_96 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_c3
with const generics
- $6size_t
*/
typedef struct Eurydice_arr_b5_s {
  Eurydice_arr_c3 data[6U];
} Eurydice_arr_b5;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 6
*/
Eurydice_dst_ref_shared_22 Eurydice_array_to_slice_shared_6d0(
    const Eurydice_arr_b5 *a);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr uint8_t[[$48size_t]]

*/
const Eurydice_arr_5f *libcrux_secrets_int_public_integers_declassify_ref_ad_7d(
    const Eurydice_arr_5f *self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 6
*/
Eurydice_dst_ref_mut_22 Eurydice_array_to_slice_mut_6d0(Eurydice_arr_b5 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 48
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_95(
    const Eurydice_arr_5f *a);

/**
 Init with zero
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.zero_ad
with const generics
- SIZE= 3309
*/
Eurydice_arr_96 libcrux_iot_ml_dsa_types_zero_ad_fa(void);

/**
 Build
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_e9
with const generics
- SIZE= 1952
*/
Eurydice_arr_4a libcrux_iot_ml_dsa_types_new_e9_97(Eurydice_arr_4a value);

/**
 Build
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_f8
with const generics
- SIZE= 4032
*/
Eurydice_arr_d10 libcrux_iot_ml_dsa_types_new_f8_09(Eurydice_arr_d10 value);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1952
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_5b(Eurydice_arr_4a *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4032
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ef(
    Eurydice_arr_d10 *a);

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASignature
with const generics
- $2420size_t
*/
typedef Eurydice_arr_400 libcrux_iot_ml_dsa_types_MLDSASignature_64;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_ad
with const generics
- SIZE= 2420
*/
const Eurydice_arr_400 *libcrux_iot_ml_dsa_types_as_ref_ad_1a(
    const Eurydice_arr_400 *self);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_e9
with const generics
- SIZE= 1312
*/
const Eurydice_arr_40 *libcrux_iot_ml_dsa_types_as_ref_e9_db(
    const Eurydice_arr_40 *self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int32_t[[$256size_t]]

*/
Eurydice_arr_c3 libcrux_secrets_int_public_integers_classify_27_5c(
    Eurydice_arr_c3 self);

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types int32_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
int32_t with const generics
- N= 263
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_subslice_to_shared_c2(
    const Eurydice_arr_13 *a, size_t r);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types int32_t

*/
Eurydice_dst_ref_shared_fc
libcrux_secrets_int_classify_public_classify_ref_9b_a8(
    Eurydice_dst_ref_shared_fc self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$34size_t]]

*/
Eurydice_arr_48 libcrux_secrets_int_public_integers_classify_27_2c(
    Eurydice_arr_48 self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$32size_t]]

*/
const Eurydice_arr_60 *libcrux_secrets_int_public_integers_classify_ref_c5_62(
    const Eurydice_arr_60 *self);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr uint8_t[[$64size_t]]

*/
const Eurydice_arr_06 *libcrux_secrets_int_public_integers_declassify_ref_ad_49(
    const Eurydice_arr_06 *self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$1312size_t]]

*/
const Eurydice_arr_40 *libcrux_secrets_int_public_integers_classify_ref_c5_90(
    const Eurydice_arr_40 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2420
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_180(
    const Eurydice_arr_400 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1312
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_bb(
    const Eurydice_arr_40 *a);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_f8
with const generics
- SIZE= 2560
*/
const Eurydice_arr_18 *libcrux_iot_ml_dsa_types_as_ref_f8_ff(
    const Eurydice_arr_18 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2560
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_59(
    const Eurydice_arr_18 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2420
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_180(
    Eurydice_arr_400 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_c3
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_83_s {
  Eurydice_arr_c3 data[4U];
} Eurydice_arr_83;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_22 Eurydice_array_to_slice_shared_6d(
    const Eurydice_arr_83 *a);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr uint8_t[[$32size_t]]

*/
const Eurydice_arr_60 *libcrux_secrets_int_public_integers_declassify_ref_ad_62(
    const Eurydice_arr_60 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_22 Eurydice_array_to_slice_mut_6d(Eurydice_arr_83 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_mut_fc Eurydice_array_to_subslice_mut_7f(
    Eurydice_arr_c3 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_200(
    const Eurydice_arr_c3 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 136
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c(
    const Eurydice_arr_3d *a, size_t r);

/**
A monomorphic instance of core.result.Result
with types Eurydice_array_u8x8, core_array_TryFromSliceError

*/
typedef struct Result_8e_s {
  Result_8e_tags tag;
  union {
    Eurydice_array_u8x8 case_Ok;
    TryFromSliceError case_Err;
  } val;
} Result_8e;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$8size_t]], core_array_TryFromSliceError

*/
Eurydice_array_u8x8 unwrap_26_ab(Result_8e self);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $768size_t
*/
typedef struct Eurydice_arr_56_s {
  uint8_t data[768U];
} Eurydice_arr_56;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 768
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ee(
    const Eurydice_arr_56 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 768
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ee(Eurydice_arr_56 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 640
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_7d(
    const Eurydice_arr_c30 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 640
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_7d(
    Eurydice_arr_c30 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 576
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_fa(
    const Eurydice_arr_5f0 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 576
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_fa(
    Eurydice_arr_5f0 *a);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$11size_t]]

*/
const Eurydice_arr_cb *libcrux_secrets_int_public_integers_classify_ref_c5_4e(
    const Eurydice_arr_cb *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 11
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_da(
    const Eurydice_arr_cb *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_f10_s {
  uint8_t data[1U];
} Eurydice_arr_f10;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_07(
    const Eurydice_arr_f10 *a);

/**
 Init with zero
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.zero_ad
with const generics
- SIZE= 2420
*/
Eurydice_arr_400 libcrux_iot_ml_dsa_types_zero_ad_1a(void);

/**
 Build
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_e9
with const generics
- SIZE= 1312
*/
Eurydice_arr_40 libcrux_iot_ml_dsa_types_new_e9_db(Eurydice_arr_40 value);

/**
 Build
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_f8
with const generics
- SIZE= 2560
*/
Eurydice_arr_18 libcrux_iot_ml_dsa_types_new_f8_ff(Eurydice_arr_18 value);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1312
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_bb(Eurydice_arr_40 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2560
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_59(Eurydice_arr_18 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_d8(
    const Eurydice_arr_06 *a);

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

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 66
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_39(
    const Eurydice_arr_a2 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_13
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_38_s {
  Eurydice_arr_13 data[4U];
} Eurydice_arr_38;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$263size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_4c Eurydice_array_to_slice_mut_f6(Eurydice_arr_38 *a);

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr_13, size_t

*/
typedef struct Eurydice_dst_ref_shared_4c_s {
  const Eurydice_arr_13 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_4c;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 263
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_20(
    const Eurydice_arr_13 *a);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr int32_t[[$263size_t]]

*/
const Eurydice_arr_13 *libcrux_secrets_int_public_integers_classify_ref_c5_0d(
    const Eurydice_arr_13 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_7b(
    const Eurydice_arr_27 *a);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr uint8_t[[$168size_t]]

*/
const Eurydice_arr_27 *libcrux_secrets_int_public_integers_declassify_ref_ad_fe(
    const Eurydice_arr_27 *self);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types int32_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
int32_t with const generics
- N= 263
*/
Eurydice_dst_ref_mut_fc Eurydice_array_to_subslice_from_mut_96(
    Eurydice_arr_13 *a, size_t r);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$34size_t]]

*/
const Eurydice_arr_48 *libcrux_secrets_int_public_integers_classify_ref_c5_2c(
    const Eurydice_arr_48 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 34
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_8d(
    const Eurydice_arr_48 *a);

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
- N= 2
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_26(
    const Eurydice_array_u8x2 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_6e(
    const Eurydice_arr_60 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 8
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_subslice_shared_7f(
    const Eurydice_arr_d4 *a, core_ops_range_Range_08 r);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr int32_t[[$8size_t]]

*/
const Eurydice_arr_d4 *libcrux_secrets_int_public_integers_declassify_ref_ad_90(
    const Eurydice_arr_d4 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 8
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_a7(
    const Eurydice_arr_d4 *a);

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t

*/
Eurydice_dst_ref_shared_fc Eurydice_slice_subslice_shared_46(
    Eurydice_dst_ref_shared_fc s, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int32_t
with const generics
- N= 8
*/
Eurydice_dst_ref_mut_fc Eurydice_array_to_slice_mut_a7(Eurydice_arr_d4 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 66
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_362(
    Eurydice_arr_a2 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_361(
    Eurydice_arr_48 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 136
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_d4(Eurydice_arr_3d *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_7b(Eurydice_arr_27 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 840
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_a8(Eurydice_arr_12 *a);

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
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_6e(Eurydice_arr_60 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$32size_t]]

*/
Eurydice_arr_60 libcrux_secrets_int_public_integers_classify_27_62(
    Eurydice_arr_60 self);

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
A monomorphic instance of Eurydice.slice_subslice_to_mut
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_to_mut_c6(
    Eurydice_mut_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 4
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_361(
    const Eurydice_array_u8x4 *a, core_ops_range_Range_08 r);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$136size_t]]

*/
Eurydice_arr_3d libcrux_secrets_int_public_integers_classify_27_df0(
    Eurydice_arr_3d self);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 136
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_360(
    const Eurydice_arr_3d *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.slice_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_from_shared_6b(
    Eurydice_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 136
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_360(
    Eurydice_arr_3d *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 136
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_d4(
    const Eurydice_arr_3d *a);

/**
A monomorphic instance of Eurydice.slice_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_to_shared_c6(
    Eurydice_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 136
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_8c(
    Eurydice_arr_3d *a, size_t r);

/**
A monomorphic instance of Eurydice.slice_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_from_mut_6b(
    Eurydice_mut_borrow_slice_u8 s, size_t r);

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
A monomorphic instance of Eurydice.slice_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_shared_7e(
    Eurydice_borrow_slice_u8 s, core_ops_range_Range_08 r);

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
A monomorphic instance of Eurydice.arr
with types uint32_t
with const generics
- $255size_t
*/
typedef struct Eurydice_arr_00_s {
  uint32_t data[255U];
} Eurydice_arr_00;

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

#define internal_libcrux_iot_mldsa_core_H_DEFINED
#endif /* internal_libcrux_iot_mldsa_core_H */
