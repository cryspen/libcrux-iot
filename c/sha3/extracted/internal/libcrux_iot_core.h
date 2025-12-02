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
 * Libcrux: b9e3a3518649180d169e38504bad3739d37bd429
 */

#ifndef internal_libcrux_iot_core_H
#define internal_libcrux_iot_core_H

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
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
uint64_t libcrux_secrets_int_as_u64_b8(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_classify_27_90(uint8_t self);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $168size_t
*/
typedef struct Eurydice_arr_27_s {
  uint8_t data[168U];
} Eurydice_arr_27;

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$168size_t]]

*/
Eurydice_arr_27 libcrux_secrets_int_public_integers_classify_27_fe(
    Eurydice_arr_27 self);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_362(
    const Eurydice_arr_27 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_361(
    Eurydice_arr_27 *a, core_ops_range_Range_08 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_7b(
    const Eurydice_arr_27 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_8c0(
    Eurydice_arr_27 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 4
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_361(
    const Eurydice_array_u8x4 *a, core_ops_range_Range_08 r);

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
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types uint8_t

*/
Eurydice_borrow_slice_u8 libcrux_secrets_int_classify_public_classify_ref_9b_90(
    Eurydice_borrow_slice_u8 self);

typedef struct Eurydice_mut_borrow_slice_u8_x2_s {
  Eurydice_mut_borrow_slice_u8 fst;
  Eurydice_mut_borrow_slice_u8 snd;
} Eurydice_mut_borrow_slice_u8_x2;

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

typedef uint8_t core_result_Result_c7_tags;

/**
A monomorphic instance of core.result.Result
with types Eurydice_array_u8x4, core_array_TryFromSliceError

*/
typedef struct core_result_Result_c7_s {
  core_result_Result_c7_tags tag;
  union {
    Eurydice_array_u8x4 case_Ok;
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_c7;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$4size_t]], core_array_TryFromSliceError

*/
Eurydice_array_u8x4 core_result_unwrap_26_84(core_result_Result_c7 self);

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
A monomorphic instance of Eurydice.arr
with types uint32_t
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_b2_s {
  uint32_t data[2U];
} Eurydice_arr_b2;

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
