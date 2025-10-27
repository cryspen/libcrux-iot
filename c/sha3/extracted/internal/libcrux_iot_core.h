/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon:
 * Eurydice:
 * Karamel:
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: 77a80e3eb2196754d31058d237c0052000775d2c
 */

#ifndef internal_libcrux_iot_core_H
#define internal_libcrux_iot_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_10;

static inline uint32_t core_num__u32__from_le_bytes(uint8_t x0[4U]);

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1);

static inline void core_num__u32__to_le_bytes(uint32_t x0, uint8_t x1[4U]);

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
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[168size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_09(uint8_t self[168U],
                                                        uint8_t ret[168U]);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[136size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_3f(uint8_t self[136U],
                                                        uint8_t ret[136U]);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[64size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_7b(uint8_t self[64U],
                                                        uint8_t ret[64U]);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[48size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_4d(uint8_t self[48U],
                                                        uint8_t ret[48U]);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[32size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_ee0(uint8_t self[32U],
                                                         uint8_t ret[32U]);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[28size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_ae(uint8_t self[28U],
                                                        uint8_t ret[28U]);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_slice uint8_t

*/
Eurydice_slice *libcrux_secrets_int_public_integers_classify_ref_c5_ba(
    Eurydice_slice *self);

typedef struct Eurydice_slice_uint8_t_x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_x2;

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[200size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_e7(uint8_t self[200U],
                                                        uint8_t ret[200U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[4size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_12_s {
  core_result_Result_10 tag;
  union {
    uint8_t case_Ok[4U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_12;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[4size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_0a(core_result_Result_12 self, uint8_t ret[4U]);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t[2size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_93(uint32_t self[2U],
                                                        uint32_t ret[2U]);

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_core_H_DEFINED
#endif /* internal_libcrux_iot_core_H */
