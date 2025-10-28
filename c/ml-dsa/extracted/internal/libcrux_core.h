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
 * Libcrux: 4c0c9248a551dd42901dc5208f62cc9e92e7e0c3
 */

#ifndef internal_libcrux_core_H
#define internal_libcrux_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_core.h"

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

/**
A monomorphic instance of core.option.Option
with types size_t

*/
typedef struct core_option_Option_08_s {
  core_option_Option_08_tags tag;
  size_t f0;
} core_option_Option_08;

static inline uint32_t core_num__u32__from_le_bytes(uint8_t x0[4U]);

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1);

static inline void core_num__u32__to_le_bytes(uint32_t x0, uint8_t x1[4U]);

static inline uint64_t core_num__u64__from_le_bytes(uint8_t x0[8U]);

extern uint8_t
core_ops_bit__core__ops__bit__BitAnd_u8__u8__for___a__u8___bitand(uint8_t *x0,
                                                                  uint8_t x1);

extern uint8_t core_ops_bit__core__ops__bit__Shr_i32__u8__for___a__u8___shr(
    uint8_t *x0, int32_t x1);

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
uint8_t *libcrux_iot_ml_dsa_types_as_ref_ad_c2(
    libcrux_iot_ml_dsa_types_MLDSASignature_9b *self);

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
uint8_t *libcrux_iot_ml_dsa_types_as_ref_e9_d8(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe *self);

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
uint8_t *libcrux_iot_ml_dsa_types_as_ref_f8_32(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 *self);

/**
A monomorphic instance of core.option.Option
with types int32_t[256size_t][8size_t]

*/
typedef struct core_option_Option_d6_s {
  core_option_Option_08_tags tag;
  int32_t f0[8U][256U];
} core_option_Option_d6;

/**
A monomorphic instance of core.option.Option
with types uint8_t[64size_t]

*/
typedef struct core_option_Option_880_s {
  core_option_Option_08_tags tag;
  uint8_t f0[64U];
} core_option_Option_880;

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
libcrux_iot_ml_dsa_types_MLDSASignature_9b libcrux_iot_ml_dsa_types_zero_ad_c2(
    void);

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
libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe
libcrux_iot_ml_dsa_types_new_e9_d8(uint8_t value[2592U]);

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
libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 libcrux_iot_ml_dsa_types_new_f8_32(
    uint8_t value[4896U]);

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
uint8_t *libcrux_iot_ml_dsa_types_as_ref_ad_fa(
    libcrux_iot_ml_dsa_types_MLDSASignature_8f *self);

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
uint8_t *libcrux_iot_ml_dsa_types_as_ref_e9_97(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea *self);

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
uint8_t *libcrux_iot_ml_dsa_types_as_ref_f8_09(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_22 *self);

/**
A monomorphic instance of core.option.Option
with types int32_t[256size_t][6size_t]

*/
typedef struct core_option_Option_f0_s {
  core_option_Option_08_tags tag;
  int32_t f0[6U][256U];
} core_option_Option_f0;

/**
A monomorphic instance of core.option.Option
with types uint8_t[48size_t]

*/
typedef struct core_option_Option_67_s {
  core_option_Option_08_tags tag;
  uint8_t f0[48U];
} core_option_Option_67;

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
libcrux_iot_ml_dsa_types_MLDSASignature_8f libcrux_iot_ml_dsa_types_zero_ad_fa(
    void);

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
libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea
libcrux_iot_ml_dsa_types_new_e9_97(uint8_t value[1952U]);

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
libcrux_iot_ml_dsa_types_MLDSASigningKey_22 libcrux_iot_ml_dsa_types_new_f8_09(
    uint8_t value[4032U]);

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
uint8_t *libcrux_iot_ml_dsa_types_as_ref_ad_1a(
    libcrux_iot_ml_dsa_types_MLDSASignature_64 *self);

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
uint8_t *libcrux_iot_ml_dsa_types_as_ref_e9_db(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c *self);

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
uint8_t *libcrux_iot_ml_dsa_types_as_ref_f8_ff(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 *self);

/**
A monomorphic instance of core.option.Option
with types int32_t[256size_t][4size_t]

*/
typedef struct core_option_Option_a8_s {
  core_option_Option_08_tags tag;
  int32_t f0[4U][256U];
} core_option_Option_a8;

/**
A monomorphic instance of core.option.Option
with types uint8_t[32size_t]

*/
typedef struct core_option_Option_85_s {
  core_option_Option_08_tags tag;
  uint8_t f0[32U];
} core_option_Option_85;

/**
A monomorphic instance of core.result.Result
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_15_s {
  core_result_Result_10 tag;
  union {
    uint8_t case_Ok[8U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_15;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_68(core_result_Result_15 self, uint8_t ret[8U]);

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
libcrux_iot_ml_dsa_types_MLDSASignature_64 libcrux_iot_ml_dsa_types_zero_ad_1a(
    void);

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
libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c
libcrux_iot_ml_dsa_types_new_e9_db(uint8_t value[1312U]);

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
libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 libcrux_iot_ml_dsa_types_new_f8_ff(
    uint8_t value[2560U]);

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
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[136size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_3f(uint8_t self[136U],
                                                        uint8_t ret[136U]);

typedef struct Eurydice_slice_uint8_t_x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_x2;

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
with types uint8_t[200size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_e7(uint8_t self[200U],
                                                        uint8_t ret[200U]);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_derefed_slice uint8_t

*/
uint8_t (*libcrux_secrets_int_public_integers_classify_ref_c5_45(
    uint8_t (*self)[]))[];

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

#define internal_libcrux_core_H_DEFINED
#endif /* internal_libcrux_core_H */
