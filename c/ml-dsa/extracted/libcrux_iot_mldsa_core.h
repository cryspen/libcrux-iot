/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 637a6bc8a4c2a79875af5aa4e413c7ef3aa7f391
 * Eurydice: 788f967cfd9eaff503d3785f64072f851945c726
 * Karamel: 4e64d915da3c172d1dfad805b8e1a46beff938bc
 * F*: unset
 * Libcrux: 34a7778be03e250fff932df62147cec2b85ec54b
 */

#ifndef libcrux_iot_mldsa_core_H
#define libcrux_iot_mldsa_core_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice-include/eurydice/base.h"
#include "eurydice-include/eurydice/core.h"
#include "eurydice-include/eurydice/slice.h"

static inline uint32_t core_num__u32__from_le_bytes(Eurydice_array_u8x4 x0);

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1);

static inline Eurydice_array_u8x4 core_num__u32__to_le_bytes(uint32_t x0);

static inline uint64_t core_num__u64__from_le_bytes(Eurydice_array_u8x8 x0);

static inline uint8_t
core_ops_bit__core__ops__bit__BitAnd_u8__u8__for__0__u8___bitand(
    const uint8_t *x0, uint8_t x1);

static inline uint8_t
core_ops_bit__core__ops__bit__Shr_i32__u8__for__0__u8___shr(const uint8_t *x0,
                                                            int32_t x1);

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

#define libcrux_iot_ml_dsa_types_VerificationError_MalformedHintError 0
#define libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError \
  1
#define libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError \
  2
#define libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError \
  3

typedef uint8_t libcrux_iot_ml_dsa_types_VerificationError;

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t
libcrux_secrets_int_public_integers_classify_27_49(uint64_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t
libcrux_secrets_int_public_integers_declassify_d8_df(uint32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
static KRML_MUSTINLINE uint64_t libcrux_secrets_int_as_u64_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_49(
      (uint64_t)libcrux_secrets_int_public_integers_declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t
libcrux_secrets_int_public_integers_classify_27_df(uint32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t
libcrux_secrets_int_public_integers_declassify_d8_49(uint64_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
static KRML_MUSTINLINE uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)libcrux_secrets_int_public_integers_declassify_d8_49(self));
}

#define libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError 0
#define libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError 1

typedef uint8_t libcrux_iot_ml_dsa_types_SigningError;

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
static KRML_MUSTINLINE uint8_t
libcrux_secrets_int_public_integers_classify_27_90(uint8_t self) {
  return self;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $4627size_t
*/
typedef struct Eurydice_arr_380_s {
  uint8_t data[4627U];
} Eurydice_arr_380;

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
static inline const Eurydice_arr_380 *libcrux_iot_ml_dsa_types_as_ref_ad_c2(
    const Eurydice_arr_380 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2592size_t
*/
typedef struct Eurydice_arr_51_s {
  uint8_t data[2592U];
} Eurydice_arr_51;

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
static inline const Eurydice_arr_51 *libcrux_iot_ml_dsa_types_as_ref_e9_d8(
    const Eurydice_arr_51 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4627
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_24(
    const Eurydice_arr_380 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4627U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2592
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f70(
    const Eurydice_arr_51 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2592U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $4896size_t
*/
typedef struct Eurydice_arr_180_s {
  uint8_t data[4896U];
} Eurydice_arr_180;

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
static inline const Eurydice_arr_180 *libcrux_iot_ml_dsa_types_as_ref_f8_32(
    const Eurydice_arr_180 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4896
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_e2(
    const Eurydice_arr_180 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4896U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4627
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_24(
    Eurydice_arr_380 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4627U;
  return lit;
}

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
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr_c3, size_t

*/
typedef struct Eurydice_dst_ref_shared_22_s {
  const Eurydice_arr_c3 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_22;

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
static inline Eurydice_dst_ref_shared_22 Eurydice_array_to_slice_shared_6d1(
    const Eurydice_arr_fb *a) {
  Eurydice_dst_ref_shared_22 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr_c3, size_t

*/
typedef struct Eurydice_dst_ref_mut_22_s {
  Eurydice_arr_c3 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_22;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 8
*/
static inline Eurydice_dst_ref_mut_22 Eurydice_array_to_slice_mut_6d1(
    Eurydice_arr_fb *a) {
  Eurydice_dst_ref_mut_22 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

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
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_fd(
    const Eurydice_arr_9e *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1024U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1024
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_fd(
    Eurydice_arr_9e *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1024U;
  return lit;
}

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
static inline Eurydice_arr_380 libcrux_iot_ml_dsa_types_zero_ad_c2(void) {
  return (KRML_CLITERAL(Eurydice_arr_380){.data = {0U}});
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $2592size_t
- $4896size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d_s {
  Eurydice_arr_180 signing_key;
  Eurydice_arr_51 verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d;

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
static inline Eurydice_arr_51 libcrux_iot_ml_dsa_types_new_e9_d8(
    Eurydice_arr_51 value) {
  return value;
}

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
static inline Eurydice_arr_180 libcrux_iot_ml_dsa_types_new_f8_32(
    Eurydice_arr_180 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2592
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f70(
    Eurydice_arr_51 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2592U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4896
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_e2(
    Eurydice_arr_180 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4896U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $3309size_t
*/
typedef struct Eurydice_arr_96_s {
  uint8_t data[3309U];
} Eurydice_arr_96;

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
static inline const Eurydice_arr_96 *libcrux_iot_ml_dsa_types_as_ref_ad_fa(
    const Eurydice_arr_96 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1952size_t
*/
typedef struct Eurydice_arr_4a_s {
  uint8_t data[1952U];
} Eurydice_arr_4a;

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
static inline const Eurydice_arr_4a *libcrux_iot_ml_dsa_types_as_ref_e9_97(
    const Eurydice_arr_4a *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 3309
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ee0(
    const Eurydice_arr_96 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3309U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1952
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_5b(
    const Eurydice_arr_4a *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1952U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $4032size_t
*/
typedef struct Eurydice_arr_d10_s {
  uint8_t data[4032U];
} Eurydice_arr_d10;

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
static inline const Eurydice_arr_d10 *libcrux_iot_ml_dsa_types_as_ref_f8_09(
    const Eurydice_arr_d10 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4032
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ef(
    const Eurydice_arr_d10 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4032U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 3309
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ee0(
    Eurydice_arr_96 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3309U;
  return lit;
}

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
static inline Eurydice_dst_ref_shared_22 Eurydice_array_to_slice_shared_6d0(
    const Eurydice_arr_b5 *a) {
  Eurydice_dst_ref_shared_22 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)6U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 6
*/
static inline Eurydice_dst_ref_mut_22 Eurydice_array_to_slice_mut_6d0(
    Eurydice_arr_b5 *a) {
  Eurydice_dst_ref_mut_22 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)6U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $48size_t
*/
typedef struct Eurydice_arr_5f_s {
  uint8_t data[48U];
} Eurydice_arr_5f;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 48
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_95(
    const Eurydice_arr_5f *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)48U;
  return lit;
}

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
static inline Eurydice_arr_96 libcrux_iot_ml_dsa_types_zero_ad_fa(void) {
  return (KRML_CLITERAL(Eurydice_arr_96){.data = {0U}});
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $1952size_t
- $4032size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_06_s {
  Eurydice_arr_d10 signing_key;
  Eurydice_arr_4a verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_06;

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
static inline Eurydice_arr_4a libcrux_iot_ml_dsa_types_new_e9_97(
    Eurydice_arr_4a value) {
  return value;
}

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
static inline Eurydice_arr_d10 libcrux_iot_ml_dsa_types_new_f8_09(
    Eurydice_arr_d10 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1952
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_5b(
    Eurydice_arr_4a *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1952U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4032
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ef(
    Eurydice_arr_d10 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4032U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2420size_t
*/
typedef struct Eurydice_arr_400_s {
  uint8_t data[2420U];
} Eurydice_arr_400;

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
static inline const Eurydice_arr_400 *libcrux_iot_ml_dsa_types_as_ref_ad_1a(
    const Eurydice_arr_400 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1312size_t
*/
typedef struct Eurydice_arr_40_s {
  uint8_t data[1312U];
} Eurydice_arr_40;

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
static inline const Eurydice_arr_40 *libcrux_iot_ml_dsa_types_as_ref_e9_db(
    const Eurydice_arr_40 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2420
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_180(
    const Eurydice_arr_400 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2420U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1312
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_bb(
    const Eurydice_arr_40 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1312U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2560size_t
*/
typedef struct Eurydice_arr_18_s {
  uint8_t data[2560U];
} Eurydice_arr_18;

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
static inline const Eurydice_arr_18 *libcrux_iot_ml_dsa_types_as_ref_f8_ff(
    const Eurydice_arr_18 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2560
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_59(
    const Eurydice_arr_18 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2560U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2420
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_180(
    Eurydice_arr_400 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2420U;
  return lit;
}

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
static inline Eurydice_dst_ref_shared_22 Eurydice_array_to_slice_shared_6d(
    const Eurydice_arr_83 *a) {
  Eurydice_dst_ref_shared_22 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 4
*/
static inline Eurydice_dst_ref_mut_22 Eurydice_array_to_slice_mut_6d(
    Eurydice_arr_83 *a) {
  Eurydice_dst_ref_mut_22 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_mut_fc_s {
  int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_fc;

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 256
*/
static inline Eurydice_dst_ref_mut_fc Eurydice_array_to_subslice_mut_7f(
    Eurydice_arr_c3 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_mut_fc){.ptr = a->data + r.start,
                                                 .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_shared_fc_s {
  const int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_fc;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 256
*/
static inline Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_200(
    const Eurydice_arr_c3 *a) {
  Eurydice_dst_ref_shared_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)256U;
  return lit;
}

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
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 136
*/
static inline Eurydice_borrow_slice_u8
Eurydice_array_to_subslice_from_shared_8c(const Eurydice_arr_3d *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)136U - r});
}

#define Ok 0
#define Err 1

typedef uint8_t Result_8e_tags;

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
static inline Eurydice_array_u8x8 unwrap_26_ab(Result_8e self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

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
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ee(
    const Eurydice_arr_56 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)768U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 768
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ee(
    Eurydice_arr_56 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)768U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $640size_t
*/
typedef struct Eurydice_arr_c30_s {
  uint8_t data[640U];
} Eurydice_arr_c30;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 640
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_7d(
    const Eurydice_arr_c30 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)640U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 640
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_7d(
    Eurydice_arr_c30 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)640U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $576size_t
*/
typedef struct Eurydice_arr_5f0_s {
  uint8_t data[576U];
} Eurydice_arr_5f0;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 576
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_fa(
    const Eurydice_arr_5f0 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)576U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 576
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_fa(
    Eurydice_arr_5f0 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)576U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $11size_t
*/
typedef struct Eurydice_arr_cb_s {
  uint8_t data[11U];
} Eurydice_arr_cb;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 11
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_da(
    const Eurydice_arr_cb *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)11U;
  return lit;
}

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
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_07(
    const Eurydice_arr_f10 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

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
static inline Eurydice_arr_400 libcrux_iot_ml_dsa_types_zero_ad_1a(void) {
  return (KRML_CLITERAL(Eurydice_arr_400){.data = {0U}});
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $1312size_t
- $2560size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2_s {
  Eurydice_arr_18 signing_key;
  Eurydice_arr_40 verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2;

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
static inline Eurydice_arr_40 libcrux_iot_ml_dsa_types_new_e9_db(
    Eurydice_arr_40 value) {
  return value;
}

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
static inline Eurydice_arr_18 libcrux_iot_ml_dsa_types_new_f8_ff(
    Eurydice_arr_18 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1312
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_bb(
    Eurydice_arr_40 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1312U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2560
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_59(
    Eurydice_arr_18 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2560U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $64size_t
*/
typedef struct Eurydice_arr_06_s {
  uint8_t data[64U];
} Eurydice_arr_06;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 64
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_d8(
    const Eurydice_arr_06 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)64U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $66size_t
*/
typedef struct Eurydice_arr_a2_s {
  uint8_t data[66U];
} Eurydice_arr_a2;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 66
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_39(
    const Eurydice_arr_a2 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)66U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types int32_t
with const generics
- $263size_t
*/
typedef struct Eurydice_arr_13_s {
  int32_t data[263U];
} Eurydice_arr_13;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr_13, size_t

*/
typedef struct Eurydice_dst_ref_mut_4c_s {
  Eurydice_arr_13 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_4c;

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
static inline Eurydice_dst_ref_mut_4c Eurydice_array_to_slice_mut_f6(
    Eurydice_arr_38 *a) {
  Eurydice_dst_ref_mut_4c lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

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
static inline Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_20(
    const Eurydice_arr_13 *a) {
  Eurydice_dst_ref_shared_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)263U;
  return lit;
}

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
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 168
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_7b(
    const Eurydice_arr_27 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)168U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $840size_t
*/
typedef struct Eurydice_arr_12_s {
  uint8_t data[840U];
} Eurydice_arr_12;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 840
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_a8(
    const Eurydice_arr_12 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)840U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types int32_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
int32_t with const generics
- N= 263
*/
static inline Eurydice_dst_ref_mut_fc Eurydice_array_to_subslice_from_mut_96(
    Eurydice_arr_13 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_mut_fc){.ptr = a->data + r,
                                                 .meta = (size_t)263U - r});
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $34size_t
*/
typedef struct Eurydice_arr_48_s {
  uint8_t data[34U];
} Eurydice_arr_48;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 34
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_8d(
    const Eurydice_arr_48 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)34U;
  return lit;
}

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
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_18(
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
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_18(
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
- N= 2
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_26(
    const Eurydice_array_u8x2 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_60_s {
  uint8_t data[32U];
} Eurydice_arr_60;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 32
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_6e(
    const Eurydice_arr_60 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)32U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types int32_t
with const generics
- $8size_t
*/
typedef struct Eurydice_arr_d4_s {
  int32_t data[8U];
} Eurydice_arr_d4;

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 8
*/
static inline Eurydice_dst_ref_shared_fc Eurydice_array_to_subslice_shared_7f(
    const Eurydice_arr_d4 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = a->data + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 8
*/
static inline Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_a7(
    const Eurydice_arr_d4 *a) {
  Eurydice_dst_ref_shared_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t

*/
static inline Eurydice_dst_ref_shared_fc Eurydice_slice_subslice_shared_46(
    Eurydice_dst_ref_shared_fc s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = s.ptr + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int32_t
with const generics
- N= 8
*/
static inline Eurydice_dst_ref_mut_fc Eurydice_array_to_slice_mut_a7(
    Eurydice_arr_d4 *a) {
  Eurydice_dst_ref_mut_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 66
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_362(
    Eurydice_arr_a2 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_361(
    Eurydice_arr_48 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 136
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_d4(
    Eurydice_arr_3d *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)136U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 168
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_7b(
    Eurydice_arr_27 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)168U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 840
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_a8(
    Eurydice_arr_12 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)840U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 64
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_d8(
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
static KRML_MUSTINLINE Eurydice_arr_06
libcrux_secrets_int_public_integers_classify_27_490(Eurydice_arr_06 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 48
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_95(
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
static KRML_MUSTINLINE Eurydice_arr_5f
libcrux_secrets_int_public_integers_classify_27_7d(Eurydice_arr_5f self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 32
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_6e(
    Eurydice_arr_60 *a) {
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
static KRML_MUSTINLINE Eurydice_arr_60
libcrux_secrets_int_public_integers_classify_27_62(Eurydice_arr_60 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $28size_t
*/
typedef struct Eurydice_arr_f1_s {
  uint8_t data[28U];
} Eurydice_arr_f1;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 28
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_c0(
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
static KRML_MUSTINLINE Eurydice_arr_f1
libcrux_secrets_int_public_integers_classify_27_4b(Eurydice_arr_f1 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 4
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_361(
    const Eurydice_array_u8x4 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$136size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_3d
libcrux_secrets_int_public_integers_classify_27_df0(Eurydice_arr_3d self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 136
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_360(
    const Eurydice_arr_3d *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
static inline Eurydice_borrow_slice_u8 Eurydice_slice_subslice_from_shared_6b(
    Eurydice_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr + r,
                                                  .meta = s.meta - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 136
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_360(
    Eurydice_arr_3d *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 136
*/
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_d4(
    const Eurydice_arr_3d *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)136U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
static inline Eurydice_borrow_slice_u8 Eurydice_slice_subslice_to_shared_c6(
    Eurydice_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr, .meta = r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 136
*/
static inline Eurydice_mut_borrow_slice_u8
Eurydice_array_to_subslice_from_mut_8c(Eurydice_arr_3d *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){
      .ptr = a->data + r, .meta = (size_t)136U - r});
}

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
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_36(
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
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f7(
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
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_60(
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
static inline Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_mut_7e(
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
static inline Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f7(
    const Eurydice_arr_88 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)200U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
static inline Eurydice_borrow_slice_u8 Eurydice_slice_subslice_shared_7e(
    Eurydice_borrow_slice_u8 s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
static inline Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_36(
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
static KRML_MUSTINLINE Eurydice_arr_88
libcrux_secrets_int_public_integers_classify_27_c1(Eurydice_arr_88 self) {
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
static KRML_MUSTINLINE Eurydice_borrow_slice_u8
libcrux_secrets_int_classify_public_classify_ref_9b_90(
    Eurydice_borrow_slice_u8 self) {
  return self;
}

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
static KRML_MUSTINLINE Eurydice_arr_b2
libcrux_secrets_int_public_integers_classify_27_54(Eurydice_arr_b2 self) {
  return self;
}

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_mldsa_core_H_DEFINED
#endif /* libcrux_iot_mldsa_core_H */
