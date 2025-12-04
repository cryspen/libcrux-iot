/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 146b7dce58cb11ca8010b1c947c3437a959dcd88
 * Eurydice: cdf02f9d8ed0d73f88c0a495c5b79359a51398fc
 * Karamel: 8e7262955105599e91f3a99c9ab3d3387f7046f2
 * F*: unset
 * Libcrux: 1ad7c25705450131b575043e252c944035898962
 */

#ifndef libcrux_iot_mldsa_core_H
#define libcrux_iot_mldsa_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $4627size_t
*/
typedef struct Eurydice_arr_38_s {
  uint8_t data[4627U];
} Eurydice_arr_38;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2592size_t
*/
typedef struct Eurydice_arr_510_s {
  uint8_t data[2592U];
} Eurydice_arr_510;

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
with types Eurydice_arr int32_t[[$256size_t]], size_t

*/
typedef struct Eurydice_dst_ref_shared_59_s {
  const Eurydice_arr_c3 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_59;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr int32_t[[$256size_t]], size_t

*/
typedef struct Eurydice_dst_ref_mut_59_s {
  Eurydice_arr_c3 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_59;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $2592size_t
- $4896size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d_s {
  Eurydice_arr_180 signing_key;
  Eurydice_arr_510 verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1952size_t
*/
typedef struct Eurydice_arr_4a_s {
  uint8_t data[1952U];
} Eurydice_arr_4a;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $48size_t
*/
typedef struct Eurydice_arr_5f_s {
  uint8_t data[48U];
} Eurydice_arr_5f;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2420size_t
*/
typedef struct Eurydice_arr_400_s {
  uint8_t data[2420U];
} Eurydice_arr_400;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2560size_t
*/
typedef struct Eurydice_arr_18_s {
  uint8_t data[2560U];
} Eurydice_arr_18;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_mut_fc_s {
  int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_fc;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $136size_t
*/
typedef struct Eurydice_arr_3d_s {
  uint8_t data[136U];
} Eurydice_arr_3d;

#define Ok 0
#define Err 1

typedef uint8_t Result_a4_tags;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $576size_t
*/
typedef struct Eurydice_arr_5f0_s {
  uint8_t data[576U];
} Eurydice_arr_5f0;

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
A monomorphic instance of Eurydice.dst_ref_shared
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_shared_fc_s {
  const int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_fc;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $64size_t
*/
typedef struct Eurydice_arr_06_s {
  uint8_t data[64U];
} Eurydice_arr_06;

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
with types Eurydice_arr int32_t[[$263size_t]], size_t

*/
typedef struct Eurydice_dst_ref_mut_2c_s {
  Eurydice_arr_13 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_2c;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $840size_t
*/
typedef struct Eurydice_arr_12_s {
  uint8_t data[840U];
} Eurydice_arr_12;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_60_s {
  uint8_t data[32U];
} Eurydice_arr_60;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $28size_t
*/
typedef struct Eurydice_arr_f1_s {
  uint8_t data[28U];
} Eurydice_arr_f1;

/**
A monomorphic instance of Eurydice.arr
with types uint32_t
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_b2_s {
  uint32_t data[2U];
} Eurydice_arr_b2;

#define libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError 0
#define libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError 1

typedef uint8_t libcrux_iot_ml_dsa_types_SigningError;

#define libcrux_iot_ml_dsa_types_VerificationError_MalformedHintError 0
#define libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError \
  1
#define libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError \
  2
#define libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError \
  3

typedef uint8_t libcrux_iot_ml_dsa_types_VerificationError;

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_mldsa_core_H_DEFINED
#endif /* libcrux_iot_mldsa_core_H */
