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

#ifndef libcrux_core_H
#define libcrux_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_10;

#define core_option_None 0
#define core_option_Some 1

typedef uint8_t core_option_Option_08_tags;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASignature
with const generics
- $4627size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSASignature_9b_s {
  uint8_t value[4627U];
} libcrux_iot_ml_dsa_types_MLDSASignature_9b;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAVerificationKey
with const generics
- $2592size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe_s {
  uint8_t value[2592U];
} libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASigningKey
with const generics
- $4896size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSASigningKey_a3_s {
  uint8_t value[4896U];
} libcrux_iot_ml_dsa_types_MLDSASigningKey_a3;

#define libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError 0
#define libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError 1

typedef uint8_t libcrux_iot_ml_dsa_types_SigningError;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature[[$4627size_t]],
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct core_result_Result_f2_s {
  core_result_Result_10 tag;
  union {
    libcrux_iot_ml_dsa_types_MLDSASignature_9b case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} core_result_Result_f2;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $2592size_t
- $4896size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d_s {
  libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 signing_key;
  libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASignature
with const generics
- $3309size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSASignature_8f_s {
  uint8_t value[3309U];
} libcrux_iot_ml_dsa_types_MLDSASignature_8f;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAVerificationKey
with const generics
- $1952size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea_s {
  uint8_t value[1952U];
} libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASigningKey
with const generics
- $4032size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSASigningKey_22_s {
  uint8_t value[4032U];
} libcrux_iot_ml_dsa_types_MLDSASigningKey_22;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature[[$3309size_t]],
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct core_result_Result_3e_s {
  core_result_Result_10 tag;
  union {
    libcrux_iot_ml_dsa_types_MLDSASignature_8f case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} core_result_Result_3e;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $1952size_t
- $4032size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_06_s {
  libcrux_iot_ml_dsa_types_MLDSASigningKey_22 signing_key;
  libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_06;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASignature
with const generics
- $2420size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSASignature_64_s {
  uint8_t value[2420U];
} libcrux_iot_ml_dsa_types_MLDSASignature_64;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAVerificationKey
with const generics
- $1312size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c_s {
  uint8_t value[1312U];
} libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c;

#define libcrux_iot_ml_dsa_types_VerificationError_MalformedHintError 0
#define libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError \
  1
#define libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError \
  2
#define libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError \
  3

typedef uint8_t libcrux_iot_ml_dsa_types_VerificationError;

/**
A monomorphic instance of core.result.Result
with types (), libcrux_iot_ml_dsa_types_VerificationError

*/
typedef struct core_result_Result_5c_s {
  core_result_Result_10 tag;
  libcrux_iot_ml_dsa_types_VerificationError f0;
} core_result_Result_5c;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASigningKey
with const generics
- $2560size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSASigningKey_b8_s {
  uint8_t value[2560U];
} libcrux_iot_ml_dsa_types_MLDSASigningKey_b8;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature[[$2420size_t]],
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct core_result_Result_ba_s {
  core_result_Result_10 tag;
  union {
    libcrux_iot_ml_dsa_types_MLDSASignature_64 case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} core_result_Result_ba;

/**
A monomorphic instance of core.result.Result
with types (), libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct core_result_Result_87_s {
  core_result_Result_10 tag;
  libcrux_iot_ml_dsa_types_SigningError f0;
} core_result_Result_87;

/**
A monomorphic instance of core.option.Option
with types uint8_t[11size_t]

*/
typedef struct core_option_Option_30_s {
  core_option_Option_08_tags tag;
  uint8_t f0[11U];
} core_option_Option_30;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $1312size_t
- $2560size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2_s {
  libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 signing_key;
  libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2;

#if defined(__cplusplus)
}
#endif

#define libcrux_core_H_DEFINED
#endif /* libcrux_core_H */
