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
 * Libcrux: ded8c0f46a4ee8f93a6474c5aec0b9f13c3501c5
 */

#ifndef libcrux_core_H
#define libcrux_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

/**
A monomorphic instance of libcrux_iot_ml_kem.types.MlKemPublicKey
with const generics
- $1568size_t
*/
typedef struct libcrux_iot_ml_kem_types_MlKemPublicKey_64_s {
  uint8_t value[1568U];
} libcrux_iot_ml_kem_types_MlKemPublicKey_64;

/**
A monomorphic instance of libcrux_iot_ml_kem.types.MlKemPrivateKey
with const generics
- $3168size_t
*/
typedef struct libcrux_iot_ml_kem_types_MlKemPrivateKey_83_s {
  uint8_t value[3168U];
} libcrux_iot_ml_kem_types_MlKemPrivateKey_83;

typedef struct libcrux_iot_ml_kem_mlkem1024_MlKem1024KeyPair_s {
  libcrux_iot_ml_kem_types_MlKemPrivateKey_83 sk;
  libcrux_iot_ml_kem_types_MlKemPublicKey_64 pk;
} libcrux_iot_ml_kem_mlkem1024_MlKem1024KeyPair;

typedef struct libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext_s {
  uint8_t value[1568U];
} libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext;

/**
A monomorphic instance of K.
with types libcrux_iot_ml_kem_types_MlKemCiphertext[[$1568size_t]],
uint8_t[32size_t]

*/
typedef struct tuple_d1_s {
  libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext fst;
  uint8_t snd[32U];
} tuple_d1;

/**
A monomorphic instance of libcrux_iot_ml_kem.types.MlKemPublicKey
with const generics
- $1184size_t
*/
typedef struct libcrux_iot_ml_kem_types_MlKemPublicKey_30_s {
  uint8_t value[1184U];
} libcrux_iot_ml_kem_types_MlKemPublicKey_30;

/**
A monomorphic instance of libcrux_iot_ml_kem.types.MlKemPrivateKey
with const generics
- $2400size_t
*/
typedef struct libcrux_iot_ml_kem_types_MlKemPrivateKey_d9_s {
  uint8_t value[2400U];
} libcrux_iot_ml_kem_types_MlKemPrivateKey_d9;

typedef struct libcrux_iot_ml_kem_mlkem768_MlKem768KeyPair_s {
  libcrux_iot_ml_kem_types_MlKemPrivateKey_d9 sk;
  libcrux_iot_ml_kem_types_MlKemPublicKey_30 pk;
} libcrux_iot_ml_kem_mlkem768_MlKem768KeyPair;

typedef struct libcrux_iot_ml_kem_mlkem768_MlKem768Ciphertext_s {
  uint8_t value[1088U];
} libcrux_iot_ml_kem_mlkem768_MlKem768Ciphertext;

/**
A monomorphic instance of K.
with types libcrux_iot_ml_kem_types_MlKemCiphertext[[$1088size_t]],
uint8_t[32size_t]

*/
typedef struct tuple_f4_s {
  libcrux_iot_ml_kem_mlkem768_MlKem768Ciphertext fst;
  uint8_t snd[32U];
} tuple_f4;

#if defined(__cplusplus)
}
#endif

#define libcrux_core_H_DEFINED
#endif /* libcrux_core_H */
