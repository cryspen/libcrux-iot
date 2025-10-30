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

#ifndef libcrux_mlkem768_portable_H
#define libcrux_mlkem768_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
void libcrux_iot_ml_kem_mlkem768_portable_decapsulate(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_iot_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext,
    uint8_t ret[32U]);

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_f4 libcrux_iot_ml_kem_mlkem768_portable_encapsulate(
    libcrux_iot_ml_kem_types_MlKemPublicKey_30 *public_key,
    uint8_t randomness[32U]);

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_iot_ml_kem_mlkem768_MlKem768KeyPair
libcrux_iot_ml_kem_mlkem768_portable_generate_key_pair(uint8_t randomness[64U]);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_iot_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key_only(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_d9 *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_public_key(
    libcrux_iot_ml_kem_types_MlKemPublicKey_30 *public_key);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem768_portable_H_DEFINED
#endif /* libcrux_mlkem768_portable_H */
