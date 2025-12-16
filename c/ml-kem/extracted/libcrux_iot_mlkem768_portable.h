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

#ifndef libcrux_iot_mlkem768_portable_H
#define libcrux_iot_mlkem768_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_iot_core.h"

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
Eurydice_arr_600 libcrux_iot_ml_kem_mlkem768_portable_decapsulate(
    const Eurydice_arr_ea *private_key, const Eurydice_arr_2c *ciphertext);

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_50 libcrux_iot_ml_kem_mlkem768_portable_encapsulate(
    const Eurydice_arr_74 *public_key, Eurydice_arr_600 randomness);

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_5f
libcrux_iot_ml_kem_mlkem768_portable_generate_key_pair(
    Eurydice_arr_06 randomness);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key(
    const Eurydice_arr_ea *private_key, const Eurydice_arr_2c *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key_only(
    const Eurydice_arr_ea *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_public_key(
    const Eurydice_arr_74 *public_key);

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_mlkem768_portable_H_DEFINED
#endif /* libcrux_iot_mlkem768_portable_H */
