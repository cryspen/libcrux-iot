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
 * Libcrux: 936916cddc98fa7c87698a18d08336862d718614
 */

#ifndef libcrux_iot_mlkem768_portable_H
#define libcrux_iot_mlkem768_portable_H

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
tuple_e9 libcrux_iot_ml_kem_mlkem768_portable_encapsulate(
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
