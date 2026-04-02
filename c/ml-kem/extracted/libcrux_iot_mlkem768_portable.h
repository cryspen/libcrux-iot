/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 377317d6b25702c46ffff072fa00a3e32095e46f
 * Eurydice: b227478b67c6a6e2ff611f978f10d6b7f26472ac
 * Karamel: 4e64d915da3c172d1dfad805b8e1a46beff938bc
 * F*: 89901492c020c74b82d811d27f3149c222d9b8b5
 * Libcrux: 0ab0448a17b81dc787e95a2c646c27ae75247f7b
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
