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

#ifndef libcrux_iot_mlkem1024_portable_H
#define libcrux_iot_mlkem1024_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_iot_core.h"

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
Eurydice_arr_600 libcrux_iot_ml_kem_mlkem1024_portable_decapsulate(
    const Eurydice_arr_17 *private_key, const Eurydice_arr_00 *ciphertext);

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_62 libcrux_iot_ml_kem_mlkem1024_portable_encapsulate(
    const Eurydice_arr_00 *public_key, Eurydice_arr_600 randomness);

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_f7
libcrux_iot_ml_kem_mlkem1024_portable_generate_key_pair(
    Eurydice_arr_06 randomness);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_private_key(
    const Eurydice_arr_17 *private_key, const Eurydice_arr_00 *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_private_key_only(
    const Eurydice_arr_17 *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_public_key(
    const Eurydice_arr_00 *public_key);

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_mlkem1024_portable_H_DEFINED
#endif /* libcrux_iot_mlkem1024_portable_H */
