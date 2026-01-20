/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 146b7dce58cb11ca8010b1c947c3437a959dcd88
 * Eurydice: cdf02f9d8ed0d73f88c0a495c5b79359a51398fc
 * Karamel: 8e7262955105599e91f3a99c9ab3d3387f7046f2
 * F*: 89901492c020c74b82d811d27f3149c222d9b8b5
 * Libcrux: 2259f47ca2a2a060c9fd147ccc78ed3588bfd288
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
tuple_32 libcrux_iot_ml_kem_mlkem1024_portable_encapsulate(
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
