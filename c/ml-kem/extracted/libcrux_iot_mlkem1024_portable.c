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
 * Libcrux: 16d98a42e1e298c86bf8eea4d92d3c82eb349f70
 */

#include "libcrux_iot_mlkem1024_portable.h"

#include "internal/libcrux_iot_mlkem_portable.h"
#include "libcrux_iot_core.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.decapsulate with const
generics
- K= 4
- K_SQUARED= 16
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
static Eurydice_arr_600 decapsulate_f3(const Eurydice_arr_17 *private_key,
                                       const Eurydice_arr_00 *ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_decapsulate_1b1(private_key, ciphertext);
}

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
Eurydice_arr_600 libcrux_iot_ml_kem_mlkem1024_portable_decapsulate(
    const Eurydice_arr_17 *private_key, const Eurydice_arr_00 *ciphertext) {
  return decapsulate_f3(private_key, ciphertext);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.encapsulate with const
generics
- K= 4
- K_SQUARED= 16
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static tuple_32 encapsulate_e0(const Eurydice_arr_00 *public_key,
                               const Eurydice_arr_600 *randomness) {
  return libcrux_iot_ml_kem_ind_cca_encapsulate_351(public_key, randomness);
}

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_32 libcrux_iot_ml_kem_mlkem1024_portable_encapsulate(
    const Eurydice_arr_00 *public_key, Eurydice_arr_600 randomness) {
  return encapsulate_e0(public_key, &randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 4
- K_SQUARED= 16
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
static libcrux_iot_ml_kem_types_MlKemKeyPair_f7 generate_keypair_86(
    const Eurydice_arr_06 *randomness) {
  return libcrux_iot_ml_kem_ind_cca_generate_keypair_b71(randomness);
}

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_f7
libcrux_iot_ml_kem_mlkem1024_portable_generate_key_pair(
    Eurydice_arr_06 randomness) {
  return generate_keypair_86(&randomness);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_private_key with
const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE bool validate_private_key_6b(
    const Eurydice_arr_17 *private_key, const Eurydice_arr_00 *ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_7b(private_key,
                                                            ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_private_key(
    const Eurydice_arr_17 *private_key, const Eurydice_arr_00 *ciphertext) {
  return validate_private_key_6b(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_private_key_only
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
static KRML_MUSTINLINE bool validate_private_key_only_44(
    const Eurydice_arr_17 *private_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_8a(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_private_key_only(
    const Eurydice_arr_17 *private_key) {
  return validate_private_key_only_44(private_key);
}

/**
 Public key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_public_key with
const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE bool validate_public_key_44(
    const Eurydice_arr_00 *public_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_public_key_c5(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_public_key(
    const Eurydice_arr_00 *public_key) {
  return validate_public_key_44(public_key);
}
