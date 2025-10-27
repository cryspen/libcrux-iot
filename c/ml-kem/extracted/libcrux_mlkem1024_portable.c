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

#include "libcrux_mlkem1024_portable.h"

#include "internal/libcrux_mlkem_iot.h"
#include "libcrux_core.h"

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
static void decapsulate_f3(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  libcrux_iot_ml_kem_ind_cca_decapsulate_1b1(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
void libcrux_iot_ml_kem_mlkem1024_portable_decapsulate(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  decapsulate_f3(private_key, ciphertext, ret);
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
static tuple_d1 encapsulate_e0(
    libcrux_iot_ml_kem_types_MlKemPublicKey_64 *public_key,
    uint8_t *randomness) {
  return libcrux_iot_ml_kem_ind_cca_encapsulate_351(public_key, randomness);
}

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_d1 libcrux_iot_ml_kem_mlkem1024_portable_encapsulate(
    libcrux_iot_ml_kem_types_MlKemPublicKey_64 *public_key,
    uint8_t randomness[32U]) {
  return encapsulate_e0(public_key, randomness);
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
static libcrux_iot_ml_kem_mlkem1024_MlKem1024KeyPair generate_keypair_86(
    uint8_t *randomness) {
  return libcrux_iot_ml_kem_ind_cca_generate_keypair_b71(randomness);
}

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_iot_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_iot_ml_kem_mlkem1024_portable_generate_key_pair(
    uint8_t randomness[64U]) {
  return generate_keypair_86(randomness);
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
    libcrux_iot_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_7b(private_key,
                                                            ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_private_key(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext) {
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
    libcrux_iot_ml_kem_types_MlKemPrivateKey_83 *private_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_8a(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_private_key_only(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_83 *private_key) {
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
static KRML_MUSTINLINE bool validate_public_key_44(uint8_t *public_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_public_key_c5(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_public_key(
    libcrux_iot_ml_kem_types_MlKemPublicKey_64 *public_key) {
  return validate_public_key_44(public_key->value);
}
