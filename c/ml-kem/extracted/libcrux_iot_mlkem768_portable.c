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
 * Libcrux: 1bf38a701c22669699956643df22dd9ff22c0456
 */

#include "libcrux_iot_mlkem768_portable.h"

#include "internal/libcrux_iot_mlkem_portable.h"
#include "libcrux_iot_core.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.decapsulate with const
generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
static Eurydice_arr_600 decapsulate_54(const Eurydice_arr_ea *private_key,
                                       const Eurydice_arr_2c *ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_decapsulate_1b0(private_key, ciphertext);
}

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
Eurydice_arr_600 libcrux_iot_ml_kem_mlkem768_portable_decapsulate(
    const Eurydice_arr_ea *private_key, const Eurydice_arr_2c *ciphertext) {
  return decapsulate_54(private_key, ciphertext);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.encapsulate with const
generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static tuple_e9 encapsulate_35(const Eurydice_arr_74 *public_key,
                               const Eurydice_arr_600 *randomness) {
  return libcrux_iot_ml_kem_ind_cca_encapsulate_350(public_key, randomness);
}

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_e9 libcrux_iot_ml_kem_mlkem768_portable_encapsulate(
    const Eurydice_arr_74 *public_key, Eurydice_arr_600 randomness) {
  return encapsulate_35(public_key, &randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static libcrux_iot_ml_kem_types_MlKemKeyPair_5f generate_keypair_06(
    const Eurydice_arr_06 *randomness) {
  return libcrux_iot_ml_kem_ind_cca_generate_keypair_b70(randomness);
}

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_5f
libcrux_iot_ml_kem_mlkem768_portable_generate_key_pair(
    Eurydice_arr_06 randomness) {
  return generate_keypair_06(&randomness);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_private_key with
const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE bool validate_private_key_31(
    const Eurydice_arr_ea *private_key, const Eurydice_arr_2c *ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_b3(private_key,
                                                            ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key(
    const Eurydice_arr_ea *private_key, const Eurydice_arr_2c *ciphertext) {
  return validate_private_key_31(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_private_key_only
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
static KRML_MUSTINLINE bool validate_private_key_only_41(
    const Eurydice_arr_ea *private_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_39(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key_only(
    const Eurydice_arr_ea *private_key) {
  return validate_private_key_only_41(private_key);
}

/**
 Public key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_public_key with
const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE bool validate_public_key_41(
    const Eurydice_arr_74 *public_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_public_key_64(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_public_key(
    const Eurydice_arr_74 *public_key) {
  return validate_public_key_41(public_key);
}
