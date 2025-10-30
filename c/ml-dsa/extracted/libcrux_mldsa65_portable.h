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
 * Libcrux: 4c0c9248a551dd42901dc5208f62cc9e92e7e0c3
 */

#ifndef libcrux_mldsa65_portable_H
#define libcrux_mldsa65_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"
#include "libcrux_iot_sha3.h"

#define libcrux_iot_ml_dsa_constants_Eta_Two 2
#define libcrux_iot_ml_dsa_constants_Eta_Four 4

typedef uint8_t libcrux_iot_ml_dsa_constants_Eta;

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT ((size_t)8U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_SIMD_UNITS_IN_RING_ELEMENT \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT /    \
   LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T ((size_t)13U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH \
  ((size_t)23U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T         \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH \
  ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN ((size_t)255U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS ((int32_t)8380417)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_GAMMA2_V261_888 ((int32_t)261888)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_GAMMA2_V95_232 ((int32_t)95232)

typedef int32_t libcrux_iot_ml_dsa_constants_Gamma2;

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_KEY_GENERATION_RANDOMNESS_SIZE \
  ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_MASK_SEED_SIZE ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_MESSAGE_REPRESENTATIVE_SIZE ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN ((size_t)814U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T *     \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T *     \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_SIGNING_RANDOMNESS_SIZE ((size_t)32U)

int32_t libcrux_iot_ml_dsa_constants_beta(size_t ones_in_verifier_challenge,
                                          libcrux_iot_ml_dsa_constants_Eta eta);

size_t libcrux_iot_ml_dsa_constants_commitment_ring_element_size(
    size_t bits_per_commitment_coefficient);

size_t libcrux_iot_ml_dsa_constants_commitment_vector_size(
    size_t bits_per_commitment_coefficient, size_t rows_in_a);

size_t libcrux_iot_ml_dsa_constants_error_ring_element_size(
    size_t bits_per_error_coefficient);

size_t libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(
    size_t bits_per_gamma1_coefficient);

size_t libcrux_iot_ml_dsa_constants_signature_size(
    size_t rows_in_a, size_t columns_in_a, size_t max_ones_in_hint,
    size_t commitment_hash_size, size_t bits_per_gamma1_coefficient);

size_t libcrux_iot_ml_dsa_constants_signing_key_size(
    size_t rows_in_a, size_t columns_in_a, size_t error_ring_element_size);

size_t libcrux_iot_ml_dsa_constants_verification_key_size(size_t rows_in_a);

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_COMMITMENT_COEFFICIENT \
  ((size_t)6U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_ERROR_COEFFICIENT \
  ((size_t)3U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_GAMMA1_COEFFICIENT \
  ((size_t)18U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE \
  ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA \
  (libcrux_iot_ml_dsa_constants_Eta_Two)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT ((size_t)17U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2 \
  ((LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS - (int32_t)1) / (int32_t)88)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT ((size_t)80U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE \
  ((size_t)39U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_COMMITMENT_COEFFICIENT \
  ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_ERROR_COEFFICIENT \
  ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_GAMMA1_COEFFICIENT \
  ((size_t)20U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A ((size_t)5U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE \
  ((size_t)48U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA \
  (libcrux_iot_ml_dsa_constants_Eta_Four)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT ((size_t)19U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2 \
  ((LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS - (int32_t)1) / (int32_t)32)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT ((size_t)55U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE \
  ((size_t)49U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A ((size_t)6U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_COMMITMENT_COEFFICIENT \
  ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_ERROR_COEFFICIENT \
  ((size_t)3U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_GAMMA1_COEFFICIENT \
  ((size_t)20U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A ((size_t)7U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE \
  ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA \
  (libcrux_iot_ml_dsa_constants_Eta_Two)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT ((size_t)19U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2 \
  ((LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS - (int32_t)1) / (int32_t)32)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT ((size_t)75U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE \
  ((size_t)60U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A ((size_t)8U)

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_dsa::constants::Eta}
*/
libcrux_iot_ml_dsa_constants_Eta libcrux_iot_ml_dsa_constants_clone_44(
    libcrux_iot_ml_dsa_constants_Eta *self);

size_t libcrux_iot_ml_dsa_encoding_error_chunk_size(
    libcrux_iot_ml_dsa_constants_Eta eta);

void libcrux_iot_ml_dsa_encoding_signature_set_hint(Eurydice_slice out_hint,
                                                    size_t i, size_t j);

#define LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT ((size_t)13U)

#define LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW ((size_t)10U)

#define LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT \
  ((size_t)10U)

typedef libcrux_iot_sha3_portable_KeccakState
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256;

libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
    Eurydice_slice input);

void libcrux_iot_ml_dsa_hash_functions_portable_shake128(Eurydice_slice input,
                                                         Eurydice_slice out);

typedef struct libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4_s {
  libcrux_iot_sha3_state_KeccakState state0;
  libcrux_iot_sha3_state_KeccakState state1;
  libcrux_iot_sha3_state_KeccakState state2;
  libcrux_iot_sha3_state_KeccakState state3;
} libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4;

libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_x4(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3);

void libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state, uint8_t *out0,
    uint8_t *out1, uint8_t *out2, uint8_t *out3);

typedef struct uint8_t_168size_t__x4_s {
  uint8_t fst[168U];
  uint8_t snd[168U];
  uint8_t thd[168U];
  uint8_t f3[168U];
} uint8_t_168size_t__x4;

uint8_t_168size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state);

typedef struct libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4_s {
  libcrux_iot_sha3_state_KeccakState state0;
  libcrux_iot_sha3_state_KeccakState state1;
  libcrux_iot_sha3_state_KeccakState state2;
  libcrux_iot_sha3_state_KeccakState state3;
} libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4;

libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_init_absorb_x4(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3);

typedef struct uint8_t_136size_t__x4_s {
  uint8_t fst[136U];
  uint8_t snd[136U];
  uint8_t thd[136U];
  uint8_t f3[136U];
} uint8_t_136size_t__x4;

uint8_t_136size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_first_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state);

uint8_t_136size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state);

void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state, uint8_t ret[136U]);

void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state, uint8_t ret[136U]);

typedef libcrux_iot_sha3_portable_KeccakState
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128;

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_b5(
    Eurydice_slice input);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_b5(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *out);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_b5(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake128_e2(
    Eurydice_slice input, Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_33(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self, uint8_t *out0,
    uint8_t *out1, uint8_t *out2, uint8_t *out3);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
uint8_t_168size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_a1(
    Eurydice_slice input);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_a1(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t ret[136U]);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_a1(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t ret[136U]);

typedef libcrux_iot_sha3_portable_incremental_Shake256Xof
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof;

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice input);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice input);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
libcrux_iot_sha3_keccak_KeccakXofState_c7
libcrux_iot_ml_dsa_hash_functions_portable_init_88(void);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_x4_29(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
uint8_t_136size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
uint8_t_136size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self);

#define LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE128_BLOCK_SIZE ((size_t)168U)

#define LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE128_FIVE_BLOCKS_SIZE \
  (LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE128_BLOCK_SIZE * (size_t)5U)

#define LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE256_BLOCK_SIZE ((size_t)136U)

typedef struct uint8_t_x2_s {
  uint8_t fst;
  uint8_t snd;
} uint8_t_x2;

uint16_t libcrux_iot_ml_dsa_sample_generate_domain_separator(uint8_t_x2 _);

void libcrux_iot_ml_dsa_sample_add_domain_separator(Eurydice_slice slice,
                                                    uint8_t_x2 indices,
                                                    uint8_t ret[34U]);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_ERROR_COEFFICIENT))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_SIGNING_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_signing_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,              \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,           \
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_VERIFICATION_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_verification_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A))

void libcrux_iot_ml_dsa_sample_add_error_domain_separator(
    Eurydice_slice slice, uint16_t domain_separator, uint8_t ret[66U]);

typedef struct libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients_s {
  int32_t values[8U];
} libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients;

libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
libcrux_iot_ml_dsa_simd_portable_vector_type_zero(void);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
libcrux_iot_ml_dsa_simd_portable_zero_c5(void);

void libcrux_iot_ml_dsa_simd_portable_vector_type_from_coefficient_array(
    Eurydice_slice array,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_from_coefficient_array_c5(
    Eurydice_slice array,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out);

void libcrux_iot_ml_dsa_simd_portable_vector_type_to_coefficient_array(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *value,
    Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_to_coefficient_array_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *value,
    Eurydice_slice out);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_add(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_add_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_subtract_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs);

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS ((int32_t)8380417)

bool libcrux_iot_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t bound);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
bool libcrux_iot_ml_dsa_simd_portable_infinity_norm_exceeds_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t bound);

typedef struct int32_t_x2_s {
  int32_t fst;
  int32_t snd;
} int32_t_x2;

int32_t_x2 libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(
    int32_t gamma2, int32_t r);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose(
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *low,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *high);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_decompose_c5(
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *low,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *high);

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_one_hint(
    int32_t low, int32_t high, int32_t gamma2);

size_t libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_hint(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *low,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *high,
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *hint);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t libcrux_iot_ml_dsa_simd_portable_compute_hint_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *low,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *high,
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *hint);

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_use_one_hint(int32_t gamma2,
                                                                 int32_t r,
                                                                 int32_t hint);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_use_hint(
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *hint);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_use_hint_c5(
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *hint);

uint64_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint64_t value);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (32U)

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (58728449ULL)

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
    int64_t value);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_montgomery_multiply_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs);

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(int32_t fe);

int32_t_x2 libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round_element(
    int32_t t);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *t0,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *t1);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_power2round_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *t0,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *t1);

size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
    Eurydice_slice randomness, Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_c5(
    Eurydice_slice randomness, Eurydice_slice out);

size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
    Eurydice_slice randomness, Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_c5(
    Eurydice_slice randomness, Eurydice_slice out);

size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
    Eurydice_slice randomness, Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_c5(
    Eurydice_slice randomness, Eurydice_slice out);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized, size_t gamma1_exponent);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_gamma1_serialize_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized, size_t gamma1_exponent);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK \
  ((LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1                     \
    << 1U) -                                                                                                        \
   (int32_t)1)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_BITMASK \
  ((LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1                     \
    << 1U) -                                                                                                        \
   (int32_t)1)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit);

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out,
    size_t gamma1_exponent);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_gamma1_deserialize_c5(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out,
    size_t gamma1_exponent);

void libcrux_iot_ml_dsa_simd_portable_encoding_commitment_serialize(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_commitment_serialize_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA \
  ((int32_t)4)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA \
  ((int32_t)2)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize(
    libcrux_iot_ml_dsa_constants_Eta eta,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_error_serialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA \
  ((int32_t)4)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_4(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_units);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA \
  ((int32_t)2)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_2(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit);

void libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_error_deserialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out);

int32_t libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
    int32_t t0);

void libcrux_iot_ml_dsa_simd_portable_encoding_t0_serialize(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_serialize_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice out);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK \
  (((int32_t)1 << (uint32_t)(int32_t)                                                         \
        LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) -                               \
   (int32_t)1)

void libcrux_iot_ml_dsa_simd_portable_encoding_t0_deserialize(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_deserialize_c5(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out);

void libcrux_iot_ml_dsa_simd_portable_encoding_t1_serialize(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_serialize_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice out);

void libcrux_iot_ml_dsa_simd_portable_encoding_t1_deserialize(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_deserialize_c5(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t c);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_99(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_7(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -2608894
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_990(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -518909
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_6(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 237124
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_991(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -777960
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a8(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -876248
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 466468
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d9(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 1826347
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_992(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 2353451
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -359251
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a80(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= -2091905
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_95(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= 3119733
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -2884855
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 3111497
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d90(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 2680103
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 2725464
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_993(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 1024112
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1c(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -1079900
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 3585928
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_44(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -549488
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a81(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1119584
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1f(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= 2619752
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_950(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2108549
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2118186
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= -3859737
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_e4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1399561
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -3277672
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_05(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 1757237
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d91(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -19422
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3a(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 4010497
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 280005
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_3(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int32_t fe, int32_t fer);

void libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta1, int32_t zeta2);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta_0, int32_t zeta_1);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta0, int32_t zeta1, int32_t zeta2, int32_t zeta3);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta_0, int32_t zeta_1, int32_t zeta_2, int32_t zeta_3);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_units);

void libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta0, int32_t zeta1, int32_t zeta2, int32_t zeta3);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta0, int32_t zeta1, int32_t zeta2, int32_t zeta3);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta0, int32_t zeta1);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta_00, int32_t zeta_01);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta1);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *self);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 280005
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_99(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 4010497
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1c(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -19422
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 1757237
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_44(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -3277672
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a8(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1399561
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1f(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= -3859737
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_95(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2118186
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2108549
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= 2619752
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_e4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1119584
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -549488
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_05(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 3585928
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d9(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -1079900
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3a(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 1024112
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 2725464
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 2680103
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_990(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 3111497
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -2884855
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a80(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= 3119733
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_950(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= -2091905
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -359251
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 2353451
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d90(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 1826347
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 466468
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_991(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -876248
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a81(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -777960
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 237124
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d91(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -518909
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_992(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -2608894
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_993(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_invert_ntt_montgomery_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_units);

uint8_t_x2 libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
    size_t index, size_t width);

/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients

*/
typedef struct libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d_s {
  libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients simd_units[32U];
} libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d;

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.zero_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
libcrux_iot_ml_dsa_polynomial_zero_c2_08(void);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_field_modulus with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.from_i32_array_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
    Eurydice_slice array,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result);

/**
 Sample and write out up to four ring elements.

 If i <= `elements_requested`, a field element with domain separated
 seed according to the provided index is generated in
 `tmp_stack[i]`. After successful rejection sampling in
 `tmp_stack[i]`, the ring element is written to `matrix` at the
 provided index in `indices[i]`.
 `rand_stack` is a working buffer that holds initial Shake output.
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_up_to_four_ring_elements_flat with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
    size_t columns, Eurydice_slice seed, Eurydice_slice matrix,
    uint8_t *rand_stack0, uint8_t *rand_stack1, uint8_t *rand_stack2,
    uint8_t *rand_stack3, Eurydice_slice tmp_stack, size_t start_index,
    size_t elements_requested);

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.matrix_flat
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 with const generics

*/
void libcrux_iot_ml_dsa_samplex4_matrix_flat_15(size_t columns,
                                                Eurydice_slice seed,
                                                Eurydice_slice matrix);

/**
This function found in impl {libcrux_iot_ml_dsa::samplex4::X4Sampler for
libcrux_iot_ml_dsa::samplex4::portable::PortableSampler}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.portable.matrix_flat_ad
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
    size_t columns, Eurydice_slice seed, Eurydice_slice matrix);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_4 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_08(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_2 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_08(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice randomness,
    size_t *sampled, int32_t *out);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_four_error_ring_elements with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice seed,
    uint16_t start_index, Eurydice_slice re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.sample_s1_and_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice seed,
    Eurydice_slice s1_s2);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_ntt_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt_multiply_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *lhs,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *rhs);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.add_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_polynomial_add_c2_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *self,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *rhs);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.invert_ntt_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re);

/**
 Compute InvertNTT(Â ◦ ŝ₁) + s₂
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_as1_plus_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_slice a_as_ntt,
    Eurydice_slice s1_ntt, Eurydice_slice s1_s2, Eurydice_slice result);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.power2round_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(Eurydice_slice t,
                                                         Eurydice_slice t1);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t1_serialize_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
    Eurydice_slice seed, Eurydice_slice t1,
    Eurydice_slice verification_key_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 64
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_24(
    Eurydice_slice input, uint8_t *out);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256_a1
with const generics
- OUTPUT_LENGTH= 64
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
    Eurydice_slice input, uint8_t *out);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_error_serialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t0_serialize_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.signing_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
void libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t error_ring_element_size,
    Eurydice_slice seed_matrix, Eurydice_slice seed_signing,
    Eurydice_slice verification_key, Eurydice_slice s1_2, Eurydice_slice t0,
    Eurydice_slice signing_key_serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.generate_key_pair with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_generate_key_pair_c4(
    uint8_t randomness[32U], Eurydice_slice signing_key,
    Eurydice_slice verification_key);

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_generate_key_pair(
    uint8_t randomness[32U], uint8_t *signing_key, uint8_t *verification_key);

/**
 Generate an ML-DSA-44 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2
libcrux_iot_ml_dsa_ml_dsa_44_portable_generate_key_pair(
    uint8_t randomness[32U]);

typedef struct libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext_s {
  Eurydice_slice context;
  core_option_Option_30 pre_hash_oid;
} libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext;

#define libcrux_iot_ml_dsa_pre_hash_DomainSeparationError_ContextTooLongError 0

typedef uint8_t libcrux_iot_ml_dsa_pre_hash_DomainSeparationError;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext,
libcrux_iot_ml_dsa_pre_hash_DomainSeparationError

*/
typedef struct core_result_Result_80_s {
  core_result_Result_10 tag;
  union {
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError case_Err;
  } val;
} core_result_Result_80;

/**
 `context` must be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
core_result_Result_80 libcrux_iot_ml_dsa_pre_hash_new_c9(
    Eurydice_slice context, core_option_Option_30 pre_hash_oid);

/**
 Returns the pre-hash OID, if any.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
core_option_Option_30 *libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self);

/**
 Returns the context, guaranteed to be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
Eurydice_slice libcrux_iot_ml_dsa_pre_hash_context_c9(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_commitment_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_COMMITMENT_COEFFICIENT))

bool libcrux_iot_ml_dsa_sample_inside_out_shuffle(Eurydice_slice randomness,
                                                  size_t *out_index,
                                                  uint64_t *signs,
                                                  int32_t *result);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA                 \
  (libcrux_iot_ml_dsa_constants_beta(                                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_GAMMA1_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of core.option.Option
with types libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext

*/
typedef struct core_option_Option_e3_s {
  core_option_Option_08_tags tag;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext f0;
} core_option_Option_e3;

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_error_deserialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice serialized,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.error.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t ring_element_size,
    Eurydice_slice serialized, Eurydice_slice ring_elements);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t0_deserialize_08(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.t0.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
    Eurydice_slice serialized, Eurydice_slice ring_elements);

/**
 This corresponds to line 6 in algorithm 7 in FIPS 204 (line 7 in algorithm
 8, resp.).

 If `domain_separation_context` is supplied, applies domain
 separation and length encoding to the context string,
 before appending the message (in the regular variant) or the
 pre-hash OID as well as the pre-hashed message digest. Otherwise,
 it is assumed that `message` already contains domain separation
 information.

 In FIPS 204 M' is the concatenation of the domain separated context, any
 potential pre-hash OID and the message (or the message pre-hash). We do not
 explicitely construct the concatenation in memory since it is of statically
 unknown length, but feed its components directly into the incremental XOF.

 Refer to line 10 of Algorithm 2 (and line 5 of Algorithm 3, resp.) in [FIPS
 204](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#section.5)
 for details on the domain separation for regular ML-DSA. Line
 23 of Algorithm 4 (and line 18 of Algorithm 5,resp.) describe domain separation
 for the HashMl-DSA variant.
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.derive_message_representative with types
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
void libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
    Eurydice_slice verification_key_hash,
    core_option_Option_e3 *domain_separation_context, Eurydice_slice message,
    uint8_t *message_representative);

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 576
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_1b(
    Eurydice_slice input, uint8_t *out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.hash_functions.portable.shake256_x4_29 with const generics
- OUT_LEN= 576
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_1b(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, uint8_t *out0, uint8_t *out1, uint8_t *out2,
    uint8_t *out3);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
    size_t gamma1_exponent, Eurydice_slice serialized,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result);

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 640
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(
    Eurydice_slice input, uint8_t *out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.hash_functions.portable.shake256_x4_29 with const generics
- OUT_LEN= 640
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_c8(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, uint8_t *out0, uint8_t *out1, uint8_t *out2,
    uint8_t *out3);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256_a1
with const generics
- OUTPUT_LENGTH= 576
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_1b(
    Eurydice_slice input, uint8_t *out);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256_a1
with const generics
- OUTPUT_LENGTH= 640
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c8(
    Eurydice_slice input, uint8_t *out);

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_mask_ring_element_1b(
    uint8_t *seed,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result,
    size_t gamma1_exponent);

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(size_t dimension,
                                                     size_t gamma1_exponent,
                                                     uint8_t *seed,
                                                     uint16_t *domain_separator,
                                                     Eurydice_slice mask);

/**
 Compute InvertNTT(Â ◦ ŷ)
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_matrix_x_mask
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(size_t rows_in_a,
                                                        size_t columns_in_a,
                                                        Eurydice_slice matrix,
                                                        Eurydice_slice mask,
                                                        Eurydice_slice result);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.decompose_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(size_t dimension,
                                                       int32_t gamma2,
                                                       Eurydice_slice t,
                                                       Eurydice_slice low,
                                                       Eurydice_slice high);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.commitment.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_commitment_serialize_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.commitment.serialize_vector with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
    size_t ring_element_size, Eurydice_slice vector, Eurydice_slice serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_challenge_ring_element with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
    Eurydice_slice seed, size_t number_of_ones,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.vector_times_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
    Eurydice_slice vector,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *ring_element);

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.add_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_add_vectors_08(size_t dimension,
                                              Eurydice_slice lhs,
                                              Eurydice_slice rhs);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.subtract_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_polynomial_subtract_c2_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *self,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *rhs);

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.subtract_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_subtract_vectors_08(size_t dimension,
                                                   Eurydice_slice lhs,
                                                   Eurydice_slice rhs);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.infinity_norm_exceeds_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
bool libcrux_iot_ml_dsa_polynomial_infinity_norm_exceeds_c2_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *self,
    int32_t bound);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.arithmetic.vector_infinity_norm_exceeds with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
    Eurydice_slice vector, int32_t bound);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.to_i32_array_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_polynomial_to_i32_array_c2_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *self,
    int32_t ret[256U]);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.make_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
size_t libcrux_iot_ml_dsa_arithmetic_make_hint_08(Eurydice_slice low,
                                                  Eurydice_slice high,
                                                  int32_t gamma2,
                                                  Eurydice_slice hint);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_gamma1_serialize_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized, size_t gamma1_exponent);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_signature_serialize_08(
    Eurydice_slice commitment_hash, Eurydice_slice signer_response,
    Eurydice_slice hint, size_t commitment_hash_size, size_t columns_in_a,
    size_t rows_in_a, size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, Eurydice_slice signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
    Eurydice_slice signing_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context, uint8_t randomness[32U],
    uint8_t *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
core_result_Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
core_result_Result_ba libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_c4(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]);

/**
 Sign.
*/
core_result_Result_ba
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]);

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_ba libcrux_iot_ml_dsa_ml_dsa_44_portable_sign(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]);

/**
 Sign.
*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature);

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_87 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_mut(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U],
    uint8_t *signature);

extern const uint8_t libcrux_iot_ml_dsa_pre_hash_SHAKE128_OID[11U];

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
void libcrux_iot_ml_dsa_pre_hash_oid_0b(uint8_t ret[11U]);

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.pre_hash.hash_0b
with types libcrux_iot_ml_dsa_hash_functions_portable_Shake128
with const generics

*/
void libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(Eurydice_slice message,
                                            Eurydice_slice output);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_pre_hashed_mut with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_mut_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U],
    uint8_t *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
core_result_Result_ba
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]);

/**
 Sign (pre-hashed).
*/
core_result_Result_ba
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_pre_hashed_shake128(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]);

/**
 Generate a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_ba
libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_pre_hashed_shake128(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_SIGNATURE_SIZE \
  (libcrux_iot_ml_dsa_constants_signature_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,            \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,         \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT,     \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t1_deserialize_08(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.deserialize with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
    size_t rows_in_a, size_t verification_key_size, Eurydice_slice serialized,
    Eurydice_slice t1);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
core_result_Result_5c libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
    size_t columns_in_a, size_t rows_in_a, size_t commitment_hash_size,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, size_t signature_size, Eurydice_slice serialized,
    Eurydice_slice out_commitment_hash, Eurydice_slice out_signer_response,
    Eurydice_slice out_hint);

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_ring_element_08(
    Eurydice_slice seed, uint8_t_x2 indices,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *out,
    uint8_t *rand_stack, uint8_t *rand_block, int32_t *tmp_stack);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce with const
generics
- SHIFT_BY= 13
*/
void libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_84(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.shift_left_then_reduce_c5 with const generics
- SHIFT_BY= 13
*/
void libcrux_iot_ml_dsa_simd_portable_shift_left_then_reduce_c5_84(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.shift_left_then_reduce
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics
- SHIFT_BY= 13
*/
void libcrux_iot_ml_dsa_arithmetic_shift_left_then_reduce_41(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re);

/**
 Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_w_approx
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_slice seed,
    uint8_t *rand_stack, uint8_t *rand_block, int32_t *tmp_stack,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *poly_slot,
    Eurydice_slice signer_response,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
        *verifier_challenge_as_ntt,
    Eurydice_slice t1);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.use_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_arithmetic_use_hint_08(int32_t gamma2,
                                               Eurydice_slice hint,
                                               Eurydice_slice re_vector);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
    uint8_t *verification_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context,
    uint8_t *signature_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
core_result_Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_c4(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, uint8_t *signature_serialized);

/**
 Verify.
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature);

/**
 Verify an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_5c libcrux_iot_ml_dsa_ml_dsa_44_portable_verify(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_iot_ml_dsa_types_MLDSASignature_64 *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_pre_hashed_36(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, Eurydice_slice pre_hash_buffer,
    uint8_t *signature_serialized);

/**
 Verify (pre-hashed with SHAKE-128).
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify_pre_hashed_shake128(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t *signature);

/**
 Verify a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_44_portable_verify_pre_hashed_shake128(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_iot_ml_dsa_types_MLDSASignature_64 *signature);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_ERROR_COEFFICIENT))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNING_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_signing_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,              \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,           \
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_VERIFICATION_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_verification_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A))

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.generate_key_pair with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_c4(
    uint8_t randomness[32U], Eurydice_slice signing_key,
    Eurydice_slice verification_key);

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
    uint8_t randomness[32U], uint8_t *signing_key, uint8_t *verification_key);

/**
 Generate an ML-DSA-65 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_06
libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair(
    uint8_t randomness[32U]);

/**
 Generate an ML-DSA-65 Key Pair
*/
void libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair_mut(
    uint8_t randomness[32U], uint8_t *signing_key, uint8_t *verification_key);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_commitment_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_COMMITMENT_COEFFICIENT))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA                 \
  (libcrux_iot_ml_dsa_constants_beta(                                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
    Eurydice_slice signing_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context, uint8_t randomness[32U],
    uint8_t *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
core_result_Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
core_result_Result_3e libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_c4(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]);

/**
 Sign.
*/
core_result_Result_3e
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]);

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_3e libcrux_iot_ml_dsa_ml_dsa_65_portable_sign(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_22 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]);

/**
 Sign.
*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature);

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_87 libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_pre_hashed_mut with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U],
    uint8_t *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
core_result_Result_3e
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]);

/**
 Sign (pre-hashed).
*/
core_result_Result_3e
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_pre_hashed_shake128(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]);

/**
 Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_3e
libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_pre_hashed_shake128(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_22 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNATURE_SIZE \
  (libcrux_iot_ml_dsa_constants_signature_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,            \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,         \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,     \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
    uint8_t *verification_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context,
    uint8_t *signature_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
core_result_Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_c4(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, uint8_t *signature_serialized);

/**
 Verify.
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature);

/**
 Verify an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_5c libcrux_iot_ml_dsa_ml_dsa_65_portable_verify(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_iot_ml_dsa_types_MLDSASignature_8f *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_36(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, Eurydice_slice pre_hash_buffer,
    uint8_t *signature_serialized);

/**
 Verify (pre-hashed with SHAKE-128).
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify_pre_hashed_shake128(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t *signature);

/**
 Verify a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_65_portable_verify_pre_hashed_shake128(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_iot_ml_dsa_types_MLDSASignature_8f *signature);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_ERROR_COEFFICIENT))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_SIGNING_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_signing_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,              \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,           \
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_VERIFICATION_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_verification_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A))

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.generate_key_pair with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_generate_key_pair_c4(
    uint8_t randomness[32U], Eurydice_slice signing_key,
    Eurydice_slice verification_key);

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_generate_key_pair(
    uint8_t randomness[32U], uint8_t *signing_key, uint8_t *verification_key);

/**
 Generate an ML-DSA-87 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d
libcrux_iot_ml_dsa_ml_dsa_87_portable_generate_key_pair(
    uint8_t randomness[32U]);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_commitment_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_COMMITMENT_COEFFICIENT))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA                 \
  (libcrux_iot_ml_dsa_constants_beta(                                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_GAMMA1_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
    Eurydice_slice signing_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context, uint8_t randomness[32U],
    uint8_t *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
core_result_Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
core_result_Result_f2 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_c4(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]);

/**
 Sign.
*/
core_result_Result_f2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]);

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_f2 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]);

/**
 Sign.
*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature);

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_87 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_mut(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U],
    uint8_t *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_pre_hashed_mut with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_mut_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U],
    uint8_t *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
core_result_Result_f2
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]);

/**
 Sign (pre-hashed).
*/
core_result_Result_f2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_pre_hashed_shake128(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]);

/**
 Generate a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_f2
libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_pre_hashed_shake128(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_SIGNATURE_SIZE \
  (libcrux_iot_ml_dsa_constants_signature_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,            \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,         \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT,     \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
    uint8_t *verification_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context,
    uint8_t *signature_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
core_result_Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_c4(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, uint8_t *signature_serialized);

/**
 Verify.
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature);

/**
 Verify an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_5c libcrux_iot_ml_dsa_ml_dsa_87_portable_verify(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_iot_ml_dsa_types_MLDSASignature_9b *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_pre_hashed_36(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, Eurydice_slice pre_hash_buffer,
    uint8_t *signature_serialized);

/**
 Verify (pre-hashed with SHAKE-128).
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify_pre_hashed_shake128(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t *signature);

/**
 Verify a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_87_portable_verify_pre_hashed_shake128(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_iot_ml_dsa_types_MLDSASignature_9b *signature);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_VECTOR_SIZE    \
  (libcrux_iot_ml_dsa_constants_commitment_vector_size(                       \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_COMMITMENT_COEFFICIENT, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A))

typedef libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44KeyPair;

typedef libcrux_iot_ml_dsa_types_MLDSASignature_64
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44Signature;

typedef libcrux_iot_ml_dsa_types_MLDSASigningKey_b8
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44SigningKey;

typedef libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44VerificationKey;

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ROW_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A +          \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ROW_X_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A *            \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_VECTOR_SIZE    \
  (libcrux_iot_ml_dsa_constants_commitment_vector_size(                       \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_COMMITMENT_COEFFICIENT, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A))

typedef libcrux_iot_ml_dsa_types_MLDSAKeyPair_06
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65KeyPair;

typedef libcrux_iot_ml_dsa_types_MLDSASignature_8f
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65Signature;

typedef libcrux_iot_ml_dsa_types_MLDSASigningKey_22
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65SigningKey;

typedef libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65VerificationKey;

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ROW_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A +          \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ROW_X_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A *            \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_VECTOR_SIZE    \
  (libcrux_iot_ml_dsa_constants_commitment_vector_size(                       \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_COMMITMENT_COEFFICIENT, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A))

typedef libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87KeyPair;

typedef libcrux_iot_ml_dsa_types_MLDSASignature_9b
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87Signature;

typedef libcrux_iot_ml_dsa_types_MLDSASigningKey_a3
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87SigningKey;

typedef libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87VerificationKey;

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ROW_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A +          \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ROW_X_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A *            \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_PRE_HASH_PRE_HASH_OID_LEN ((size_t)11U)

typedef uint8_t libcrux_iot_ml_dsa_pre_hash_PreHashOID[11U];

typedef core_result_Result_80 libcrux_iot_ml_dsa_pre_hash_PreHashResult;

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::SigningError}
*/
libcrux_iot_ml_dsa_types_SigningError libcrux_iot_ml_dsa_pre_hash_from_49(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e);

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::VerificationError}
*/
libcrux_iot_ml_dsa_types_VerificationError libcrux_iot_ml_dsa_pre_hash_from_97(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e);

typedef int32_t libcrux_iot_ml_dsa_simd_traits_FieldElementTimesMontgomeryR;

typedef int32_t libcrux_iot_ml_dsa_simd_portable_vector_type_FieldElement;

#if defined(__cplusplus)
}
#endif

#define libcrux_mldsa65_portable_H_DEFINED
#endif /* libcrux_mldsa65_portable_H */
