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
 * Libcrux: 0c7d13eb4d0117dce1ec2ef42fdb87d10cf78e2b
 */

#ifndef libcrux_iot_mldsa65_portable_H
#define libcrux_iot_mldsa65_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_iot_mldsa_core.h"
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
    const libcrux_iot_ml_dsa_constants_Eta *self);

size_t libcrux_iot_ml_dsa_encoding_error_chunk_size(
    libcrux_iot_ml_dsa_constants_Eta eta);

void libcrux_iot_ml_dsa_encoding_signature_set_hint(
    Eurydice_dst_ref_mut_59 out_hint, size_t i, size_t j);

#define LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT ((size_t)13U)

#define LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW ((size_t)10U)

#define LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT \
  ((size_t)10U)

typedef libcrux_iot_sha3_portable_KeccakState
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256;

libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
    Eurydice_borrow_slice_u8 input);

void libcrux_iot_ml_dsa_hash_functions_portable_shake128(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 out);

typedef struct libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4_s {
  libcrux_iot_sha3_state_KeccakState state0;
  libcrux_iot_sha3_state_KeccakState state1;
  libcrux_iot_sha3_state_KeccakState state2;
  libcrux_iot_sha3_state_KeccakState state3;
} libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4;

libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_x4(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3);

void libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state,
    Eurydice_arr_12 *out0, Eurydice_arr_12 *out1, Eurydice_arr_12 *out2,
    Eurydice_arr_12 *out3);

typedef struct Eurydice_arr_uint8_t___168size_t___x4_s {
  Eurydice_arr_27 fst;
  Eurydice_arr_27 snd;
  Eurydice_arr_27 thd;
  Eurydice_arr_27 f3;
} Eurydice_arr_uint8_t___168size_t___x4;

Eurydice_arr_uint8_t___168size_t___x4
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
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3);

typedef struct Eurydice_arr_uint8_t___136size_t___x4_s {
  Eurydice_arr_3d fst;
  Eurydice_arr_3d snd;
  Eurydice_arr_3d thd;
  Eurydice_arr_3d f3;
} Eurydice_arr_uint8_t___136size_t___x4;

Eurydice_arr_uint8_t___136size_t___x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_first_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state);

Eurydice_arr_uint8_t___136size_t___x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state);

Eurydice_arr_3d
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state);

Eurydice_arr_3d
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state);

typedef libcrux_iot_sha3_portable_KeccakState
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128;

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_b5(
    Eurydice_borrow_slice_u8 input);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_b5(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_12 *out);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_b5(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_27 *out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake128_e2(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_33(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self,
    Eurydice_arr_12 *out0, Eurydice_arr_12 *out1, Eurydice_arr_12 *out2,
    Eurydice_arr_12 *out3);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
Eurydice_arr_uint8_t___168size_t___x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_a1(
    Eurydice_borrow_slice_u8 input);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
Eurydice_arr_3d
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_a1(
    libcrux_iot_sha3_state_KeccakState *self);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
Eurydice_arr_3d
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_a1(
    libcrux_iot_sha3_state_KeccakState *self);

typedef libcrux_iot_sha3_portable_incremental_Shake256Xof
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof;

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 input);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 input);

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
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_x4_29(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
Eurydice_arr_uint8_t___136size_t___x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
Eurydice_arr_uint8_t___136size_t___x4
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

Eurydice_arr_48 libcrux_iot_ml_dsa_sample_add_domain_separator(
    Eurydice_borrow_slice_u8 slice, uint8_t_x2 indices);

Eurydice_arr_a2 libcrux_iot_ml_dsa_sample_add_error_domain_separator(
    Eurydice_borrow_slice_u8 slice, uint16_t domain_separator);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_ERROR_COEFFICIENT))

typedef Eurydice_arr_d4
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients;

Eurydice_arr_d4 libcrux_iot_ml_dsa_simd_portable_vector_type_zero(void);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
Eurydice_arr_d4 libcrux_iot_ml_dsa_simd_portable_zero_c5(void);

void libcrux_iot_ml_dsa_simd_portable_vector_type_from_coefficient_array(
    Eurydice_dst_ref_shared_fc array, Eurydice_arr_d4 *out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_from_coefficient_array_c5(
    Eurydice_dst_ref_shared_fc array, Eurydice_arr_d4 *out);

void libcrux_iot_ml_dsa_simd_portable_vector_type_to_coefficient_array(
    const Eurydice_arr_d4 *value, Eurydice_dst_ref_mut_fc out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_to_coefficient_array_c5(
    const Eurydice_arr_d4 *value, Eurydice_dst_ref_mut_fc out);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_add(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_add_c5(Eurydice_arr_d4 *lhs,
                                             const Eurydice_arr_d4 *rhs);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_subtract_c5(Eurydice_arr_d4 *lhs,
                                                  const Eurydice_arr_d4 *rhs);

bool libcrux_iot_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
    const Eurydice_arr_d4 *simd_unit, int32_t bound);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
bool libcrux_iot_ml_dsa_simd_portable_infinity_norm_exceeds_c5(
    const Eurydice_arr_d4 *simd_unit, int32_t bound);

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS ((int32_t)8380417)

typedef struct int32_t_x2_s {
  int32_t fst;
  int32_t snd;
} int32_t_x2;

int32_t_x2 libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(
    int32_t gamma2, int32_t r);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose(
    int32_t gamma2, const Eurydice_arr_d4 *simd_unit, Eurydice_arr_d4 *low,
    Eurydice_arr_d4 *high);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_decompose_c5(
    int32_t gamma2, const Eurydice_arr_d4 *simd_unit, Eurydice_arr_d4 *low,
    Eurydice_arr_d4 *high);

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_one_hint(
    int32_t low, int32_t high, int32_t gamma2);

size_t libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_hint(
    const Eurydice_arr_d4 *low, const Eurydice_arr_d4 *high, int32_t gamma2,
    Eurydice_arr_d4 *hint);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t libcrux_iot_ml_dsa_simd_portable_compute_hint_c5(
    const Eurydice_arr_d4 *low, const Eurydice_arr_d4 *high, int32_t gamma2,
    Eurydice_arr_d4 *hint);

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_use_one_hint(int32_t gamma2,
                                                                 int32_t r,
                                                                 int32_t hint);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_use_hint(
    int32_t gamma2, const Eurydice_arr_d4 *simd_unit, Eurydice_arr_d4 *hint);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_use_hint_c5(
    int32_t gamma2, const Eurydice_arr_d4 *simd_unit, Eurydice_arr_d4 *hint);

uint64_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint64_t value);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (32U)

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (58728449ULL)

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
    int64_t value);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_montgomery_multiply_c5(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs);

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(int32_t fe);

int32_t_x2 libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round_element(
    int32_t t);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round(
    Eurydice_arr_d4 *t0, Eurydice_arr_d4 *t1);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_power2round_c5(Eurydice_arr_d4 *t0,
                                                     Eurydice_arr_d4 *t1);

size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out);

size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out);

size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_gamma1_serialize_c5(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK \
  ((LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1                     \
    << 1U) -                                                                                                        \
   (int32_t)1)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_BITMASK \
  ((LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1                     \
    << 1U) -                                                                                                        \
   (int32_t)1)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit);

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *out,
    size_t gamma1_exponent);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_gamma1_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *out,
    size_t gamma1_exponent);

void libcrux_iot_ml_dsa_simd_portable_encoding_commitment_serialize(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_commitment_serialize_c5(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA \
  ((int32_t)4)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_4(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA \
  ((int32_t)2)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_2(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_d4 *simd_unit,
    Eurydice_mut_borrow_slice_u8 serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_error_serialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_d4 *simd_unit,
    Eurydice_mut_borrow_slice_u8 serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA \
  ((int32_t)4)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_4(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_units);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA \
  ((int32_t)2)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_2(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit);

void libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_d4 *out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_error_deserialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_d4 *out);

int32_t libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
    int32_t t0);

void libcrux_iot_ml_dsa_simd_portable_encoding_t0_serialize(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_serialize_c5(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 out);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK \
  (((int32_t)1 << (uint32_t)(int32_t)                                                         \
        LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) -                               \
   (int32_t)1)

void libcrux_iot_ml_dsa_simd_portable_encoding_t0_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *out);

void libcrux_iot_ml_dsa_simd_portable_encoding_t1_serialize(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_serialize_c5(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 out);

void libcrux_iot_ml_dsa_simd_portable_encoding_t1_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *out);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
    Eurydice_arr_d4 *simd_unit, int32_t c);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_79_s {
  Eurydice_arr_d4 data[32U];
} Eurydice_arr_79;

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_99(Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_7(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -2608894
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_990(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -518909
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a(Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_6(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 237124
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_991(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -777960
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a8(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -876248
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a0(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 466468
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d9(Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_5(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 1826347
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_992(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 2353451
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -359251
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a80(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= -2091905
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_95(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= 3119733
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a1(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -2884855
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 3111497
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d90(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 2680103
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b(Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_4(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 2725464
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_993(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 1024112
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1c(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -1079900
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b0(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 3585928
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_44(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -549488
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a81(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1119584
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1f(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= 2619752
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_950(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2108549
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b0(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2118186
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a2(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= -3859737
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_e4(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1399561
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de0(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -3277672
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_05(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 1757237
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d91(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -19422
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3a(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 4010497
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b1(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 280005
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a0(Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_3(Eurydice_arr_79 *re);

int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int32_t fe, int32_t fer);

void libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(
    Eurydice_arr_d4 *simd_unit, int32_t zeta);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2(Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(
    Eurydice_arr_d4 *simd_unit, int32_t zeta1, int32_t zeta2);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta_0, int32_t zeta_1);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1(Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
    Eurydice_arr_d4 *simd_unit, int32_t zeta0, int32_t zeta1, int32_t zeta2,
    int32_t zeta3);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta_0, int32_t zeta_1,
    int32_t zeta_2, int32_t zeta_3);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0(Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt(Eurydice_arr_79 *re);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_c5(Eurydice_arr_79 *simd_units);

void libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
    Eurydice_arr_d4 *simd_unit, int32_t zeta0, int32_t zeta1, int32_t zeta2,
    int32_t zeta3);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta0, int32_t zeta1,
    int32_t zeta2, int32_t zeta3);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(
    Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
    Eurydice_arr_d4 *simd_unit, int32_t zeta0, int32_t zeta1);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta_00, int32_t zeta_01);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(
    Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
    Eurydice_arr_d4 *simd_unit, int32_t zeta);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta1);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(
    Eurydice_arr_79 *re);

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
Eurydice_arr_d4 libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
    const Eurydice_arr_d4 *self);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 280005
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_99(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 4010497
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1c(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -19422
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 1757237
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_44(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -3277672
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a8(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1399561
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1f(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= -3859737
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_95(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2118186
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2108549
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= 2619752
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_e4(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1119584
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -549488
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_05(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 3585928
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d9(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -1079900
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3a(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 1024112
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b0(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 2725464
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a0(
    Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 2680103
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_990(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 3111497
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b0(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -2884855
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a80(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= 3119733
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_950(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= -2091905
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a0(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -359251
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de0(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 2353451
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d90(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 1826347
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b1(
    Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 466468
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_991(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -876248
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a81(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -777960
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a1(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 237124
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d91(
    Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -518909
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_992(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -2608894
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a2(
    Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_993(
    Eurydice_arr_79 *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(
    Eurydice_arr_79 *re);

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients, size_t

*/
typedef struct Eurydice_dst_ref_shared_6f_s {
  const Eurydice_arr_d4 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_6f;

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(
    Eurydice_arr_79 *re);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_invert_ntt_montgomery_c5(
    Eurydice_arr_79 *simd_units);

uint8_t_x2 libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
    size_t index, size_t width);

/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients

*/
typedef Eurydice_arr_79 libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $16size_t
*/
typedef struct Eurydice_arr_34_s {
  Eurydice_arr_79 data[16U];
} Eurydice_arr_34;

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
Eurydice_arr_79 libcrux_iot_ml_dsa_polynomial_zero_c2_08(void);

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients, size_t

*/
typedef struct Eurydice_dst_ref_mut_65_s {
  Eurydice_arr_79 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_65;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients, size_t

*/
typedef struct Eurydice_dst_ref_shared_65_s {
  const Eurydice_arr_79 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_65;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_field_modulus with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_13 *out);

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
    Eurydice_dst_ref_shared_fc array, Eurydice_arr_79 *result);

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
    size_t columns, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_65 matrix, Eurydice_arr_12 *rand_stack0,
    Eurydice_arr_12 *rand_stack1, Eurydice_arr_12 *rand_stack2,
    Eurydice_arr_12 *rand_stack3, Eurydice_dst_ref_mut_2c tmp_stack,
    size_t start_index, size_t elements_requested);

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.matrix_flat
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 with const generics

*/
void libcrux_iot_ml_dsa_samplex4_matrix_flat_15(size_t columns,
                                                Eurydice_borrow_slice_u8 seed,
                                                Eurydice_dst_ref_mut_65 matrix);

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
    size_t columns, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_65 matrix);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $8size_t
*/
typedef struct Eurydice_arr_14_s {
  Eurydice_arr_79 data[8U];
} Eurydice_arr_14;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_4 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_13 *out);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_2 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_13 *out);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 randomness,
    size_t *sampled, Eurydice_arr_13 *out);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_four_error_ring_elements with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 seed,
    uint16_t start_index, Eurydice_dst_ref_mut_65 re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.sample_s1_and_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_65 s1_s2);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $4size_t
*/
typedef struct Eurydice_arr_fb_s {
  Eurydice_arr_79 data[4U];
} Eurydice_arr_fb;

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_ntt_08(Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt_multiply_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
    Eurydice_arr_79 *lhs, const Eurydice_arr_79 *rhs);

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
void libcrux_iot_ml_dsa_polynomial_add_c2_08(Eurydice_arr_79 *self,
                                             const Eurydice_arr_79 *rhs);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.invert_ntt_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(Eurydice_arr_79 *re);

/**
 Compute InvertNTT(Â ◦ ŝ₁) + s₂
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_as1_plus_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_dst_ref_shared_65 a_as_ntt,
    Eurydice_dst_ref_shared_65 s1_ntt, Eurydice_dst_ref_shared_65 s1_s2,
    Eurydice_dst_ref_mut_65 result);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.power2round_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
    Eurydice_dst_ref_mut_65 t, Eurydice_dst_ref_mut_65 t1);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t1_serialize_08(
    const Eurydice_arr_79 *re, Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
    Eurydice_borrow_slice_u8 seed, Eurydice_dst_ref_shared_65 t1,
    Eurydice_mut_borrow_slice_u8 verification_key_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 64
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_24(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_06 *out);

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
    Eurydice_borrow_slice_u8 input, Eurydice_arr_06 *out);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_error_serialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_79 *re,
    Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t0_serialize_08(
    const Eurydice_arr_79 *re, Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.signing_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
void libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t error_ring_element_size,
    Eurydice_borrow_slice_u8 seed_matrix, Eurydice_borrow_slice_u8 seed_signing,
    Eurydice_borrow_slice_u8 verification_key, Eurydice_dst_ref_shared_65 s1_2,
    Eurydice_dst_ref_shared_65 t0,
    Eurydice_mut_borrow_slice_u8 signing_key_serialized);

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
    Eurydice_arr_60 randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key);

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_generate_key_pair(
    Eurydice_arr_60 randomness, Eurydice_arr_18 *signing_key,
    Eurydice_arr_40 *verification_key);

/**
 Generate an ML-DSA-44 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2
libcrux_iot_ml_dsa_ml_dsa_44_portable_generate_key_pair(
    Eurydice_arr_60 randomness);

#define None 0
#define Some 1

typedef uint8_t Option_3b_tags;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr uint8_t[[$11size_t]]

*/
typedef struct Option_3b_s {
  Option_3b_tags tag;
  Eurydice_arr_cb f0;
} Option_3b;

typedef struct libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext_s {
  Eurydice_borrow_slice_u8 context;
  Option_3b pre_hash_oid;
} libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext;

#define libcrux_iot_ml_dsa_pre_hash_DomainSeparationError_ContextTooLongError 0

typedef uint8_t libcrux_iot_ml_dsa_pre_hash_DomainSeparationError;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext,
libcrux_iot_ml_dsa_pre_hash_DomainSeparationError

*/
typedef struct Result_80_s {
  Result_a4_tags tag;
  union {
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError case_Err;
  } val;
} Result_80;

/**
 `context` must be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
Result_80 libcrux_iot_ml_dsa_pre_hash_new_c9(Eurydice_borrow_slice_u8 context,
                                             Option_3b pre_hash_oid);

/**
 Returns the pre-hash OID, if any.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
const Option_3b *libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self);

/**
 Returns the context, guaranteed to be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
Eurydice_borrow_slice_u8 libcrux_iot_ml_dsa_pre_hash_context_c9(
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_commitment_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_COMMITMENT_COEFFICIENT))

bool libcrux_iot_ml_dsa_sample_inside_out_shuffle(
    Eurydice_borrow_slice_u8 randomness, size_t *out_index, uint64_t *signs,
    Eurydice_arr_c3 *result);

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
typedef struct Option_e3_s {
  Option_3b_tags tag;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext f0;
} Option_e3;

/**
A monomorphic instance of core.result.Result
with types (), libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_87_s {
  Result_a4_tags tag;
  libcrux_iot_ml_dsa_types_SigningError f0;
} Result_87;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature[[$2420size_t]],
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_ba_s {
  Result_a4_tags tag;
  union {
    Eurydice_arr_400 case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} Result_ba;

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_error_deserialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_79 *result);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.error.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t ring_element_size,
    Eurydice_borrow_slice_u8 serialized, Eurydice_dst_ref_mut_65 ring_elements);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t0_deserialize_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_79 *result);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.t0.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_dst_ref_mut_65 ring_elements);

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
    Eurydice_borrow_slice_u8 verification_key_hash,
    const Option_e3 *domain_separation_context,
    Eurydice_borrow_slice_u8 message, Eurydice_arr_06 *message_representative);

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 576
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_1b(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_5f0 *out);

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
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3,
    Eurydice_arr_5f0 *out0, Eurydice_arr_5f0 *out1, Eurydice_arr_5f0 *out2,
    Eurydice_arr_5f0 *out3);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
    size_t gamma1_exponent, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_79 *result);

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 640
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_c30 *out);

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
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3,
    Eurydice_arr_c30 *out0, Eurydice_arr_c30 *out1, Eurydice_arr_c30 *out2,
    Eurydice_arr_c30 *out3);

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
    Eurydice_borrow_slice_u8 input, Eurydice_arr_5f0 *out);

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
    Eurydice_borrow_slice_u8 input, Eurydice_arr_c30 *out);

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_mask_ring_element_1b(
    const Eurydice_arr_a2 *seed, Eurydice_arr_79 *result,
    size_t gamma1_exponent);

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
    size_t dimension, size_t gamma1_exponent, const Eurydice_arr_06 *seed,
    uint16_t *domain_separator, Eurydice_dst_ref_mut_65 mask);

/**
 Compute InvertNTT(Â ◦ ŷ)
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_matrix_x_mask
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_dst_ref_shared_65 matrix,
    Eurydice_dst_ref_shared_65 mask, Eurydice_dst_ref_mut_65 result);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.decompose_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
    size_t dimension, int32_t gamma2, Eurydice_dst_ref_shared_65 t,
    Eurydice_dst_ref_mut_65 low, Eurydice_dst_ref_mut_65 high);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.commitment.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_commitment_serialize_08(
    const Eurydice_arr_79 *re, Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.commitment.serialize_vector with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
    size_t ring_element_size, Eurydice_dst_ref_shared_65 vector,
    Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_challenge_ring_element with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
    Eurydice_borrow_slice_u8 seed, size_t number_of_ones, Eurydice_arr_79 *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.vector_times_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
    Eurydice_dst_ref_mut_65 vector, const Eurydice_arr_79 *ring_element);

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.add_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_add_vectors_08(size_t dimension,
                                              Eurydice_dst_ref_mut_65 lhs,
                                              Eurydice_dst_ref_shared_65 rhs);

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
void libcrux_iot_ml_dsa_polynomial_subtract_c2_08(Eurydice_arr_79 *self,
                                                  const Eurydice_arr_79 *rhs);

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.subtract_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
    size_t dimension, Eurydice_dst_ref_mut_65 lhs,
    Eurydice_dst_ref_shared_65 rhs);

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
    const Eurydice_arr_79 *self, int32_t bound);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.arithmetic.vector_infinity_norm_exceeds with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
    Eurydice_dst_ref_shared_65 vector, int32_t bound);

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
Eurydice_arr_c3 libcrux_iot_ml_dsa_polynomial_to_i32_array_c2_08(
    const Eurydice_arr_79 *self);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.make_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
size_t libcrux_iot_ml_dsa_arithmetic_make_hint_08(
    Eurydice_dst_ref_shared_65 low, Eurydice_dst_ref_shared_65 high,
    int32_t gamma2, Eurydice_dst_ref_mut_59 hint);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_gamma1_serialize_08(
    const Eurydice_arr_79 *re, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_signature_serialize_08(
    Eurydice_borrow_slice_u8 commitment_hash,
    Eurydice_dst_ref_shared_65 signer_response, Eurydice_dst_ref_shared_59 hint,
    size_t commitment_hash_size, size_t columns_in_a, size_t rows_in_a,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, Eurydice_mut_borrow_slice_u8 signature);

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
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_ba libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

/**
 Sign.
*/
Result_ba
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_ba libcrux_iot_ml_dsa_ml_dsa_44_portable_sign(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

/**
 Sign.
*/
Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_mut(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature);

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_mut(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature);

#define LIBCRUX_IOT_ML_DSA_PRE_HASH_SHAKE128_OID \
  ((KRML_CLITERAL(Eurydice_arr_cb){              \
      .data = {6U, 9U, 96U, 134U, 72U, 1U, 101U, 3U, 4U, 2U, 11U}}))

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
Eurydice_arr_cb libcrux_iot_ml_dsa_pre_hash_oid_0b(void);

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.pre_hash.hash_0b
with types libcrux_iot_ml_dsa_hash_functions_portable_Shake128
with const generics

*/
void libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
    Eurydice_borrow_slice_u8 message, Eurydice_mut_borrow_slice_u8 output);

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
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature);

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
Result_ba libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness);

/**
 Sign (pre-hashed).
*/
Result_ba
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_pre_hashed_shake128(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness);

/**
 Generate a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_ba libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_VERIFICATION_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_verification_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_SIGNATURE_SIZE \
  (libcrux_iot_ml_dsa_constants_signature_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,            \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,         \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT,     \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of core.result.Result
with types (), libcrux_iot_ml_dsa_types_VerificationError

*/
typedef struct Result_5c_s {
  Result_a4_tags tag;
  libcrux_iot_ml_dsa_types_VerificationError f0;
} Result_5c;

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t1_deserialize_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_79 *result);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.deserialize with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
    size_t rows_in_a, size_t verification_key_size,
    Eurydice_borrow_slice_u8 serialized, Eurydice_dst_ref_mut_65 t1);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
Result_5c libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
    size_t columns_in_a, size_t rows_in_a, size_t commitment_hash_size,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, size_t signature_size,
    Eurydice_borrow_slice_u8 serialized,
    Eurydice_mut_borrow_slice_u8 out_commitment_hash,
    Eurydice_dst_ref_mut_65 out_signer_response,
    Eurydice_dst_ref_mut_59 out_hint);

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_ring_element_08(
    Eurydice_borrow_slice_u8 seed, uint8_t_x2 indices, Eurydice_arr_79 *out,
    Eurydice_arr_12 *rand_stack, Eurydice_arr_27 *rand_block,
    Eurydice_arr_13 *tmp_stack);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce with const
generics
- SHIFT_BY= 13
*/
void libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_84(
    Eurydice_arr_d4 *simd_unit);

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
    Eurydice_arr_d4 *simd_unit);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.shift_left_then_reduce
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics
- SHIFT_BY= 13
*/
void libcrux_iot_ml_dsa_arithmetic_shift_left_then_reduce_41(
    Eurydice_arr_79 *re);

/**
 Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_w_approx
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_borrow_slice_u8 seed,
    Eurydice_arr_12 *rand_stack, Eurydice_arr_27 *rand_block,
    Eurydice_arr_13 *tmp_stack, Eurydice_arr_79 *poly_slot,
    Eurydice_dst_ref_shared_65 signer_response,
    const Eurydice_arr_79 *verifier_challenge_as_ntt,
    Eurydice_dst_ref_mut_65 t1);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.use_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_arithmetic_use_hint_08(
    int32_t gamma2, Eurydice_dst_ref_shared_59 hint,
    Eurydice_dst_ref_mut_65 re_vector);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_400 *signature_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_c4(
    const Eurydice_arr_40 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_400 *signature_serialized);

/**
 Verify.
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_400 *signature);

/**
 Verify an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_44_portable_verify(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_400 *signature);

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
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_pre_hashed_36(
    const Eurydice_arr_40 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_400 *signature_serialized);

/**
 Verify (pre-hashed with SHAKE-128).
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify_pre_hashed_shake128(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_400 *signature);

/**
 Verify a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_44_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_400 *signature);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_ERROR_COEFFICIENT))

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $30size_t
*/
typedef struct Eurydice_arr_84_s {
  Eurydice_arr_79 data[30U];
} Eurydice_arr_84;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $11size_t
*/
typedef struct Eurydice_arr_0a_s {
  Eurydice_arr_79 data[11U];
} Eurydice_arr_0a;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $6size_t
*/
typedef struct Eurydice_arr_87_s {
  Eurydice_arr_79 data[6U];
} Eurydice_arr_87;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $5size_t
*/
typedef struct Eurydice_arr_62_s {
  Eurydice_arr_79 data[5U];
} Eurydice_arr_62;

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
    Eurydice_arr_60 randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key);

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
    Eurydice_arr_60 randomness, Eurydice_arr_d10 *signing_key,
    Eurydice_arr_4a *verification_key);

/**
 Generate an ML-DSA-65 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_06
libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair(
    Eurydice_arr_60 randomness);

/**
 Generate an ML-DSA-65 Key Pair
*/
void libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair_mut(
    Eurydice_arr_60 randomness, Eurydice_arr_d10 *signing_key,
    Eurydice_arr_4a *verification_key);

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
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature[[$3309size_t]],
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_3e_s {
  Result_a4_tags tag;
  union {
    Eurydice_arr_96 case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} Result_3e;

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
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_3e libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

/**
 Sign.
*/
Result_3e
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_3e libcrux_iot_ml_dsa_ml_dsa_65_portable_sign(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

/**
 Sign.
*/
Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_mut(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature);

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_mut(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature);

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
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature);

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
Result_3e libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness);

/**
 Sign (pre-hashed).
*/
Result_3e
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_pre_hashed_shake128(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness);

/**
 Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_3e libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_VERIFICATION_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_verification_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A))

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
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_96 *signature_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_c4(
    const Eurydice_arr_4a *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_96 *signature_serialized);

/**
 Verify.
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_96 *signature);

/**
 Verify an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_65_portable_verify(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_96 *signature);

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
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_36(
    const Eurydice_arr_4a *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_96 *signature_serialized);

/**
 Verify (pre-hashed with SHAKE-128).
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify_pre_hashed_shake128(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_96 *signature);

/**
 Verify a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_65_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_96 *signature);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_ERROR_COEFFICIENT))

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $56size_t
*/
typedef struct Eurydice_arr_75_s {
  Eurydice_arr_79 data[56U];
} Eurydice_arr_75;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $15size_t
*/
typedef struct Eurydice_arr_df_s {
  Eurydice_arr_79 data[15U];
} Eurydice_arr_df;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- $7size_t
*/
typedef struct Eurydice_arr_32_s {
  Eurydice_arr_79 data[7U];
} Eurydice_arr_32;

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
    Eurydice_arr_60 randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key);

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_generate_key_pair(
    Eurydice_arr_60 randomness, Eurydice_arr_180 *signing_key,
    Eurydice_arr_510 *verification_key);

/**
 Generate an ML-DSA-87 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d
libcrux_iot_ml_dsa_ml_dsa_87_portable_generate_key_pair(
    Eurydice_arr_60 randomness);

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
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature[[$4627size_t]],
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_f2_s {
  Result_a4_tags tag;
  union {
    Eurydice_arr_38 case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} Result_f2;

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
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_60 randomness,
    Eurydice_arr_38 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_38 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_f2 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

/**
 Sign.
*/
Result_f2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_f2 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

/**
 Sign.
*/
Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_mut(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_38 *signature);

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_mut(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_38 *signature);

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
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness,
    Eurydice_arr_38 *signature);

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
Result_f2 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness);

/**
 Sign (pre-hashed).
*/
Result_f2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_pre_hashed_shake128(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness);

/**
 Generate a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_f2 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_VERIFICATION_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_verification_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A))

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
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
    const Eurydice_arr_510 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_38 *signature_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_c4(
    const Eurydice_arr_510 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_38 *signature_serialized);

/**
 Verify.
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify(
    const Eurydice_arr_510 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_38 *signature);

/**
 Verify an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_87_portable_verify(
    const Eurydice_arr_510 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_38 *signature);

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
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_pre_hashed_36(
    const Eurydice_arr_510 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_38 *signature_serialized);

/**
 Verify (pre-hashed with SHAKE-128).
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify_pre_hashed_shake128(
    const Eurydice_arr_510 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_38 *signature);

/**
 Verify a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_87_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_510 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_38 *signature);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_VECTOR_SIZE    \
  (libcrux_iot_ml_dsa_constants_commitment_vector_size(                       \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_COMMITMENT_COEFFICIENT, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A))

typedef libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44KeyPair;

typedef Eurydice_arr_400
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44Signature;

typedef Eurydice_arr_18
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44SigningKey;

typedef Eurydice_arr_40
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44VerificationKey;

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ROW_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A +          \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ROW_X_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A *            \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_SIGNING_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_signing_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,              \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,           \
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_VECTOR_SIZE    \
  (libcrux_iot_ml_dsa_constants_commitment_vector_size(                       \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_COMMITMENT_COEFFICIENT, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A))

typedef libcrux_iot_ml_dsa_types_MLDSAKeyPair_06
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65KeyPair;

typedef Eurydice_arr_96
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65Signature;

typedef Eurydice_arr_d10
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65SigningKey;

typedef Eurydice_arr_4a
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65VerificationKey;

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ROW_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A +          \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ROW_X_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A *            \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNING_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_signing_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,              \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,           \
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_VECTOR_SIZE    \
  (libcrux_iot_ml_dsa_constants_commitment_vector_size(                       \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_COMMITMENT_COEFFICIENT, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A))

typedef libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87KeyPair;

typedef Eurydice_arr_38
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87Signature;

typedef Eurydice_arr_180
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87SigningKey;

typedef Eurydice_arr_510
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87VerificationKey;

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ROW_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A +          \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ROW_X_COLUMN \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A *            \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_SIGNING_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_signing_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,              \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,           \
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE))

#define LIBCRUX_IOT_ML_DSA_PRE_HASH_PRE_HASH_OID_LEN ((size_t)11U)

typedef Eurydice_arr_cb libcrux_iot_ml_dsa_pre_hash_PreHashOID;

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

typedef Result_80 libcrux_iot_ml_dsa_pre_hash_PreHashResult;

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_mldsa65_portable_H_DEFINED
#endif /* libcrux_iot_mldsa65_portable_H */
