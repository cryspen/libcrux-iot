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

#ifndef libcrux_iot_mldsa65_portable_H
#define libcrux_iot_mldsa65_portable_H

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

static inline int32_t libcrux_iot_ml_dsa_constants_beta(
    size_t ones_in_verifier_challenge, libcrux_iot_ml_dsa_constants_Eta eta) {
  size_t eta_val;
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      eta_val = (size_t)2U;
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      eta_val = (size_t)4U;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return (int32_t)(ones_in_verifier_challenge * eta_val);
}

static inline size_t libcrux_iot_ml_dsa_constants_commitment_ring_element_size(
    size_t bits_per_commitment_coefficient) {
  return bits_per_commitment_coefficient *
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

static inline size_t libcrux_iot_ml_dsa_constants_commitment_vector_size(
    size_t bits_per_commitment_coefficient, size_t rows_in_a) {
  return libcrux_iot_ml_dsa_constants_commitment_ring_element_size(
             bits_per_commitment_coefficient) *
         rows_in_a;
}

static inline size_t libcrux_iot_ml_dsa_constants_error_ring_element_size(
    size_t bits_per_error_coefficient) {
  return bits_per_error_coefficient *
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

static inline size_t libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(
    size_t bits_per_gamma1_coefficient) {
  return bits_per_gamma1_coefficient *
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

static inline size_t libcrux_iot_ml_dsa_constants_signature_size(
    size_t rows_in_a, size_t columns_in_a, size_t max_ones_in_hint,
    size_t commitment_hash_size, size_t bits_per_gamma1_coefficient) {
  return commitment_hash_size +
         columns_in_a * libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(
                            bits_per_gamma1_coefficient) +
         max_ones_in_hint + rows_in_a;
}

static inline size_t libcrux_iot_ml_dsa_constants_signing_key_size(
    size_t rows_in_a, size_t columns_in_a, size_t error_ring_element_size) {
  return LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
         LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE +
         LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH +
         (rows_in_a + columns_in_a) * error_ring_element_size +
         rows_in_a * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
}

static inline size_t libcrux_iot_ml_dsa_constants_verification_key_size(
    size_t rows_in_a) {
  return LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * rows_in_a *
             (LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH -
              LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) /
             (size_t)8U;
}

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
static inline libcrux_iot_ml_dsa_constants_Eta
libcrux_iot_ml_dsa_constants_clone_44(
    const libcrux_iot_ml_dsa_constants_Eta *self) {
  return self[0U];
}

static KRML_MUSTINLINE size_t libcrux_iot_ml_dsa_encoding_error_chunk_size(
    libcrux_iot_ml_dsa_constants_Eta eta) {
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      return (size_t)4U;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return (size_t)3U;
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_signature_set_hint(
    Eurydice_dst_ref_mut_22 out_hint, size_t i, size_t j) {
  out_hint.ptr[i].data[j] = (int32_t)1;
}

#define LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT ((size_t)13U)

#define LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW ((size_t)10U)

#define LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT \
  ((size_t)10U)

typedef libcrux_iot_sha3_portable_KeccakState
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128;

typedef struct libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4_s {
  libcrux_iot_sha3_state_KeccakState state0;
  libcrux_iot_sha3_state_KeccakState state1;
  libcrux_iot_sha3_state_KeccakState state2;
  libcrux_iot_sha3_state_KeccakState state3;
} libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4;

typedef libcrux_iot_sha3_portable_KeccakState
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256;

typedef struct libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4_s {
  libcrux_iot_sha3_state_KeccakState state0;
  libcrux_iot_sha3_state_KeccakState state1;
  libcrux_iot_sha3_state_KeccakState state2;
  libcrux_iot_sha3_state_KeccakState state3;
} libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4;

typedef libcrux_iot_sha3_portable_incremental_Shake256Xof
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof;

static KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_sha3_portable_incremental_shake256_init();
  libcrux_iot_sha3_portable_incremental_shake256_absorb_final(&state, input);
  return state;
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake128(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_portable_shake128(out, input);
}

static KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_x4(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3) {
  libcrux_iot_sha3_state_KeccakState state0 =
      libcrux_iot_sha3_portable_incremental_shake128_init();
  libcrux_iot_sha3_portable_incremental_shake128_absorb_final(&state0, input0);
  libcrux_iot_sha3_state_KeccakState state1 =
      libcrux_iot_sha3_portable_incremental_shake128_init();
  libcrux_iot_sha3_portable_incremental_shake128_absorb_final(&state1, input1);
  libcrux_iot_sha3_state_KeccakState state2 =
      libcrux_iot_sha3_portable_incremental_shake128_init();
  libcrux_iot_sha3_portable_incremental_shake128_absorb_final(&state2, input2);
  libcrux_iot_sha3_state_KeccakState state3 =
      libcrux_iot_sha3_portable_incremental_shake128_init();
  libcrux_iot_sha3_portable_incremental_shake128_absorb_final(&state3, input3);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4){
      .state0 = state0, .state1 = state1, .state2 = state2, .state3 = state3});
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state,
    Eurydice_arr_12 *out0, Eurydice_arr_12 *out1, Eurydice_arr_12 *out2,
    Eurydice_arr_12 *out3) {
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state0, Eurydice_array_to_slice_mut_a8(out0));
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state1, Eurydice_array_to_slice_mut_a8(out1));
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state2, Eurydice_array_to_slice_mut_a8(out2));
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state3, Eurydice_array_to_slice_mut_a8(out3));
}

typedef struct Eurydice_arr_27_x4_s {
  Eurydice_arr_27 fst;
  Eurydice_arr_27 snd;
  Eurydice_arr_27 thd;
  Eurydice_arr_27 f3;
} Eurydice_arr_27_x4;

static KRML_MUSTINLINE Eurydice_arr_27_x4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state) {
  Eurydice_arr_27 out0 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state0, Eurydice_array_to_slice_mut_7b(&out0));
  Eurydice_arr_27 out1 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state1, Eurydice_array_to_slice_mut_7b(&out1));
  Eurydice_arr_27 out2 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state2, Eurydice_array_to_slice_mut_7b(&out2));
  Eurydice_arr_27 out3 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state3, Eurydice_array_to_slice_mut_7b(&out3));
  return (KRML_CLITERAL(Eurydice_arr_27_x4){
      .fst = out0, .snd = out1, .thd = out2, .f3 = out3});
}

static KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_init_absorb_x4(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3) {
  libcrux_iot_sha3_state_KeccakState state0 =
      libcrux_iot_sha3_portable_incremental_shake256_init();
  libcrux_iot_sha3_portable_incremental_shake256_absorb_final(&state0, input0);
  libcrux_iot_sha3_state_KeccakState state1 =
      libcrux_iot_sha3_portable_incremental_shake256_init();
  libcrux_iot_sha3_portable_incremental_shake256_absorb_final(&state1, input1);
  libcrux_iot_sha3_state_KeccakState state2 =
      libcrux_iot_sha3_portable_incremental_shake256_init();
  libcrux_iot_sha3_portable_incremental_shake256_absorb_final(&state2, input2);
  libcrux_iot_sha3_state_KeccakState state3 =
      libcrux_iot_sha3_portable_incremental_shake256_init();
  libcrux_iot_sha3_portable_incremental_shake256_absorb_final(&state3, input3);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4){
      .state0 = state0, .state1 = state1, .state2 = state2, .state3 = state3});
}

typedef struct Eurydice_arr_3d_x4_s {
  Eurydice_arr_3d fst;
  Eurydice_arr_3d snd;
  Eurydice_arr_3d thd;
  Eurydice_arr_3d f3;
} Eurydice_arr_3d_x4;

static KRML_MUSTINLINE Eurydice_arr_3d_x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_first_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state) {
  Eurydice_arr_3d out0 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state0, Eurydice_array_to_slice_mut_d4(&out0));
  Eurydice_arr_3d out1 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state1, Eurydice_array_to_slice_mut_d4(&out1));
  Eurydice_arr_3d out2 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state2, Eurydice_array_to_slice_mut_d4(&out2));
  Eurydice_arr_3d out3 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state3, Eurydice_array_to_slice_mut_d4(&out3));
  return (KRML_CLITERAL(Eurydice_arr_3d_x4){
      .fst = out0, .snd = out1, .thd = out2, .f3 = out3});
}

static KRML_MUSTINLINE Eurydice_arr_3d_x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state) {
  Eurydice_arr_3d out0 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state0, Eurydice_array_to_slice_mut_d4(&out0));
  Eurydice_arr_3d out1 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state1, Eurydice_array_to_slice_mut_d4(&out1));
  Eurydice_arr_3d out2 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state2, Eurydice_array_to_slice_mut_d4(&out2));
  Eurydice_arr_3d out3 = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state3, Eurydice_array_to_slice_mut_d4(&out3));
  return (KRML_CLITERAL(Eurydice_arr_3d_x4){
      .fst = out0, .snd = out1, .thd = out2, .f3 = out3});
}

static KRML_MUSTINLINE Eurydice_arr_3d
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state) {
  Eurydice_arr_3d out = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      state, Eurydice_array_to_slice_mut_d4(&out));
  return out;
}

static KRML_MUSTINLINE Eurydice_arr_3d
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state) {
  Eurydice_arr_3d out = {.data = {0U}};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      state, Eurydice_array_to_slice_mut_d4(&out));
  return out;
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
static KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_b5(
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_sha3_portable_incremental_shake128_init();
  libcrux_iot_sha3_portable_incremental_shake128_absorb_final(&state, input);
  return state;
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_b5(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_12 *out) {
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      self, Eurydice_array_to_slice_mut_a8(out));
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_b5(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_27 *out) {
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      self, Eurydice_array_to_slice_mut_7b(out));
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_e2(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake128(input, out);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
static KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_33(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_x4(
      input0, input1, input2, input3);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self,
    Eurydice_arr_12 *out0, Eurydice_arr_12 *out1, Eurydice_arr_12 *out2,
    Eurydice_arr_12 *out3) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_x4(
      self, out0, out1, out2, out3);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
static KRML_MUSTINLINE Eurydice_arr_27_x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_x4(
      self);
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
static KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_a1(
    Eurydice_borrow_slice_u8 input) {
  return libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
      input);
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
static KRML_MUSTINLINE Eurydice_arr_3d
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_a1(
    libcrux_iot_sha3_state_KeccakState *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(
      self);
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
static KRML_MUSTINLINE Eurydice_arr_3d
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_a1(
    libcrux_iot_sha3_state_KeccakState *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(
      self);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
static inline void libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_portable_incremental_absorb_a5(self, input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
static inline void libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_portable_incremental_absorb_final_a5(self, input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
static inline libcrux_iot_sha3_keccak_KeccakXofState_c7
libcrux_iot_ml_dsa_hash_functions_portable_init_88(void) {
  return libcrux_iot_sha3_portable_incremental_new_a5();
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
static inline void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_portable_incremental_squeeze_a5(self, out);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
static KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_x4_29(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake256_init_absorb_x4(
      input0, input1, input2, input3);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
static KRML_MUSTINLINE Eurydice_arr_3d_x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_first_block_x4(
      self);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
static KRML_MUSTINLINE Eurydice_arr_3d_x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_next_block_x4(
      self);
}

#define LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE128_BLOCK_SIZE ((size_t)168U)

#define LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE128_FIVE_BLOCKS_SIZE \
  (LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE128_BLOCK_SIZE * (size_t)5U)

#define LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE256_BLOCK_SIZE ((size_t)136U)

typedef struct uint8_t_x2_s {
  uint8_t fst;
  uint8_t snd;
} uint8_t_x2;

static KRML_MUSTINLINE uint16_t
libcrux_iot_ml_dsa_sample_generate_domain_separator(uint8_t_x2 _) {
  uint8_t row = _.fst;
  uint8_t column = _.snd;
  return (uint32_t)(uint16_t)column | (uint32_t)(uint16_t)row << 8U;
}

static KRML_MUSTINLINE Eurydice_arr_48
libcrux_iot_ml_dsa_sample_add_domain_separator(Eurydice_borrow_slice_u8 slice,
                                               uint8_t_x2 indices) {
  Eurydice_arr_48 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_361(
                          &out, (KRML_CLITERAL(core_ops_range_Range_08){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  uint16_t domain_separator =
      libcrux_iot_ml_dsa_sample_generate_domain_separator(indices);
  out.data[32U] = (uint8_t)domain_separator;
  out.data[33U] = (uint8_t)((uint32_t)domain_separator >> 8U);
  return out;
}

static KRML_MUSTINLINE Eurydice_arr_a2
libcrux_iot_ml_dsa_sample_add_error_domain_separator(
    Eurydice_borrow_slice_u8 slice, uint16_t domain_separator) {
  Eurydice_arr_a2 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_362(
                          &out, (KRML_CLITERAL(core_ops_range_Range_08){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  out.data[64U] = (uint8_t)domain_separator;
  out.data[65U] = (uint8_t)((uint32_t)domain_separator >> 8U);
  return out;
}

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_ERROR_COEFFICIENT))

typedef Eurydice_arr_d4
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients;

static inline Eurydice_arr_d4 libcrux_iot_ml_dsa_simd_portable_vector_type_zero(
    void) {
  return (KRML_CLITERAL(Eurydice_arr_d4){.data = {0U}});
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline Eurydice_arr_d4 libcrux_iot_ml_dsa_simd_portable_zero_c5(void) {
  return libcrux_iot_ml_dsa_simd_portable_vector_type_zero();
}

static inline void
libcrux_iot_ml_dsa_simd_portable_vector_type_from_coefficient_array(
    Eurydice_dst_ref_shared_fc array, Eurydice_arr_d4 *out) {
  Eurydice_slice_copy(
      Eurydice_array_to_slice_mut_a7(out),
      Eurydice_slice_subslice_shared_46(
          array,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT})),
      int32_t);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_from_coefficient_array_c5(
    Eurydice_dst_ref_shared_fc array, Eurydice_arr_d4 *out) {
  libcrux_iot_ml_dsa_simd_portable_vector_type_from_coefficient_array(array,
                                                                      out);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_vector_type_to_coefficient_array(
    const Eurydice_arr_d4 *value, Eurydice_dst_ref_mut_fc out) {
  Eurydice_slice_copy(out, Eurydice_array_to_slice_shared_a7(value), int32_t);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_to_coefficient_array_c5(
    const Eurydice_arr_d4 *value, Eurydice_dst_ref_mut_fc out) {
  libcrux_iot_ml_dsa_simd_portable_vector_type_to_coefficient_array(value, out);
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_add(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->data[uu____0] = lhs->data[uu____0] + rhs->data[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_add_c5(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_add(lhs, rhs);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->data[uu____0] = lhs->data[uu____0] - rhs->data[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_subtract_c5(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(lhs, rhs);
}

static KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
    const Eurydice_arr_d4 *simd_unit, int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    int32_t coefficient = simd_unit->data[i0];
    int32_t sign = coefficient >> 31U;
    int32_t normalized = coefficient - (sign & (int32_t)2 * coefficient);
    bool uu____0;
    if (result) {
      uu____0 = true;
    } else {
      uu____0 = normalized >= bound;
    }
    result = uu____0;
  }
  return result;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline bool libcrux_iot_ml_dsa_simd_portable_infinity_norm_exceeds_c5(
    const Eurydice_arr_d4 *simd_unit, int32_t bound) {
  return libcrux_iot_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
      simd_unit, bound);
}

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS ((int32_t)8380417)

typedef struct int32_t_x2_s {
  int32_t fst;
  int32_t snd;
} int32_t_x2;

static KRML_MUSTINLINE int32_t_x2
libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(int32_t gamma2,
                                                              int32_t r) {
  int32_t r0 = r + (r >> 31U & LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  int32_t ceil_of_r_by_128 = (r0 + (int32_t)127) >> 7U;
  int32_t r1;
  switch (gamma2) {
    case 95232: {
      int32_t result =
          (ceil_of_r_by_128 * (int32_t)11275 + ((int32_t)1 << 23U)) >> 24U;
      r1 = (result ^ ((int32_t)43 - result) >> 31U) & result;
      break;
    }
    case 261888: {
      int32_t result =
          (ceil_of_r_by_128 * (int32_t)1025 + ((int32_t)1 << 21U)) >> 22U;
      r1 = result & (int32_t)15;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  int32_t alpha = gamma2 * (int32_t)2;
  int32_t r00 = r0 - r1 * alpha;
  r00 = r00 - (((LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS - (int32_t)1) /
                    (int32_t)2 -
                r00) >>
                   31U &
               LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  return (KRML_CLITERAL(int32_t_x2){.fst = r00, .snd = r1});
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose(
    int32_t gamma2, const Eurydice_arr_d4 *simd_unit, Eurydice_arr_d4 *low,
    Eurydice_arr_d4 *high) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    int32_t_x2 uu____0 =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(
            gamma2, simd_unit->data[i0]);
    int32_t uu____1 = uu____0.snd;
    low->data[i0] = uu____0.fst;
    high->data[i0] = uu____1;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_decompose_c5(
    int32_t gamma2, const Eurydice_arr_d4 *simd_unit, Eurydice_arr_d4 *low,
    Eurydice_arr_d4 *high) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose(gamma2, simd_unit, low,
                                                        high);
}

static KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_one_hint(int32_t low,
                                                             int32_t high,
                                                             int32_t gamma2) {
  int32_t uu____0;
  if (low > gamma2) {
    uu____0 = (int32_t)1;
  } else if (low < -gamma2) {
    uu____0 = (int32_t)1;
  } else if (low == -gamma2) {
    if (high != (int32_t)0) {
      uu____0 = (int32_t)1;
    } else {
      uu____0 = (int32_t)0;
    }
  } else {
    uu____0 = (int32_t)0;
  }
  return uu____0;
}

static KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_hint(
    const Eurydice_arr_d4 *low, const Eurydice_arr_d4 *high, int32_t gamma2,
    Eurydice_arr_d4 *hint) {
  size_t one_hints_count = (size_t)0U;
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    hint->data[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_one_hint(
            low->data[i0], high->data[i0], gamma2);
    one_hints_count = one_hints_count + (size_t)hint->data[i0];
  }
  return one_hints_count;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline size_t libcrux_iot_ml_dsa_simd_portable_compute_hint_c5(
    const Eurydice_arr_d4 *low, const Eurydice_arr_d4 *high, int32_t gamma2,
    Eurydice_arr_d4 *hint) {
  return libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_hint(low, high,
                                                                  gamma2, hint);
}

static KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_use_one_hint(int32_t gamma2,
                                                         int32_t r,
                                                         int32_t hint) {
  int32_t_x2 uu____0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(gamma2, r);
  int32_t r0 = uu____0.fst;
  int32_t r1 = uu____0.snd;
  int32_t uu____1;
  if (!(hint == (int32_t)0)) {
    switch (gamma2) {
      case 95232: {
        if (r0 > (int32_t)0) {
          if (r1 == (int32_t)43) {
            uu____1 = (int32_t)0;
          } else {
            uu____1 = r1 + hint;
          }
        } else if (r1 == (int32_t)0) {
          uu____1 = (int32_t)43;
        } else {
          uu____1 = r1 - hint;
        }
        break;
      }
      case 261888: {
        if (r0 > (int32_t)0) {
          uu____1 = (r1 + hint) & (int32_t)15;
        } else {
          uu____1 = (r1 - hint) & (int32_t)15;
        }
        break;
      }
      default: {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                          "panic!");
        KRML_HOST_EXIT(255U);
      }
    }
    return uu____1;
  }
  return r1;
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_use_hint(
    int32_t gamma2, const Eurydice_arr_d4 *simd_unit, Eurydice_arr_d4 *hint) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    int32_t uu____0 = libcrux_iot_ml_dsa_simd_portable_arithmetic_use_one_hint(
        gamma2, simd_unit->data[i0], hint->data[i0]);
    hint->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_use_hint_c5(
    int32_t gamma2, const Eurydice_arr_d4 *simd_unit, Eurydice_arr_d4 *hint) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_use_hint(gamma2, simd_unit, hint);
}

static KRML_MUSTINLINE uint64_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint64_t value) {
  return value & ((1ULL << (uint32_t)n) - 1ULL);
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (32U)

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (58728449ULL)

static KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
    int64_t value) {
  uint64_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT,
          (uint64_t)value) *
      LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
  int32_t k = (int32_t)
      libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT, t);
  int64_t k_times_modulus =
      (int64_t)k * (int64_t)LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS;
  int32_t c =
      (int32_t)(k_times_modulus >>
                (uint32_t)
                    LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int32_t value_high =
      (int32_t)(value >>
                (uint32_t)
                    LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  return value_high - c;
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    lhs->data[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
            (int64_t)lhs->data[i0] * (int64_t)rhs->data[i0]);
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_montgomery_multiply_c5(
    Eurydice_arr_d4 *lhs, const Eurydice_arr_d4 *rhs) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply(lhs, rhs);
}

static KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(int32_t fe) {
  int32_t quotient = (fe + ((int32_t)1 << 22U)) >> 23U;
  return fe - quotient * LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS;
}

static KRML_MUSTINLINE int32_t_x2
libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round_element(int32_t t) {
  int32_t t2 = t + (t >> 31U & LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  int32_t t1 =
      (t2 - (int32_t)1 +
       ((int32_t)1
        << (uint32_t)(LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T -
                      (size_t)1U))) >>
      (uint32_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T;
  int32_t t0 =
      t2 -
      (t1 << (uint32_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T);
  return (KRML_CLITERAL(int32_t_x2){.fst = t0, .snd = t1});
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round(Eurydice_arr_d4 *t0,
                                                        Eurydice_arr_d4 *t1) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    int32_t_x2 uu____0 =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round_element(
            t0->data[i0]);
    int32_t uu____1 = uu____0.snd;
    t0->data[i0] = uu____0.fst;
    t1->data[i0] = uu____1;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_power2round_c5(
    Eurydice_arr_d4 *t0, Eurydice_arr_d4 *t1) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round(t0, t1);
}

static KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < randomness.meta / (size_t)3U; i++) {
    size_t _cloop_i = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        randomness, (KRML_CLITERAL(core_ops_range_Range_08){
                        .start = _cloop_i * (size_t)3U,
                        .end = _cloop_i * (size_t)3U + (size_t)3U}));
    int32_t b0 = (int32_t)bytes.ptr[0U];
    int32_t b1 = (int32_t)bytes.ptr[1U];
    int32_t b2 = (int32_t)bytes.ptr[2U];
    int32_t coefficient = ((b2 << 16U | b1 << 8U) | b0) & (int32_t)8388607;
    if (coefficient < LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS) {
      out.ptr[sampled] = coefficient;
      sampled++;
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out) {
  return libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
      randomness, out);
}

static KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < randomness.meta; i++) {
    size_t _cloop_j = i;
    const uint8_t *byte = &randomness.ptr[_cloop_j];
    uint8_t try_0 =
        core_ops_bit__core__ops__bit__BitAnd_u8__u8__for__0__u8___bitand(byte,
                                                                         15U);
    uint8_t try_1 = core_ops_bit__core__ops__bit__Shr_i32__u8__for__0__u8___shr(
        byte, (int32_t)4);
    if (try_0 < 15U) {
      int32_t try_00 = (int32_t)try_0;
      int32_t try_0_mod_5 = try_00 - (try_00 * (int32_t)26 >> 7U) * (int32_t)5;
      out.ptr[sampled] = (int32_t)2 - try_0_mod_5;
      sampled++;
    }
    if (try_1 < 15U) {
      int32_t try_10 = (int32_t)try_1;
      int32_t try_1_mod_5 = try_10 - (try_10 * (int32_t)26 >> 7U) * (int32_t)5;
      out.ptr[sampled] = (int32_t)2 - try_1_mod_5;
      sampled++;
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out) {
  return libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
      randomness, out);
}

static KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < randomness.meta; i++) {
    size_t _cloop_j = i;
    const uint8_t *byte = &randomness.ptr[_cloop_j];
    uint8_t try_0 =
        core_ops_bit__core__ops__bit__BitAnd_u8__u8__for__0__u8___bitand(byte,
                                                                         15U);
    uint8_t try_1 = core_ops_bit__core__ops__bit__Shr_i32__u8__for__0__u8___shr(
        byte, (int32_t)4);
    if (try_0 < 9U) {
      out.ptr[sampled] = (int32_t)4 - (int32_t)try_0;
      sampled++;
    }
    if (try_1 < 9U) {
      out.ptr[sampled] = (int32_t)4 - (int32_t)try_1;
      sampled++;
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_fc out) {
  return libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
      randomness, out);
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_fc coefficients =
        Eurydice_array_to_subslice_shared_7f(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = i0 * (size_t)4U,
                           .end = i0 * (size_t)4U + (size_t)4U}));
    int32_t coefficient0 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficients.ptr[0U];
    int32_t coefficient1 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficients.ptr[1U];
    int32_t coefficient2 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficients.ptr[2U];
    int32_t coefficient3 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficients.ptr[3U];
    serialized.ptr[(size_t)9U * i0] = (uint8_t)coefficient0;
    serialized.ptr[(size_t)9U * i0 + (size_t)1U] =
        (uint8_t)(coefficient0 >> 8U);
    serialized.ptr[(size_t)9U * i0 + (size_t)2U] =
        (uint8_t)(coefficient0 >> 16U);
    size_t uu____0 = (size_t)9U * i0 + (size_t)2U;
    serialized.ptr[uu____0] = (uint32_t)serialized.ptr[uu____0] |
                              (uint32_t)(uint8_t)(coefficient1 << 2U);
    serialized.ptr[(size_t)9U * i0 + (size_t)3U] =
        (uint8_t)(coefficient1 >> 6U);
    serialized.ptr[(size_t)9U * i0 + (size_t)4U] =
        (uint8_t)(coefficient1 >> 14U);
    size_t uu____1 = (size_t)9U * i0 + (size_t)4U;
    serialized.ptr[uu____1] = (uint32_t)serialized.ptr[uu____1] |
                              (uint32_t)(uint8_t)(coefficient2 << 4U);
    serialized.ptr[(size_t)9U * i0 + (size_t)5U] =
        (uint8_t)(coefficient2 >> 4U);
    serialized.ptr[(size_t)9U * i0 + (size_t)6U] =
        (uint8_t)(coefficient2 >> 12U);
    size_t uu____2 = (size_t)9U * i0 + (size_t)6U;
    serialized.ptr[uu____2] = (uint32_t)serialized.ptr[uu____2] |
                              (uint32_t)(uint8_t)(coefficient3 << 6U);
    serialized.ptr[(size_t)9U * i0 + (size_t)7U] =
        (uint8_t)(coefficient3 >> 2U);
    serialized.ptr[(size_t)9U * i0 + (size_t)8U] =
        (uint8_t)(coefficient3 >> 10U);
  }
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)2U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_fc coefficients =
        Eurydice_array_to_subslice_shared_7f(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = i0 * (size_t)2U,
                           .end = i0 * (size_t)2U + (size_t)2U}));
    int32_t coefficient0 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        coefficients.ptr[0U];
    int32_t coefficient1 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        coefficients.ptr[1U];
    serialized.ptr[(size_t)5U * i0] = (uint8_t)coefficient0;
    serialized.ptr[(size_t)5U * i0 + (size_t)1U] =
        (uint8_t)(coefficient0 >> 8U);
    serialized.ptr[(size_t)5U * i0 + (size_t)2U] =
        (uint8_t)(coefficient0 >> 16U);
    size_t uu____0 = (size_t)5U * i0 + (size_t)2U;
    serialized.ptr[uu____0] = (uint32_t)serialized.ptr[uu____0] |
                              (uint32_t)(uint8_t)(coefficient1 << 4U);
    serialized.ptr[(size_t)5U * i0 + (size_t)3U] =
        (uint8_t)(coefficient1 >> 4U);
    serialized.ptr[(size_t)5U * i0 + (size_t)4U] =
        (uint8_t)(coefficient1 >> 12U);
  }
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent) {
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
          simd_unit, serialized);
      break;
    }
    case 19U: {
      libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
          simd_unit, serialized);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_gamma1_serialize_c5(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent) {
  libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize(
      simd_unit, serialized, gamma1_exponent);
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK \
  ((LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1                     \
    << 1U) -                                                                                                        \
   (int32_t)1)

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)9U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)9U, .end = i0 * (size_t)9U + (size_t)9U}));
    int32_t coefficient0 = (int32_t)bytes.ptr[0U];
    coefficient0 = coefficient0 | (int32_t)bytes.ptr[1U] << 8U;
    coefficient0 = coefficient0 | (int32_t)bytes.ptr[2U] << 16U;
    coefficient0 =
        coefficient0 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient1 = (int32_t)bytes.ptr[2U] >> 2U;
    coefficient1 = coefficient1 | (int32_t)bytes.ptr[3U] << 6U;
    coefficient1 = coefficient1 | (int32_t)bytes.ptr[4U] << 14U;
    coefficient1 =
        coefficient1 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient2 = (int32_t)bytes.ptr[4U] >> 4U;
    coefficient2 = coefficient2 | (int32_t)bytes.ptr[5U] << 4U;
    coefficient2 = coefficient2 | (int32_t)bytes.ptr[6U] << 12U;
    coefficient2 =
        coefficient2 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient3 = (int32_t)bytes.ptr[6U] >> 6U;
    coefficient3 = coefficient3 | (int32_t)bytes.ptr[7U] << 2U;
    coefficient3 = coefficient3 | (int32_t)bytes.ptr[8U] << 10U;
    coefficient3 =
        coefficient3 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    simd_unit->data[(size_t)4U * i0] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficient0;
    simd_unit->data[(size_t)4U * i0 + (size_t)1U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficient1;
    simd_unit->data[(size_t)4U * i0 + (size_t)2U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficient2;
    simd_unit->data[(size_t)4U * i0 + (size_t)3U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficient3;
  }
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_BITMASK \
  ((LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1                     \
    << 1U) -                                                                                                        \
   (int32_t)1)

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)5U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)5U, .end = i0 * (size_t)5U + (size_t)5U}));
    int32_t coefficient0 = (int32_t)bytes.ptr[0U];
    coefficient0 = coefficient0 | (int32_t)bytes.ptr[1U] << 8U;
    coefficient0 = coefficient0 | (int32_t)bytes.ptr[2U] << 16U;
    coefficient0 =
        coefficient0 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient1 = (int32_t)bytes.ptr[2U] >> 4U;
    coefficient1 = coefficient1 | (int32_t)bytes.ptr[3U] << 4U;
    coefficient1 = coefficient1 | (int32_t)bytes.ptr[4U] << 12U;
    simd_unit->data[(size_t)2U * i0] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        coefficient0;
    simd_unit->data[(size_t)2U * i0 + (size_t)1U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        coefficient1;
  }
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *out,
    size_t gamma1_exponent) {
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
          serialized, out);
      break;
    }
    case 19U: {
      libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
          serialized, out);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_gamma1_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *out,
    size_t gamma1_exponent) {
  libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize(serialized, out,
                                                               gamma1_exponent);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_commitment_serialize(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  switch ((uint8_t)serialized.meta) {
    case 4U: {
      break;
    }
    case 6U: {
      for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)4U; i++) {
        size_t i0 = i;
        Eurydice_dst_ref_shared_fc coefficients =
            Eurydice_array_to_subslice_shared_7f(
                simd_unit, (KRML_CLITERAL(core_ops_range_Range_08){
                               .start = i0 * (size_t)4U,
                               .end = i0 * (size_t)4U + (size_t)4U}));
        uint8_t coefficient0 = (uint8_t)coefficients.ptr[0U];
        uint8_t coefficient1 = (uint8_t)coefficients.ptr[1U];
        uint8_t coefficient2 = (uint8_t)coefficients.ptr[2U];
        uint8_t coefficient3 = (uint8_t)coefficients.ptr[3U];
        serialized.ptr[(size_t)3U * i0] =
            (uint32_t)coefficient1 << 6U | (uint32_t)coefficient0;
        serialized.ptr[(size_t)3U * i0 + (size_t)1U] =
            (uint32_t)coefficient2 << 4U | (uint32_t)coefficient1 >> 2U;
        serialized.ptr[(size_t)3U * i0 + (size_t)2U] =
            (uint32_t)coefficient3 << 2U | (uint32_t)coefficient2 >> 4U;
      }
      return;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)2U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_fc coefficients =
        Eurydice_array_to_subslice_shared_7f(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = i0 * (size_t)2U,
                           .end = i0 * (size_t)2U + (size_t)2U}));
    uint8_t coefficient0 = (uint8_t)coefficients.ptr[0U];
    uint8_t coefficient1 = (uint8_t)coefficients.ptr[1U];
    serialized.ptr[i0] = (uint32_t)coefficient1 << 4U | (uint32_t)coefficient0;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_commitment_serialize_c5(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  libcrux_iot_ml_dsa_simd_portable_encoding_commitment_serialize(simd_unit,
                                                                 serialized);
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA \
  ((int32_t)4)

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_4(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)2U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_fc coefficients =
        Eurydice_array_to_subslice_shared_7f(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = i0 * (size_t)2U,
                           .end = i0 * (size_t)2U + (size_t)2U}));
    uint8_t coefficient0 =
        (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA -
                  coefficients.ptr[0U]);
    uint8_t coefficient1 =
        (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA -
                  coefficients.ptr[1U]);
    serialized.ptr[i0] = (uint32_t)coefficient1 << 4U | (uint32_t)coefficient0;
  }
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA \
  ((int32_t)2)

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_2(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  uint8_t coefficient0 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->data[0U]);
  uint8_t coefficient1 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->data[1U]);
  uint8_t coefficient2 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->data[2U]);
  uint8_t coefficient3 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->data[3U]);
  uint8_t coefficient4 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->data[4U]);
  uint8_t coefficient5 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->data[5U]);
  uint8_t coefficient6 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->data[6U]);
  uint8_t coefficient7 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->data[7U]);
  serialized.ptr[0U] =
      ((uint32_t)coefficient2 << 6U | (uint32_t)coefficient1 << 3U) |
      (uint32_t)coefficient0;
  serialized.ptr[1U] =
      (((uint32_t)coefficient5 << 7U | (uint32_t)coefficient4 << 4U) |
       (uint32_t)coefficient3 << 1U) |
      (uint32_t)coefficient2 >> 2U;
  serialized.ptr[2U] =
      ((uint32_t)coefficient7 << 5U | (uint32_t)coefficient6 << 2U) |
      (uint32_t)coefficient5 >> 1U;
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_d4 *simd_unit,
    Eurydice_mut_borrow_slice_u8 serialized) {
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_4(
          simd_unit, serialized);
      return;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_2(
      simd_unit, serialized);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_error_serialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_d4 *simd_unit,
    Eurydice_mut_borrow_slice_u8 serialized) {
  libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize(eta, simd_unit,
                                                            serialized);
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA \
  ((int32_t)4)

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_4(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_units) {
  for (size_t i = (size_t)0U; i < serialized.meta; i++) {
    size_t i0 = i;
    const uint8_t *byte = &serialized.ptr[i0];
    uint8_t uu____0 =
        core_ops_bit__core__ops__bit__BitAnd_u8__u8__for__0__u8___bitand(byte,
                                                                         15U);
    simd_units->data[(size_t)2U * i0] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA -
        (int32_t)uu____0;
    uint8_t uu____1 =
        core_ops_bit__core__ops__bit__Shr_i32__u8__for__0__u8___shr(byte,
                                                                    (int32_t)4);
    simd_units->data[(size_t)2U * i0 + (size_t)1U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA -
        (int32_t)uu____1;
  }
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA \
  ((int32_t)2)

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_2(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit) {
  int32_t byte0 = (int32_t)serialized.ptr[0U];
  int32_t byte1 = (int32_t)serialized.ptr[1U];
  int32_t byte2 = (int32_t)serialized.ptr[2U];
  simd_unit->data[0U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte0 & (int32_t)7);
  simd_unit->data[1U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte0 >> 3U & (int32_t)7);
  simd_unit->data[2U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      ((byte0 >> 6U | byte1 << 2U) & (int32_t)7);
  simd_unit->data[3U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte1 >> 1U & (int32_t)7);
  simd_unit->data[4U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte1 >> 4U & (int32_t)7);
  simd_unit->data[5U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      ((byte1 >> 7U | byte2 << 1U) & (int32_t)7);
  simd_unit->data[6U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte2 >> 2U & (int32_t)7);
  simd_unit->data[7U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte2 >> 5U & (int32_t)7);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_d4 *out) {
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_4(
          serialized, out);
      return;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_2(
      serialized, out);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_error_deserialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_d4 *out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize(eta, serialized,
                                                              out);
}

static KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(int32_t t0) {
  return ((int32_t)1
          << (uint32_t)(LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T -
                        (size_t)1U)) -
         t0;
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_t0_serialize(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  int32_t coefficient0 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[0U]);
  int32_t coefficient1 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[1U]);
  int32_t coefficient2 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[2U]);
  int32_t coefficient3 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[3U]);
  int32_t coefficient4 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[4U]);
  int32_t coefficient5 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[5U]);
  int32_t coefficient6 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[6U]);
  int32_t coefficient7 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[7U]);
  serialized.ptr[0U] = (uint8_t)coefficient0;
  serialized.ptr[1U] = (uint8_t)(coefficient0 >> 8U);
  size_t uu____0 = (size_t)1U;
  serialized.ptr[uu____0] = (uint32_t)serialized.ptr[uu____0] |
                            (uint32_t)(uint8_t)(coefficient1 << 5U);
  serialized.ptr[2U] = (uint8_t)(coefficient1 >> 3U);
  serialized.ptr[3U] = (uint8_t)(coefficient1 >> 11U);
  size_t uu____1 = (size_t)3U;
  serialized.ptr[uu____1] = (uint32_t)serialized.ptr[uu____1] |
                            (uint32_t)(uint8_t)(coefficient2 << 2U);
  serialized.ptr[4U] = (uint8_t)(coefficient2 >> 6U);
  size_t uu____2 = (size_t)4U;
  serialized.ptr[uu____2] = (uint32_t)serialized.ptr[uu____2] |
                            (uint32_t)(uint8_t)(coefficient3 << 7U);
  serialized.ptr[5U] = (uint8_t)(coefficient3 >> 1U);
  serialized.ptr[6U] = (uint8_t)(coefficient3 >> 9U);
  size_t uu____3 = (size_t)6U;
  serialized.ptr[uu____3] = (uint32_t)serialized.ptr[uu____3] |
                            (uint32_t)(uint8_t)(coefficient4 << 4U);
  serialized.ptr[7U] = (uint8_t)(coefficient4 >> 4U);
  serialized.ptr[8U] = (uint8_t)(coefficient4 >> 12U);
  size_t uu____4 = (size_t)8U;
  serialized.ptr[uu____4] = (uint32_t)serialized.ptr[uu____4] |
                            (uint32_t)(uint8_t)(coefficient5 << 1U);
  serialized.ptr[9U] = (uint8_t)(coefficient5 >> 7U);
  size_t uu____5 = (size_t)9U;
  serialized.ptr[uu____5] = (uint32_t)serialized.ptr[uu____5] |
                            (uint32_t)(uint8_t)(coefficient6 << 6U);
  serialized.ptr[10U] = (uint8_t)(coefficient6 >> 2U);
  serialized.ptr[11U] = (uint8_t)(coefficient6 >> 10U);
  size_t uu____6 = (size_t)11U;
  serialized.ptr[uu____6] = (uint32_t)serialized.ptr[uu____6] |
                            (uint32_t)(uint8_t)(coefficient7 << 3U);
  serialized.ptr[12U] = (uint8_t)(coefficient7 >> 5U);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_t0_serialize_c5(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t0_serialize(simd_unit, out);
}

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK \
  (((int32_t)1 << (uint32_t)(int32_t)                                                         \
        LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) -                               \
   (int32_t)1)

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_t0_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit) {
  int32_t byte0 = (int32_t)serialized.ptr[0U];
  int32_t byte1 = (int32_t)serialized.ptr[1U];
  int32_t byte2 = (int32_t)serialized.ptr[2U];
  int32_t byte3 = (int32_t)serialized.ptr[3U];
  int32_t byte4 = (int32_t)serialized.ptr[4U];
  int32_t byte5 = (int32_t)serialized.ptr[5U];
  int32_t byte6 = (int32_t)serialized.ptr[6U];
  int32_t byte7 = (int32_t)serialized.ptr[7U];
  int32_t byte8 = (int32_t)serialized.ptr[8U];
  int32_t byte9 = (int32_t)serialized.ptr[9U];
  int32_t byte10 = (int32_t)serialized.ptr[10U];
  int32_t byte11 = (int32_t)serialized.ptr[11U];
  int32_t byte12 = (int32_t)serialized.ptr[12U];
  int32_t coefficient0 = byte0;
  coefficient0 = coefficient0 | byte1 << 8U;
  coefficient0 =
      coefficient0 &
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient1 = byte1 >> 5U;
  coefficient1 = coefficient1 | byte2 << 3U;
  coefficient1 = coefficient1 | byte3 << 11U;
  coefficient1 =
      coefficient1 &
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient2 = byte3 >> 2U;
  coefficient2 = coefficient2 | byte4 << 6U;
  coefficient2 =
      coefficient2 &
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient3 = byte4 >> 7U;
  coefficient3 = coefficient3 | byte5 << 1U;
  coefficient3 = coefficient3 | byte6 << 9U;
  coefficient3 =
      coefficient3 &
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient4 = byte6 >> 4U;
  coefficient4 = coefficient4 | byte7 << 4U;
  coefficient4 = coefficient4 | byte8 << 12U;
  coefficient4 =
      coefficient4 &
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient5 = byte8 >> 1U;
  coefficient5 = coefficient5 | byte9 << 7U;
  coefficient5 =
      coefficient5 &
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient6 = byte9 >> 6U;
  coefficient6 = coefficient6 | byte10 << 2U;
  coefficient6 = coefficient6 | byte11 << 10U;
  coefficient6 =
      coefficient6 &
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient7 = byte11 >> 3U;
  coefficient7 = coefficient7 | byte12 << 5U;
  coefficient7 =
      coefficient7 &
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  simd_unit->data[0U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient0);
  simd_unit->data[1U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient1);
  simd_unit->data[2U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient2);
  simd_unit->data[3U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient3);
  simd_unit->data[4U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient4);
  simd_unit->data[5U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient5);
  simd_unit->data[6U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient6);
  simd_unit->data[7U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient7);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_t0_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t0_deserialize(serialized, out);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_t1_serialize(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_fc coefficients =
        Eurydice_array_to_subslice_shared_7f(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = i0 * (size_t)4U,
                           .end = i0 * (size_t)4U + (size_t)4U}));
    serialized.ptr[(size_t)5U * i0] =
        (uint8_t)(coefficients.ptr[0U] & (int32_t)255);
    serialized.ptr[(size_t)5U * i0 + (size_t)1U] =
        (uint32_t)(uint8_t)(coefficients.ptr[1U] & (int32_t)63) << 2U |
        (uint32_t)(uint8_t)(coefficients.ptr[0U] >> 8U & (int32_t)3);
    serialized.ptr[(size_t)5U * i0 + (size_t)2U] =
        (uint32_t)(uint8_t)(coefficients.ptr[2U] & (int32_t)15) << 4U |
        (uint32_t)(uint8_t)(coefficients.ptr[1U] >> 6U & (int32_t)15);
    serialized.ptr[(size_t)5U * i0 + (size_t)3U] =
        (uint32_t)(uint8_t)(coefficients.ptr[3U] & (int32_t)3) << 6U |
        (uint32_t)(uint8_t)(coefficients.ptr[2U] >> 4U & (int32_t)63);
    serialized.ptr[(size_t)5U * i0 + (size_t)4U] =
        (uint8_t)(coefficients.ptr[3U] >> 2U & (int32_t)255);
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_t1_serialize_c5(
    const Eurydice_arr_d4 *simd_unit, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t1_serialize(simd_unit, out);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_t1_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *simd_unit) {
  int32_t mask = ((int32_t)1 << (uint32_t)
                      LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T) -
                 (int32_t)1;
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)5U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)5U, .end = i0 * (size_t)5U + (size_t)5U}));
    int32_t byte0 = (int32_t)bytes.ptr[0U];
    int32_t byte1 = (int32_t)bytes.ptr[1U];
    int32_t byte2 = (int32_t)bytes.ptr[2U];
    int32_t byte3 = (int32_t)bytes.ptr[3U];
    int32_t byte4 = (int32_t)bytes.ptr[4U];
    simd_unit->data[(size_t)4U * i0] = (byte0 | byte1 << 8U) & mask;
    simd_unit->data[(size_t)4U * i0 + (size_t)1U] =
        (byte1 >> 2U | byte2 << 6U) & mask;
    simd_unit->data[(size_t)4U * i0 + (size_t)2U] =
        (byte2 >> 4U | byte3 << 4U) & mask;
    simd_unit->data[(size_t)4U * i0 + (size_t)3U] =
        (byte3 >> 6U | byte4 << 2U) & mask;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_t1_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_d4 *out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t1_deserialize(serialized, out);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
    Eurydice_arr_d4 *simd_unit, int32_t c) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    simd_unit->data[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
            (int64_t)simd_unit->data[i0] * (int64_t)c);
  }
}

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
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_99(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)16U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)16U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)25847);
    re->data[j + (size_t)16U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)16U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_7(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_99(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -2608894
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_990(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)8U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)8U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2608894);
    re->data[j + (size_t)8U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)8U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -518909
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)8U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)8U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-518909);
    re->data[j + (size_t)8U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)8U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_6(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_990(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 237124
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_991(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)237124);
    re->data[j + (size_t)4U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)4U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -777960
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a8(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-777960);
    re->data[j + (size_t)4U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)4U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -876248
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-876248);
    re->data[j + (size_t)4U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)4U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 466468
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d9(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)466468);
    re->data[j + (size_t)4U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)4U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_5(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_991(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a8(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a0(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d9(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 1826347
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_992(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)1826347);
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 2353451
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)2353451);
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -359251
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a80(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-359251);
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= -2091905
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_95(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2091905);
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= 3119733
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a1(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)3119733);
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -2884855
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2884855);
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 3111497
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d90(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)3111497);
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 2680103
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)2680103);
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_4(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_992(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a80(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_95(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a1(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d90(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 2725464
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_993(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)2725464);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 1024112
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1c(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)2U; i < (size_t)2U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)1024112);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -1079900
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-1079900);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 3585928
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_44(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)6U; i < (size_t)6U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)3585928);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -549488
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a81(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-549488);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1119584
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1f(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)10U; i < (size_t)10U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-1119584);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= 2619752
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_950(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)2619752);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2108549
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)14U; i < (size_t)14U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2108549);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2118186
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a2(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2118186);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= -3859737
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_e4(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)18U; i < (size_t)18U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-3859737);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1399561
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-1399561);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -3277672
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_05(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)22U; i < (size_t)22U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-3277672);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 1757237
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d91(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)1757237);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -19422
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3a(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)26U; i < (size_t)26U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-19422);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 4010497
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b1(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)4010497);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 280005
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)30U; i < (size_t)30U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)280005);
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_3(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_993(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1c(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b0(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_44(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a81(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1f(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_950(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b0(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a2(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_e4(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de0(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_05(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d91(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3a(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b1(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a0(re);
}

static KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int32_t fe, int32_t fer) {
  return libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
      (int64_t)fe * (int64_t)fer);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(
    Eurydice_arr_d4 *simd_unit, int32_t zeta) {
  int32_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[4U], zeta);
  simd_unit->data[4U] = simd_unit->data[0U] - t;
  simd_unit->data[0U] = simd_unit->data[0U] + t;
  int32_t t0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[5U], zeta);
  simd_unit->data[5U] = simd_unit->data[1U] - t0;
  simd_unit->data[1U] = simd_unit->data[1U] + t0;
  int32_t t1 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[6U], zeta);
  simd_unit->data[6U] = simd_unit->data[2U] - t1;
  simd_unit->data[2U] = simd_unit->data[2U] + t1;
  int32_t t2 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[7U], zeta);
  simd_unit->data[7U] = simd_unit->data[3U] - t2;
  simd_unit->data[3U] = simd_unit->data[3U] + t2;
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(Eurydice_arr_79 *re,
                                                          size_t index,
                                                          int32_t zeta) {
  libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(
      &re->data[index], zeta);
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)0U,
                                                            (int32_t)2706023);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)1U,
                                                            (int32_t)95776);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)2U,
                                                            (int32_t)3077325);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)3U,
                                                            (int32_t)3530437);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)4U,
                                                            (int32_t)-1661693);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)5U,
                                                            (int32_t)-3592148);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)6U,
                                                            (int32_t)-2537516);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)7U,
                                                            (int32_t)3915439);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)8U,
                                                            (int32_t)-3861115);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)9U,
                                                            (int32_t)-3043716);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)10U,
                                                            (int32_t)3574422);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)11U,
                                                            (int32_t)-2867647);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)12U,
                                                            (int32_t)3539968);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)13U,
                                                            (int32_t)-300467);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)14U,
                                                            (int32_t)2348700);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)15U,
                                                            (int32_t)-539299);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)16U,
                                                            (int32_t)-1699267);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)17U,
                                                            (int32_t)-1643818);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)18U,
                                                            (int32_t)3505694);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)19U,
                                                            (int32_t)-3821735);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)20U,
                                                            (int32_t)3507263);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)21U,
                                                            (int32_t)-2140649);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)22U,
                                                            (int32_t)-1600420);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)23U,
                                                            (int32_t)3699596);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)24U,
                                                            (int32_t)811944);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)25U,
                                                            (int32_t)531354);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)26U,
                                                            (int32_t)954230);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)27U,
                                                            (int32_t)3881043);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)28U,
                                                            (int32_t)3900724);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)29U,
                                                            (int32_t)-2556880);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)30U,
                                                            (int32_t)2071892);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)31U,
                                                            (int32_t)-2797779);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(
    Eurydice_arr_d4 *simd_unit, int32_t zeta1, int32_t zeta2) {
  int32_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[2U], zeta1);
  simd_unit->data[2U] = simd_unit->data[0U] - t;
  simd_unit->data[0U] = simd_unit->data[0U] + t;
  int32_t t0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[3U], zeta1);
  simd_unit->data[3U] = simd_unit->data[1U] - t0;
  simd_unit->data[1U] = simd_unit->data[1U] + t0;
  int32_t t1 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[6U], zeta2);
  simd_unit->data[6U] = simd_unit->data[4U] - t1;
  simd_unit->data[4U] = simd_unit->data[4U] + t1;
  int32_t t2 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[7U], zeta2);
  simd_unit->data[7U] = simd_unit->data[5U] - t2;
  simd_unit->data[5U] = simd_unit->data[5U] + t2;
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(Eurydice_arr_79 *re,
                                                          size_t index,
                                                          int32_t zeta_0,
                                                          int32_t zeta_1) {
  libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(
      &re->data[index], zeta_0, zeta_1);
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)0U, (int32_t)-3930395, (int32_t)-1528703);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)1U, (int32_t)-3677745, (int32_t)-3041255);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)2U, (int32_t)-1452451, (int32_t)3475950);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)3U, (int32_t)2176455, (int32_t)-1585221);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)4U, (int32_t)-1257611, (int32_t)1939314);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)5U, (int32_t)-4083598, (int32_t)-1000202);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)6U, (int32_t)-3190144, (int32_t)-3157330);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)7U, (int32_t)-3632928, (int32_t)126922);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)8U, (int32_t)3412210, (int32_t)-983419);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)9U, (int32_t)2147896, (int32_t)2715295);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)10U, (int32_t)-2967645, (int32_t)-3693493);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)11U, (int32_t)-411027, (int32_t)-2477047);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)12U, (int32_t)-671102, (int32_t)-1228525);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)13U, (int32_t)-22981, (int32_t)-1308169);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)14U, (int32_t)-381987, (int32_t)1349076);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)15U, (int32_t)1852771, (int32_t)-1430430);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)16U, (int32_t)-3343383, (int32_t)264944);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)17U, (int32_t)508951, (int32_t)3097992);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)18U, (int32_t)44288, (int32_t)-1100098);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)19U, (int32_t)904516, (int32_t)3958618);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)20U, (int32_t)-3724342, (int32_t)-8578);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)21U, (int32_t)1653064, (int32_t)-3249728);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)22U, (int32_t)2389356, (int32_t)-210977);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)23U, (int32_t)759969, (int32_t)-1316856);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)24U, (int32_t)189548, (int32_t)-3553272);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)25U, (int32_t)3159746, (int32_t)-1851402);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)26U, (int32_t)-2409325, (int32_t)-177440);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)27U, (int32_t)1315589, (int32_t)1341330);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)28U, (int32_t)1285669, (int32_t)-1584928);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)29U, (int32_t)-812732, (int32_t)-1439742);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)30U, (int32_t)-3019102, (int32_t)-3881060);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)31U, (int32_t)-3628969, (int32_t)3839961);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
    Eurydice_arr_d4 *simd_unit, int32_t zeta0, int32_t zeta1, int32_t zeta2,
    int32_t zeta3) {
  int32_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[1U], zeta0);
  simd_unit->data[1U] = simd_unit->data[0U] - t;
  simd_unit->data[0U] = simd_unit->data[0U] + t;
  int32_t t0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[3U], zeta1);
  simd_unit->data[3U] = simd_unit->data[2U] - t0;
  simd_unit->data[2U] = simd_unit->data[2U] + t0;
  int32_t t1 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[5U], zeta2);
  simd_unit->data[5U] = simd_unit->data[4U] - t1;
  simd_unit->data[4U] = simd_unit->data[4U] + t1;
  int32_t t2 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[7U], zeta3);
  simd_unit->data[7U] = simd_unit->data[6U] - t2;
  simd_unit->data[6U] = simd_unit->data[6U] + t2;
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta_0, int32_t zeta_1,
    int32_t zeta_2, int32_t zeta_3) {
  libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
      &re->data[index], zeta_0, zeta_1, zeta_2, zeta_3);
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)0U, (int32_t)2091667, (int32_t)3407706, (int32_t)2316500,
      (int32_t)3817976);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)1U, (int32_t)-3342478, (int32_t)2244091, (int32_t)-2446433,
      (int32_t)-3562462);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)2U, (int32_t)266997, (int32_t)2434439, (int32_t)-1235728,
      (int32_t)3513181);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)3U, (int32_t)-3520352, (int32_t)-3759364, (int32_t)-1197226,
      (int32_t)-3193378);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)4U, (int32_t)900702, (int32_t)1859098, (int32_t)909542,
      (int32_t)819034);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)5U, (int32_t)495491, (int32_t)-1613174, (int32_t)-43260,
      (int32_t)-522500);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)6U, (int32_t)-655327, (int32_t)-3122442, (int32_t)2031748,
      (int32_t)3207046);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)7U, (int32_t)-3556995, (int32_t)-525098, (int32_t)-768622,
      (int32_t)-3595838);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)8U, (int32_t)342297, (int32_t)286988, (int32_t)-2437823,
      (int32_t)4108315);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)9U, (int32_t)3437287, (int32_t)-3342277, (int32_t)1735879,
      (int32_t)203044);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)10U, (int32_t)2842341, (int32_t)2691481, (int32_t)-2590150,
      (int32_t)1265009);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)11U, (int32_t)4055324, (int32_t)1247620, (int32_t)2486353,
      (int32_t)1595974);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)12U, (int32_t)-3767016, (int32_t)1250494, (int32_t)2635921,
      (int32_t)-3548272);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)13U, (int32_t)-2994039, (int32_t)1869119, (int32_t)1903435,
      (int32_t)-1050970);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)14U, (int32_t)-1333058, (int32_t)1237275, (int32_t)-3318210,
      (int32_t)-1430225);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)15U, (int32_t)-451100, (int32_t)1312455, (int32_t)3306115,
      (int32_t)-1962642);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)16U, (int32_t)-1279661, (int32_t)1917081, (int32_t)-2546312,
      (int32_t)-1374803);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)17U, (int32_t)1500165, (int32_t)777191, (int32_t)2235880,
      (int32_t)3406031);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)18U, (int32_t)-542412, (int32_t)-2831860, (int32_t)-1671176,
      (int32_t)-1846953);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)19U, (int32_t)-2584293, (int32_t)-3724270, (int32_t)594136,
      (int32_t)-3776993);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)20U, (int32_t)-2013608, (int32_t)2432395, (int32_t)2454455,
      (int32_t)-164721);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)21U, (int32_t)1957272, (int32_t)3369112, (int32_t)185531,
      (int32_t)-1207385);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)22U, (int32_t)-3183426, (int32_t)162844, (int32_t)1616392,
      (int32_t)3014001);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)23U, (int32_t)810149, (int32_t)1652634, (int32_t)-3694233,
      (int32_t)-1799107);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)24U, (int32_t)-3038916, (int32_t)3523897, (int32_t)3866901,
      (int32_t)269760);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)25U, (int32_t)2213111, (int32_t)-975884, (int32_t)1717735,
      (int32_t)472078);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)26U, (int32_t)-426683, (int32_t)1723600, (int32_t)-1803090,
      (int32_t)1910376);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)27U, (int32_t)-1667432, (int32_t)-1104333, (int32_t)-260646,
      (int32_t)-3833893);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)28U, (int32_t)-2939036, (int32_t)-2235985, (int32_t)-420899,
      (int32_t)-2286327);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)29U, (int32_t)183443, (int32_t)-976891, (int32_t)1612842,
      (int32_t)-3545687);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)30U, (int32_t)-554416, (int32_t)3919660, (int32_t)-48306,
      (int32_t)-1362209);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)31U, (int32_t)3937738, (int32_t)1400424, (int32_t)-846154,
      (int32_t)1976782);
}

static KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_7(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_6(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_5(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_4(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_3(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0(re);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_ntt_c5(
    Eurydice_arr_79 *simd_units) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt(simd_units);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
    Eurydice_arr_d4 *simd_unit, int32_t zeta0, int32_t zeta1, int32_t zeta2,
    int32_t zeta3) {
  int32_t a_minus_b = simd_unit->data[1U] - simd_unit->data[0U];
  simd_unit->data[0U] = simd_unit->data[0U] + simd_unit->data[1U];
  simd_unit->data[1U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta0);
  int32_t a_minus_b0 = simd_unit->data[3U] - simd_unit->data[2U];
  simd_unit->data[2U] = simd_unit->data[2U] + simd_unit->data[3U];
  simd_unit->data[3U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, zeta1);
  int32_t a_minus_b1 = simd_unit->data[5U] - simd_unit->data[4U];
  simd_unit->data[4U] = simd_unit->data[4U] + simd_unit->data[5U];
  simd_unit->data[5U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, zeta2);
  int32_t a_minus_b2 = simd_unit->data[7U] - simd_unit->data[6U];
  simd_unit->data[6U] = simd_unit->data[6U] + simd_unit->data[7U];
  simd_unit->data[7U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, zeta3);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta0, int32_t zeta1,
    int32_t zeta2, int32_t zeta3) {
  libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
      &re->data[index], zeta0, zeta1, zeta2, zeta3);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)0U, (int32_t)1976782, (int32_t)-846154, (int32_t)1400424,
      (int32_t)3937738);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)1U, (int32_t)-1362209, (int32_t)-48306, (int32_t)3919660,
      (int32_t)-554416);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)2U, (int32_t)-3545687, (int32_t)1612842, (int32_t)-976891,
      (int32_t)183443);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)3U, (int32_t)-2286327, (int32_t)-420899, (int32_t)-2235985,
      (int32_t)-2939036);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)4U, (int32_t)-3833893, (int32_t)-260646, (int32_t)-1104333,
      (int32_t)-1667432);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)5U, (int32_t)1910376, (int32_t)-1803090, (int32_t)1723600,
      (int32_t)-426683);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)6U, (int32_t)472078, (int32_t)1717735, (int32_t)-975884,
      (int32_t)2213111);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)7U, (int32_t)269760, (int32_t)3866901, (int32_t)3523897,
      (int32_t)-3038916);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)8U, (int32_t)-1799107, (int32_t)-3694233, (int32_t)1652634,
      (int32_t)810149);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)9U, (int32_t)3014001, (int32_t)1616392, (int32_t)162844,
      (int32_t)-3183426);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)10U, (int32_t)-1207385, (int32_t)185531, (int32_t)3369112,
      (int32_t)1957272);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)11U, (int32_t)-164721, (int32_t)2454455, (int32_t)2432395,
      (int32_t)-2013608);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)12U, (int32_t)-3776993, (int32_t)594136, (int32_t)-3724270,
      (int32_t)-2584293);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)13U, (int32_t)-1846953, (int32_t)-1671176, (int32_t)-2831860,
      (int32_t)-542412);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)14U, (int32_t)3406031, (int32_t)2235880, (int32_t)777191,
      (int32_t)1500165);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)15U, (int32_t)-1374803, (int32_t)-2546312, (int32_t)1917081,
      (int32_t)-1279661);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)16U, (int32_t)-1962642, (int32_t)3306115, (int32_t)1312455,
      (int32_t)-451100);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)17U, (int32_t)-1430225, (int32_t)-3318210, (int32_t)1237275,
      (int32_t)-1333058);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)18U, (int32_t)-1050970, (int32_t)1903435, (int32_t)1869119,
      (int32_t)-2994039);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)19U, (int32_t)-3548272, (int32_t)2635921, (int32_t)1250494,
      (int32_t)-3767016);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)20U, (int32_t)1595974, (int32_t)2486353, (int32_t)1247620,
      (int32_t)4055324);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)21U, (int32_t)1265009, (int32_t)-2590150, (int32_t)2691481,
      (int32_t)2842341);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)22U, (int32_t)203044, (int32_t)1735879, (int32_t)-3342277,
      (int32_t)3437287);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)23U, (int32_t)4108315, (int32_t)-2437823, (int32_t)286988,
      (int32_t)342297);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)24U, (int32_t)-3595838, (int32_t)-768622, (int32_t)-525098,
      (int32_t)-3556995);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)25U, (int32_t)3207046, (int32_t)2031748, (int32_t)-3122442,
      (int32_t)-655327);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)26U, (int32_t)-522500, (int32_t)-43260, (int32_t)-1613174,
      (int32_t)495491);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)27U, (int32_t)819034, (int32_t)909542, (int32_t)1859098,
      (int32_t)900702);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)28U, (int32_t)-3193378, (int32_t)-1197226, (int32_t)-3759364,
      (int32_t)-3520352);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)29U, (int32_t)3513181, (int32_t)-1235728, (int32_t)2434439,
      (int32_t)266997);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)30U, (int32_t)-3562462, (int32_t)-2446433, (int32_t)2244091,
      (int32_t)-3342478);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)31U, (int32_t)3817976, (int32_t)2316500, (int32_t)3407706,
      (int32_t)2091667);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
    Eurydice_arr_d4 *simd_unit, int32_t zeta0, int32_t zeta1) {
  int32_t a_minus_b = simd_unit->data[2U] - simd_unit->data[0U];
  simd_unit->data[0U] = simd_unit->data[0U] + simd_unit->data[2U];
  simd_unit->data[2U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta0);
  int32_t a_minus_b0 = simd_unit->data[3U] - simd_unit->data[1U];
  simd_unit->data[1U] = simd_unit->data[1U] + simd_unit->data[3U];
  simd_unit->data[3U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, zeta0);
  int32_t a_minus_b1 = simd_unit->data[6U] - simd_unit->data[4U];
  simd_unit->data[4U] = simd_unit->data[4U] + simd_unit->data[6U];
  simd_unit->data[6U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, zeta1);
  int32_t a_minus_b2 = simd_unit->data[7U] - simd_unit->data[5U];
  simd_unit->data[5U] = simd_unit->data[5U] + simd_unit->data[7U];
  simd_unit->data[7U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, zeta1);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta_00, int32_t zeta_01) {
  libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
      &re->data[index], zeta_00, zeta_01);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)0U, (int32_t)3839961, (int32_t)-3628969);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)1U, (int32_t)-3881060, (int32_t)-3019102);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)2U, (int32_t)-1439742, (int32_t)-812732);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)3U, (int32_t)-1584928, (int32_t)1285669);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)4U, (int32_t)1341330, (int32_t)1315589);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)5U, (int32_t)-177440, (int32_t)-2409325);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)6U, (int32_t)-1851402, (int32_t)3159746);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)7U, (int32_t)-3553272, (int32_t)189548);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)8U, (int32_t)-1316856, (int32_t)759969);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)9U, (int32_t)-210977, (int32_t)2389356);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)10U, (int32_t)-3249728, (int32_t)1653064);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)11U, (int32_t)-8578, (int32_t)-3724342);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)12U, (int32_t)3958618, (int32_t)904516);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)13U, (int32_t)-1100098, (int32_t)44288);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)14U, (int32_t)3097992, (int32_t)508951);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)15U, (int32_t)264944, (int32_t)-3343383);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)16U, (int32_t)-1430430, (int32_t)1852771);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)17U, (int32_t)1349076, (int32_t)-381987);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)18U, (int32_t)-1308169, (int32_t)-22981);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)19U, (int32_t)-1228525, (int32_t)-671102);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)20U, (int32_t)-2477047, (int32_t)-411027);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)21U, (int32_t)-3693493, (int32_t)-2967645);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)22U, (int32_t)2715295, (int32_t)2147896);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)23U, (int32_t)-983419, (int32_t)3412210);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)24U, (int32_t)126922, (int32_t)-3632928);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)25U, (int32_t)-3157330, (int32_t)-3190144);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)26U, (int32_t)-1000202, (int32_t)-4083598);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)27U, (int32_t)1939314, (int32_t)-1257611);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)28U, (int32_t)-1585221, (int32_t)2176455);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)29U, (int32_t)3475950, (int32_t)-1452451);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)30U, (int32_t)-3041255, (int32_t)-3677745);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)31U, (int32_t)-1528703, (int32_t)-3930395);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
    Eurydice_arr_d4 *simd_unit, int32_t zeta) {
  int32_t a_minus_b = simd_unit->data[4U] - simd_unit->data[0U];
  simd_unit->data[0U] = simd_unit->data[0U] + simd_unit->data[4U];
  simd_unit->data[4U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta);
  int32_t a_minus_b0 = simd_unit->data[5U] - simd_unit->data[1U];
  simd_unit->data[1U] = simd_unit->data[1U] + simd_unit->data[5U];
  simd_unit->data[5U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, zeta);
  int32_t a_minus_b1 = simd_unit->data[6U] - simd_unit->data[2U];
  simd_unit->data[2U] = simd_unit->data[2U] + simd_unit->data[6U];
  simd_unit->data[6U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, zeta);
  int32_t a_minus_b2 = simd_unit->data[7U] - simd_unit->data[3U];
  simd_unit->data[3U] = simd_unit->data[3U] + simd_unit->data[7U];
  simd_unit->data[7U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, zeta);
}

static inline void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
    Eurydice_arr_79 *re, size_t index, int32_t zeta1) {
  libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
      &re->data[index], zeta1);
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)0U, (int32_t)-2797779);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)1U, (int32_t)2071892);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)2U, (int32_t)-2556880);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)3U, (int32_t)3900724);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)4U, (int32_t)3881043);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)5U, (int32_t)954230);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)6U, (int32_t)531354);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)7U, (int32_t)811944);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)8U, (int32_t)3699596);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)9U, (int32_t)-1600420);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)10U, (int32_t)-2140649);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)11U, (int32_t)3507263);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)12U, (int32_t)-3821735);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)13U, (int32_t)3505694);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)14U, (int32_t)-1643818);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)15U, (int32_t)-1699267);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)16U, (int32_t)-539299);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)17U, (int32_t)2348700);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)18U, (int32_t)-300467);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)19U, (int32_t)3539968);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)20U, (int32_t)-2867647);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)21U, (int32_t)3574422);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)22U, (int32_t)-3043716);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)23U, (int32_t)-3861115);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)24U, (int32_t)3915439);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)25U, (int32_t)-2537516);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)26U, (int32_t)-3592148);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)27U, (int32_t)-1661693);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)28U, (int32_t)3530437);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)29U, (int32_t)3077325);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)30U, (int32_t)95776);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)31U, (int32_t)2706023);
}

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline Eurydice_arr_d4
libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
    const Eurydice_arr_d4 *self) {
  return self[0U];
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 280005
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_99(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)280005);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 4010497
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1c(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)2U; i < (size_t)2U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)4010497);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -19422
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)-19422);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 1757237
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_44(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)6U; i < (size_t)6U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)1757237);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -3277672
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a8(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)-3277672);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1399561
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1f(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)10U; i < (size_t)10U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)-1399561);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= -3859737
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_95(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)-3859737);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2118186
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)14U; i < (size_t)14U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)-2118186);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2108549
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)-2108549);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= 2619752
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_e4(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)18U; i < (size_t)18U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)2619752);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1119584
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)-1119584);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -549488
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_05(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)22U; i < (size_t)22U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)-549488);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 3585928
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d9(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)3585928);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -1079900
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3a(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)26U; i < (size_t)26U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)-1079900);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 1024112
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)1024112);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 2725464
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)30U; i < (size_t)30U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U], (int32_t)2725464);
  }
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_99(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1c(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_44(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a8(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1f(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_95(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_e4(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_05(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d9(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3a(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b0(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a0(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 2680103
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_990(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U], (int32_t)2680103);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 3111497
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U], (int32_t)3111497);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -2884855
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a80(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U], (int32_t)-2884855);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= 3119733
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_950(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U], (int32_t)3119733);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= -2091905
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U], (int32_t)-2091905);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -359251
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de0(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U], (int32_t)-359251);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 2353451
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d90(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U], (int32_t)2353451);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 1826347
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b1(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U], (int32_t)1826347);
  }
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_990(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b0(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a80(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_950(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a0(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de0(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d90(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b1(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 466468
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_991(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)4U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)4U], (int32_t)466468);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -876248
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a81(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)4U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)4U], (int32_t)-876248);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -777960
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a1(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)4U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)4U], (int32_t)-777960);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 237124
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d91(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)4U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)4U], (int32_t)237124);
  }
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_991(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a81(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a1(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d91(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -518909
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_992(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)8U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)8U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)8U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)8U], (int32_t)-518909);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -2608894
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a2(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)8U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)8U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)8U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)8U], (int32_t)-2608894);
  }
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_992(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a2(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_993(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)16U; i++) {
    size_t j = i;
    Eurydice_arr_d4 rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)16U]);
    Eurydice_arr_d4 a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)16U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)16U], (int32_t)25847);
  }
}

static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_993(re);
}

static inline void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(re);
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[i0], (int32_t)41978);
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
static inline void libcrux_iot_ml_dsa_simd_portable_invert_ntt_montgomery_c5(
    Eurydice_arr_79 *simd_units) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(simd_units);
}

static inline uint8_t_x2
libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
    size_t index, size_t width) {
  return (KRML_CLITERAL(uint8_t_x2){.fst = (uint8_t)(index / width),
                                    .snd = (uint8_t)(index % width)});
}

typedef struct Eurydice_borrow_slice_u8_x2_s {
  Eurydice_borrow_slice_u8 fst;
  Eurydice_borrow_slice_u8 snd;
} Eurydice_borrow_slice_u8_x2;

/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients

*/
typedef Eurydice_arr_79 libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_5c_s {
  Eurydice_arr_79 data[16U];
} Eurydice_arr_5c;

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
static inline Eurydice_arr_79 libcrux_iot_ml_dsa_polynomial_zero_c2_08(void) {
  Eurydice_arr_79 lit;
  Eurydice_arr_d4 repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_simd_portable_zero_c5();
  }
  memcpy(lit.data, repeat_expression, (size_t)32U * sizeof(Eurydice_arr_d4));
  return lit;
}

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, size_t

*/
typedef struct Eurydice_dst_ref_mut_32_s {
  Eurydice_arr_79 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_32;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, size_t

*/
typedef struct Eurydice_dst_ref_shared_32_s {
  const Eurydice_arr_79 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_32;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_field_modulus with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_13 *out) {
  bool done = false;
  for (size_t i = (size_t)0U; i < randomness.meta / (size_t)24U; i++) {
    size_t _cloop_i = i;
    Eurydice_borrow_slice_u8 random_bytes = Eurydice_slice_subslice_shared_7e(
        randomness, (KRML_CLITERAL(core_ops_range_Range_08){
                        .start = _cloop_i * (size_t)24U,
                        .end = _cloop_i * (size_t)24U + (size_t)24U}));
    if (!done) {
      size_t sampled =
          libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_c5(
              random_bytes, Eurydice_array_to_subslice_from_mut_96(
                                out, sampled_coefficients[0U]));
      sampled_coefficients[0U] = sampled_coefficients[0U] + sampled;
      if (sampled_coefficients[0U] >=
          LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        done = true;
      }
    }
  }
  return done;
}

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
static inline void libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
    Eurydice_dst_ref_shared_fc array, Eurydice_arr_79 *result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_SIMD_UNITS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_from_coefficient_array_c5(
        Eurydice_slice_subslice_shared_46(
            array,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT})),
        &result->data[i0]);
  }
}

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
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
    size_t columns, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_32 matrix, Eurydice_arr_12 *rand_stack0,
    Eurydice_arr_12 *rand_stack1, Eurydice_arr_12 *rand_stack2,
    Eurydice_arr_12 *rand_stack3, Eurydice_dst_ref_mut_4c tmp_stack,
    size_t start_index, size_t elements_requested) {
  Eurydice_arr_48 seed0 = libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed, libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
                start_index, columns));
  Eurydice_arr_48 seed1 = libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed, libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
                start_index + (size_t)1U, columns));
  Eurydice_arr_48 seed2 = libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed, libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
                start_index + (size_t)2U, columns));
  Eurydice_arr_48 seed3 = libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed, libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
                start_index + (size_t)3U, columns));
  libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 state =
      libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_33(
          Eurydice_array_to_slice_shared_8d(&seed0),
          Eurydice_array_to_slice_shared_8d(&seed1),
          Eurydice_array_to_slice_shared_8d(&seed2),
          Eurydice_array_to_slice_shared_8d(&seed3));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_33(
      &state, rand_stack0, rand_stack1, rand_stack2, rand_stack3);
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  bool done0 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice_shared_a8(rand_stack0), &sampled0,
          tmp_stack.ptr);
  bool done1 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice_shared_a8(rand_stack1), &sampled1,
          &tmp_stack.ptr[1U]);
  bool done2 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice_shared_a8(rand_stack2), &sampled2,
          &tmp_stack.ptr[2U]);
  bool done3 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice_shared_a8(rand_stack3), &sampled3,
          &tmp_stack.ptr[3U]);
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            Eurydice_arr_27_x4 randomnesses =
                libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
                    &state);
            if (!done0) {
              done0 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice_shared_7b(&randomnesses.fst),
                      &sampled0, tmp_stack.ptr);
            }
            if (!done1) {
              done1 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice_shared_7b(&randomnesses.snd),
                      &sampled1, &tmp_stack.ptr[1U]);
            }
            if (!done2) {
              done2 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice_shared_7b(&randomnesses.thd),
                      &sampled2, &tmp_stack.ptr[2U]);
            }
            if (!done3) {
              done3 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice_shared_7b(&randomnesses.f3),
                      &sampled3, &tmp_stack.ptr[3U]);
            }
          }
        } else {
          Eurydice_arr_27_x4 randomnesses =
              libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
                  &state);
          if (!done0) {
            done0 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice_shared_7b(&randomnesses.fst),
                    &sampled0, tmp_stack.ptr);
          }
          if (!done1) {
            done1 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice_shared_7b(&randomnesses.snd),
                    &sampled1, &tmp_stack.ptr[1U]);
          }
          if (!done2) {
            done2 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice_shared_7b(&randomnesses.thd),
                    &sampled2, &tmp_stack.ptr[2U]);
          }
          if (!done3) {
            done3 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice_shared_7b(&randomnesses.f3),
                    &sampled3, &tmp_stack.ptr[3U]);
          }
        }
      } else {
        Eurydice_arr_27_x4 randomnesses =
            libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
                &state);
        if (!done0) {
          done0 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice_shared_7b(&randomnesses.fst),
                  &sampled0, tmp_stack.ptr);
        }
        if (!done1) {
          done1 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice_shared_7b(&randomnesses.snd),
                  &sampled1, &tmp_stack.ptr[1U]);
        }
        if (!done2) {
          done2 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice_shared_7b(&randomnesses.thd),
                  &sampled2, &tmp_stack.ptr[2U]);
        }
        if (!done3) {
          done3 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice_shared_7b(&randomnesses.f3),
                  &sampled3, &tmp_stack.ptr[3U]);
        }
      }
    } else {
      Eurydice_arr_27_x4 randomnesses =
          libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
              &state);
      if (!done0) {
        done0 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice_shared_7b(&randomnesses.fst), &sampled0,
                tmp_stack.ptr);
      }
      if (!done1) {
        done1 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice_shared_7b(&randomnesses.snd), &sampled1,
                &tmp_stack.ptr[1U]);
      }
      if (!done2) {
        done2 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice_shared_7b(&randomnesses.thd), &sampled2,
                &tmp_stack.ptr[2U]);
      }
      if (!done3) {
        done3 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice_shared_7b(&randomnesses.f3), &sampled3,
                &tmp_stack.ptr[3U]);
      }
    }
  }
  for (size_t i = (size_t)0U; i < elements_requested; i++) {
    size_t k = i;
    libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
        Eurydice_array_to_slice_shared_20(&tmp_stack.ptr[k]),
        &matrix.ptr[start_index + k]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.matrix_flat
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_samplex4_matrix_flat_15(
    size_t columns, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_32 matrix) {
  Eurydice_arr_12 rand_stack0 = {.data = {0U}};
  Eurydice_arr_12 rand_stack1 = {.data = {0U}};
  Eurydice_arr_12 rand_stack2 = {.data = {0U}};
  Eurydice_arr_12 rand_stack3 = {.data = {0U}};
  Eurydice_arr_38 tmp_stack = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  size_t full_quartets = matrix.meta / (size_t)4U;
  for (size_t i = (size_t)0U; i < full_quartets; i++) {
    size_t start_index = i;
    libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
        columns, seed, matrix, &rand_stack0, &rand_stack1, &rand_stack2,
        &rand_stack3, Eurydice_array_to_slice_mut_f6(&tmp_stack),
        start_index * (size_t)4U, (size_t)4U);
  }
  size_t uu____0 = columns;
  Eurydice_borrow_slice_u8 uu____1 = seed;
  Eurydice_dst_ref_mut_32 uu____2 = matrix;
  Eurydice_arr_12 *uu____3 = &rand_stack0;
  Eurydice_arr_12 *uu____4 = &rand_stack1;
  Eurydice_arr_12 *uu____5 = &rand_stack2;
  Eurydice_arr_12 *uu____6 = &rand_stack3;
  libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
      uu____0, uu____1, uu____2, uu____3, uu____4, uu____5, uu____6,
      Eurydice_array_to_slice_mut_f6(&tmp_stack), full_quartets * (size_t)4U,
      matrix.meta % (size_t)4U);
}

/**
This function found in impl {libcrux_iot_ml_dsa::samplex4::X4Sampler for
libcrux_iot_ml_dsa::samplex4::portable::PortableSampler}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.portable.matrix_flat_ad
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static inline void libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
    size_t columns, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_32 matrix) {
  libcrux_iot_ml_dsa_samplex4_matrix_flat_15(columns, seed, matrix);
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 16
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_97(
    Eurydice_arr_5c *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $8size_t
*/
typedef struct Eurydice_arr_a5_s {
  Eurydice_arr_79 data[8U];
} Eurydice_arr_a5;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_4 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_13 *out) {
  bool done = false;
  for (size_t i = (size_t)0U; i < randomness.meta / (size_t)4U; i++) {
    size_t _cloop_i = i;
    Eurydice_borrow_slice_u8 random_bytes = Eurydice_slice_subslice_shared_7e(
        randomness, (KRML_CLITERAL(core_ops_range_Range_08){
                        .start = _cloop_i * (size_t)4U,
                        .end = _cloop_i * (size_t)4U + (size_t)4U}));
    if (!done) {
      size_t sampled =
          libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_c5(
              random_bytes, Eurydice_array_to_subslice_from_mut_96(
                                out, sampled_coefficients[0U]));
      sampled_coefficients[0U] = sampled_coefficients[0U] + sampled;
      if (sampled_coefficients[0U] >=
          LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        done = true;
      }
    }
  }
  return done;
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_2 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_13 *out) {
  bool done = false;
  for (size_t i = (size_t)0U; i < randomness.meta / (size_t)4U; i++) {
    size_t _cloop_i = i;
    Eurydice_borrow_slice_u8 random_bytes = Eurydice_slice_subslice_shared_7e(
        randomness, (KRML_CLITERAL(core_ops_range_Range_08){
                        .start = _cloop_i * (size_t)4U,
                        .end = _cloop_i * (size_t)4U + (size_t)4U}));
    if (!done) {
      size_t sampled =
          libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_c5(
              random_bytes, Eurydice_array_to_subslice_from_mut_96(
                                out, sampled_coefficients[0U]));
      sampled_coefficients[0U] = sampled_coefficients[0U] + sampled;
      if (sampled_coefficients[0U] >=
          LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        done = true;
      }
    }
  }
  return done;
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 randomness,
    size_t *sampled, Eurydice_arr_13 *out) {
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      return libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_08(
          randomness, sampled, out);
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_08(
      randomness, sampled, out);
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_four_error_ring_elements with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 seed,
    uint16_t start_index, Eurydice_dst_ref_mut_32 re) {
  Eurydice_arr_a2 seed0 =
      libcrux_iot_ml_dsa_sample_add_error_domain_separator(seed, start_index);
  Eurydice_arr_a2 seed1 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 1U);
  Eurydice_arr_a2 seed2 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 2U);
  Eurydice_arr_a2 seed3 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 3U);
  libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 state =
      libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_x4_29(
          Eurydice_array_to_slice_shared_39(&seed0),
          Eurydice_array_to_slice_shared_39(&seed1),
          Eurydice_array_to_slice_shared_39(&seed2),
          Eurydice_array_to_slice_shared_39(&seed3));
  Eurydice_arr_3d_x4 randomnesses0 =
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_x4_29(
          &state);
  Eurydice_arr_38 out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  libcrux_iot_ml_dsa_constants_Eta uu____0 = eta;
  bool done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      uu____0, Eurydice_array_to_slice_shared_d4(&randomnesses0.fst), &sampled0,
      out.data);
  libcrux_iot_ml_dsa_constants_Eta uu____1 = eta;
  bool done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      uu____1, Eurydice_array_to_slice_shared_d4(&randomnesses0.snd), &sampled1,
      &out.data[1U]);
  libcrux_iot_ml_dsa_constants_Eta uu____2 = eta;
  bool done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      uu____2, Eurydice_array_to_slice_shared_d4(&randomnesses0.thd), &sampled2,
      &out.data[2U]);
  libcrux_iot_ml_dsa_constants_Eta uu____3 = eta;
  bool done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      uu____3, Eurydice_array_to_slice_shared_d4(&randomnesses0.f3), &sampled3,
      &out.data[3U]);
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            Eurydice_arr_3d_x4 randomnesses =
                libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
                    &state);
            if (!done0) {
              libcrux_iot_ml_dsa_constants_Eta uu____4 = eta;
              done0 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      uu____4,
                      Eurydice_array_to_slice_shared_d4(&randomnesses.fst),
                      &sampled0, out.data);
            }
            if (!done1) {
              libcrux_iot_ml_dsa_constants_Eta uu____5 = eta;
              done1 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      uu____5,
                      Eurydice_array_to_slice_shared_d4(&randomnesses.snd),
                      &sampled1, &out.data[1U]);
            }
            if (!done2) {
              libcrux_iot_ml_dsa_constants_Eta uu____6 = eta;
              done2 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      uu____6,
                      Eurydice_array_to_slice_shared_d4(&randomnesses.thd),
                      &sampled2, &out.data[2U]);
            }
            if (!done3) {
              libcrux_iot_ml_dsa_constants_Eta uu____7 = eta;
              done3 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      uu____7,
                      Eurydice_array_to_slice_shared_d4(&randomnesses.f3),
                      &sampled3, &out.data[3U]);
            }
          }
        } else {
          Eurydice_arr_3d_x4 randomnesses =
              libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
                  &state);
          if (!done0) {
            libcrux_iot_ml_dsa_constants_Eta uu____8 = eta;
            done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                uu____8, Eurydice_array_to_slice_shared_d4(&randomnesses.fst),
                &sampled0, out.data);
          }
          if (!done1) {
            libcrux_iot_ml_dsa_constants_Eta uu____9 = eta;
            done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                uu____9, Eurydice_array_to_slice_shared_d4(&randomnesses.snd),
                &sampled1, &out.data[1U]);
          }
          if (!done2) {
            libcrux_iot_ml_dsa_constants_Eta uu____10 = eta;
            done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                uu____10, Eurydice_array_to_slice_shared_d4(&randomnesses.thd),
                &sampled2, &out.data[2U]);
          }
          if (!done3) {
            libcrux_iot_ml_dsa_constants_Eta uu____11 = eta;
            done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                uu____11, Eurydice_array_to_slice_shared_d4(&randomnesses.f3),
                &sampled3, &out.data[3U]);
          }
        }
      } else {
        Eurydice_arr_3d_x4 randomnesses =
            libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
                &state);
        if (!done0) {
          libcrux_iot_ml_dsa_constants_Eta uu____12 = eta;
          done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              uu____12, Eurydice_array_to_slice_shared_d4(&randomnesses.fst),
              &sampled0, out.data);
        }
        if (!done1) {
          libcrux_iot_ml_dsa_constants_Eta uu____13 = eta;
          done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              uu____13, Eurydice_array_to_slice_shared_d4(&randomnesses.snd),
              &sampled1, &out.data[1U]);
        }
        if (!done2) {
          libcrux_iot_ml_dsa_constants_Eta uu____14 = eta;
          done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              uu____14, Eurydice_array_to_slice_shared_d4(&randomnesses.thd),
              &sampled2, &out.data[2U]);
        }
        if (!done3) {
          libcrux_iot_ml_dsa_constants_Eta uu____15 = eta;
          done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              uu____15, Eurydice_array_to_slice_shared_d4(&randomnesses.f3),
              &sampled3, &out.data[3U]);
        }
      }
    } else {
      Eurydice_arr_3d_x4 randomnesses =
          libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
              &state);
      if (!done0) {
        libcrux_iot_ml_dsa_constants_Eta uu____16 = eta;
        done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            uu____16, Eurydice_array_to_slice_shared_d4(&randomnesses.fst),
            &sampled0, out.data);
      }
      if (!done1) {
        libcrux_iot_ml_dsa_constants_Eta uu____17 = eta;
        done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            uu____17, Eurydice_array_to_slice_shared_d4(&randomnesses.snd),
            &sampled1, &out.data[1U]);
      }
      if (!done2) {
        libcrux_iot_ml_dsa_constants_Eta uu____18 = eta;
        done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            uu____18, Eurydice_array_to_slice_shared_d4(&randomnesses.thd),
            &sampled2, &out.data[2U]);
      }
      if (!done3) {
        libcrux_iot_ml_dsa_constants_Eta uu____19 = eta;
        done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            uu____19, Eurydice_array_to_slice_shared_d4(&randomnesses.f3),
            &sampled3, &out.data[3U]);
      }
    }
  }
  size_t max0 = (size_t)start_index + (size_t)4U;
  size_t max;
  if (re.meta < max0) {
    max = re.meta;
  } else {
    max = max0;
  }
  for (size_t i = (size_t)start_index; i < max; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
        Eurydice_array_to_slice_shared_20(&out.data[i0 % (size_t)4U]),
        &re.ptr[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.sample_s1_and_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_32 s1_s2) {
  size_t len = s1_s2.meta;
  for (size_t i = (size_t)0U; i < len / (size_t)4U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
        eta, seed, 4U * (uint32_t)(uint16_t)i0, s1_s2);
  }
  size_t remainder = len % (size_t)4U;
  if (remainder != (size_t)0U) {
    libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
        eta, seed, (uint16_t)(len - remainder), s1_s2);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 8
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_970(
    Eurydice_arr_a5 *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_270_s {
  Eurydice_arr_79 data[4U];
} Eurydice_arr_270;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 4
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_971(
    Eurydice_arr_270 *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients, core_ops_range_Range
size_t, Eurydice_derefed_slice
libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 8
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_subslice_shared_52(
    const Eurydice_arr_a5 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_32){.ptr = a->data + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_ntt_08(Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_c5(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt_multiply_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
    Eurydice_arr_79 *lhs, const Eurydice_arr_79 *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_montgomery_multiply_c5(&lhs->data[i0],
                                                            &rhs->data[i0]);
  }
}

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
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_polynomial_add_c2_08(
    Eurydice_arr_79 *self, const Eurydice_arr_79 *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_add_c5(&self->data[i0], &rhs->data[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.invert_ntt_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(
    Eurydice_arr_79 *re) {
  libcrux_iot_ml_dsa_simd_portable_invert_ntt_montgomery_c5(re);
}

/**
 Compute InvertNTT(Â ◦ ŝ₁) + s₂
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_as1_plus_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static inline void libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_dst_ref_shared_32 a_as_ntt,
    Eurydice_dst_ref_shared_32 s1_ntt, Eurydice_dst_ref_shared_32 s1_s2,
    Eurydice_dst_ref_mut_32 result) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      Eurydice_arr_79 product = a_as_ntt.ptr[i1 * columns_in_a + j];
      libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(&product,
                                                        &s1_ntt.ptr[j]);
      libcrux_iot_ml_dsa_polynomial_add_c2_08(&result.ptr[i1], &product);
    }
  }
  for (size_t i = (size_t)0U; i < result.meta; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&result.ptr[i0]);
    libcrux_iot_ml_dsa_polynomial_add_c2_08(&result.ptr[i0],
                                            &s1_s2.ptr[columns_in_a + i0]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 16
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_97(
    const Eurydice_arr_5c *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 4
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_970(
    const Eurydice_arr_270 *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 8
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_971(
    const Eurydice_arr_a5 *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.power2round_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
    Eurydice_dst_ref_mut_32 t, Eurydice_dst_ref_mut_32 t1) {
  for (size_t i0 = (size_t)0U; i0 < t.meta; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_simd_portable_power2round_c5(&t.ptr[i1].data[j],
                                                      &t1.ptr[i1].data[j]);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_t1_serialize_08(
    const Eurydice_arr_79 *re, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_d4 *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_t1_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice_mut_7e(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT})));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
    Eurydice_borrow_slice_u8 seed, Eurydice_dst_ref_shared_32 t1,
    Eurydice_mut_borrow_slice_u8 verification_key_serialized) {
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_7e(
          verification_key_serialized,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end = LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE})),
      seed, uint8_t);
  for (size_t i = (size_t)0U; i < t1.meta; i++) {
    size_t i0 = i;
    const Eurydice_arr_79 *ring_element = &t1.ptr[i0];
    size_t offset = LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
                    i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE;
    libcrux_iot_ml_dsa_encoding_t1_serialize_08(
        ring_element,
        Eurydice_slice_subslice_mut_7e(
            verification_key_serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start = offset,
                .end =
                    offset +
                    LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE})));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 64
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_24(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_06 *out) {
  libcrux_iot_sha3_portable_shake256(Eurydice_array_to_slice_mut_d8(out),
                                     input);
}

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
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_06 *out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_24(input, out);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_error_serialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_79 *re,
    Eurydice_mut_borrow_slice_u8 serialized) {
  size_t output_bytes_per_simd_unit =
      libcrux_iot_ml_dsa_encoding_error_chunk_size(eta);
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_d4 *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_error_serialize_c5(
        eta, simd_unit,
        Eurydice_slice_subslice_mut_7e(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start = i0 * output_bytes_per_simd_unit,
                .end = (i0 + (size_t)1U) * output_bytes_per_simd_unit})));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_t0_serialize_08(
    const Eurydice_arr_79 *re, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_d4 *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_t0_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice_mut_7e(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT})));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.signing_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t error_ring_element_size,
    Eurydice_borrow_slice_u8 seed_matrix, Eurydice_borrow_slice_u8 seed_signing,
    Eurydice_borrow_slice_u8 verification_key, Eurydice_dst_ref_shared_32 s1_2,
    Eurydice_dst_ref_shared_32 t0,
    Eurydice_mut_borrow_slice_u8 signing_key_serialized) {
  size_t offset = (size_t)0U;
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_7e(
          signing_key_serialized,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = offset,
              .end = offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE})),
      seed_matrix, uint8_t);
  offset = offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE;
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_7e(
          signing_key_serialized,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = offset,
              .end = offset +
                     LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE})),
      seed_signing, uint8_t);
  offset = offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE;
  Eurydice_arr_06 verification_key_hash = {.data = {0U}};
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
      verification_key, &verification_key_hash);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_7e(
          signing_key_serialized,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = offset,
              .end =
                  offset +
                  LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH})),
      Eurydice_array_to_slice_shared_d8(&verification_key_hash), uint8_t);
  offset =
      offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH;
  for (size_t i = (size_t)0U; i < s1_2.meta; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_error_serialize_08(
        eta, &s1_2.ptr[i0],
        Eurydice_slice_subslice_mut_7e(
            signing_key_serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start = offset, .end = offset + error_ring_element_size})));
    offset = offset + error_ring_element_size;
  }
  for (size_t i = (size_t)0U; i < t0.meta; i++) {
    size_t _cloop_j = i;
    const Eurydice_arr_79 *ring_element = &t0.ptr[_cloop_j];
    libcrux_iot_ml_dsa_encoding_t0_serialize_08(
        ring_element,
        Eurydice_slice_subslice_mut_7e(
            signing_key_serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start = offset,
                .end =
                    offset +
                    LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE})));
    offset = offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
  }
}

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
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_generate_key_pair_c4(
    Eurydice_arr_60 randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key) {
  Eurydice_arr_d1 seed_expanded0 = {.data = {0U}};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice_shared_6e(&randomness));
  /* original Rust expression is not an lvalue in C */
  Eurydice_array_u8x2 lvalue = {
      .data = {(uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
               (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A}};
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, Eurydice_array_to_slice_shared_26(&lvalue));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_18(&seed_expanded0));
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_18(&seed_expanded0),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 seed_expanded = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_error_vectors = uu____1.fst;
  Eurydice_borrow_slice_u8 seed_for_signing = uu____1.snd;
  Eurydice_arr_5c a_as_ntt;
  Eurydice_arr_79 repeat_expression0[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(a_as_ntt.data, repeat_expression0,
         (size_t)16U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice_mut_97(&a_as_ntt));
  Eurydice_arr_a5 s1_s2;
  Eurydice_arr_79 repeat_expression1[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_s2.data, repeat_expression1, (size_t)8U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA, seed_for_error_vectors,
      Eurydice_array_to_slice_mut_970(&s1_s2));
  Eurydice_arr_270 t0;
  Eurydice_arr_79 repeat_expression2[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0.data, repeat_expression2, (size_t)4U * sizeof(Eurydice_arr_79));
  Eurydice_arr_270 s1_ntt;
  Eurydice_arr_79 repeat_expression3[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_ntt.data, repeat_expression3, (size_t)4U * sizeof(Eurydice_arr_79));
  Eurydice_slice_copy(
      Eurydice_array_to_slice_mut_971(&s1_ntt),
      Eurydice_array_to_subslice_shared_52(
          &s1_s2,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end = LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A})),
      Eurydice_arr_79);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_08(&s1_ntt.data[i0]);
  }
  libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
      Eurydice_array_to_slice_shared_97(&a_as_ntt),
      Eurydice_array_to_slice_shared_970(&s1_ntt),
      Eurydice_array_to_slice_shared_971(&s1_s2),
      Eurydice_array_to_slice_mut_971(&t0));
  Eurydice_arr_270 t1;
  Eurydice_arr_79 repeat_expression[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
      Eurydice_array_to_slice_mut_971(&t0),
      Eurydice_array_to_slice_mut_971(&t1));
  libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
      seed_for_a, Eurydice_array_to_slice_shared_970(&t1), verification_key);
  libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = verification_key.ptr,
                                               .meta = verification_key.meta}),
      Eurydice_array_to_slice_shared_971(&s1_s2),
      Eurydice_array_to_slice_shared_970(&t0), signing_key);
}

/**
 Generate key pair.
*/
static inline void
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_generate_key_pair(
    Eurydice_arr_60 randomness, Eurydice_arr_18 *signing_key,
    Eurydice_arr_40 *verification_key) {
  libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_generate_key_pair_c4(
      randomness, Eurydice_array_to_slice_mut_59(signing_key),
      Eurydice_array_to_slice_mut_bb(verification_key));
}

/**
 Generate an ML-DSA-44 Key Pair
*/
static inline libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2
libcrux_iot_ml_dsa_ml_dsa_44_portable_generate_key_pair(
    Eurydice_arr_60 randomness) {
  Eurydice_arr_18 signing_key = {.data = {0U}};
  Eurydice_arr_40 verification_key = {.data = {0U}};
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_generate_key_pair(
      randomness, &signing_key, &verification_key);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2){
      .signing_key = libcrux_iot_ml_dsa_types_new_f8_ff(signing_key),
      .verification_key =
          libcrux_iot_ml_dsa_types_new_e9_db(verification_key)});
}

#define None 0
#define Some 1

typedef uint8_t Option_b5_tags;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_cb

*/
typedef struct Option_b5_s {
  Option_b5_tags tag;
  Eurydice_arr_cb f0;
} Option_b5;

typedef struct libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext_s {
  Eurydice_borrow_slice_u8 context;
  Option_b5 pre_hash_oid;
} libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext;

#define libcrux_iot_ml_dsa_pre_hash_DomainSeparationError_ContextTooLongError 0

typedef uint8_t libcrux_iot_ml_dsa_pre_hash_DomainSeparationError;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext,
libcrux_iot_ml_dsa_pre_hash_DomainSeparationError

*/
typedef struct Result_80_s {
  Result_8e_tags tag;
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
static inline Result_80 libcrux_iot_ml_dsa_pre_hash_new_c9(
    Eurydice_borrow_slice_u8 context, Option_b5 pre_hash_oid) {
  if (!(context.meta > LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    return (KRML_CLITERAL(Result_80){
        .tag = Ok,
        .val = {
            .case_Ok = {.context = context, .pre_hash_oid = pre_hash_oid}}});
  }
  return (KRML_CLITERAL(Result_80){
      .tag = Err,
      .val = {
          .case_Err =
              libcrux_iot_ml_dsa_pre_hash_DomainSeparationError_ContextTooLongError}});
}

/**
 Returns the pre-hash OID, if any.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
static inline const Option_b5 *libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self) {
  return &self->pre_hash_oid;
}

/**
 Returns the context, guaranteed to be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
static inline Eurydice_borrow_slice_u8 libcrux_iot_ml_dsa_pre_hash_context_c9(
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self) {
  return self->context;
}

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_commitment_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_COMMITMENT_COEFFICIENT))

static KRML_MUSTINLINE bool libcrux_iot_ml_dsa_sample_inside_out_shuffle(
    Eurydice_borrow_slice_u8 randomness, size_t *out_index, uint64_t *signs,
    Eurydice_arr_c3 *result) {
  bool done = false;
  for (size_t i = (size_t)0U; i < randomness.meta; i++) {
    size_t _cloop_j = i;
    const uint8_t *byte = &randomness.ptr[_cloop_j];
    if (!done) {
      size_t sample_at = (size_t)byte[0U];
      if (sample_at <= out_index[0U]) {
        result->data[out_index[0U]] = result->data[sample_at];
        out_index[0U] = out_index[0U] + (size_t)1U;
        result->data[sample_at] =
            (int32_t)1 - (int32_t)2 * (int32_t)(signs[0U] & 1ULL);
        signs[0U] = signs[0U] >> 1U;
      }
      done = out_index[0U] == (size_t)256U;
    }
  }
  return done;
}

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
  Option_b5_tags tag;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext f0;
} Option_e3;

/**
A monomorphic instance of core.result.Result
with types (), libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_87_s {
  Result_8e_tags tag;
  libcrux_iot_ml_dsa_types_SigningError f0;
} Result_87;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_60

*/
typedef struct Option_90_s {
  Option_b5_tags tag;
  Eurydice_arr_60 f0;
} Option_90;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_83

*/
typedef struct Option_cf_s {
  Option_b5_tags tag;
  Eurydice_arr_83 f0;
} Option_cf;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature_64,
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_d6_s {
  Result_8e_tags tag;
  union {
    Eurydice_arr_400 case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} Result_d6;

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_error_deserialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_79 *result) {
  size_t chunk_size = libcrux_iot_ml_dsa_encoding_error_chunk_size(eta);
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_error_deserialize_c5(
        eta,
        Eurydice_slice_subslice_shared_7e(
            serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                            .start = i0 * chunk_size,
                            .end = (i0 + (size_t)1U) * chunk_size})),
        &result->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.error.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t ring_element_size,
    Eurydice_borrow_slice_u8 serialized,
    Eurydice_dst_ref_mut_32 ring_elements) {
  for (size_t i = (size_t)0U; i < serialized.meta / ring_element_size; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                        .start = i0 * ring_element_size,
                        .end = i0 * ring_element_size + ring_element_size}));
    libcrux_iot_ml_dsa_encoding_error_deserialize_08(eta, bytes,
                                                     &ring_elements.ptr[i0]);
    libcrux_iot_ml_dsa_ntt_ntt_08(&ring_elements.ptr[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_t0_deserialize_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_79 *result) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_t0_deserialize_c5(
        Eurydice_slice_subslice_shared_7e(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT})),
        &result->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.t0.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
    Eurydice_borrow_slice_u8 serialized,
    Eurydice_dst_ref_mut_32 ring_elements) {
  for (size_t i = (size_t)0U;
       i <
       serialized.meta / LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE,
            .end = i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE +
                   LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE}));
    libcrux_iot_ml_dsa_encoding_t0_deserialize_08(bytes,
                                                  &ring_elements.ptr[i0]);
    libcrux_iot_ml_dsa_ntt_ntt_08(&ring_elements.ptr[i0]);
  }
}

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
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
    Eurydice_borrow_slice_u8 verification_key_hash,
    const Option_e3 *domain_separation_context,
    Eurydice_borrow_slice_u8 message, Eurydice_arr_06 *message_representative) {
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake,
                                                       verification_key_hash);
  if (domain_separation_context->tag == Some) {
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        *domain_separation_context0 = &domain_separation_context->f0;
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *uu____0 = &shake;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_f10 lvalue0 = {
        .data = {
            (uint8_t)
                core_option__core__option__Option_T__TraitClause_0___is_some(
                    libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(
                        domain_separation_context0),
                    Eurydice_arr_cb, bool)}};
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        uu____0, Eurydice_array_to_slice_shared_07(&lvalue0));
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *uu____1 = &shake;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_f10 lvalue = {
        .data = {(uint8_t)libcrux_iot_ml_dsa_pre_hash_context_c9(
                     domain_separation_context0)
                     .meta}};
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        uu____1, Eurydice_array_to_slice_shared_07(&lvalue));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake,
        libcrux_iot_ml_dsa_pre_hash_context_c9(domain_separation_context0));
    const Option_b5 *uu____2 =
        libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(domain_separation_context0);
    if (uu____2->tag == Some) {
      const Eurydice_arr_cb *pre_hash_oid = &uu____2->f0;
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice_shared_da(pre_hash_oid));
    }
  }
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(&shake, message);
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_d8(message_representative));
}

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_270

*/
typedef struct Option_47_s {
  Option_b5_tags tag;
  Eurydice_arr_270 f0;
} Option_47;

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 576
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_1b(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_5f0 *out) {
  libcrux_iot_sha3_portable_shake256(Eurydice_array_to_slice_mut_fa(out),
                                     input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.hash_functions.portable.shake256_x4_29 with const generics
- OUT_LEN= 576
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_1b(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3,
    Eurydice_arr_5f0 *out0, Eurydice_arr_5f0 *out1, Eurydice_arr_5f0 *out2,
    Eurydice_arr_5f0 *out3) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_1b(input0, out0);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_1b(input1, out1);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_1b(input2, out2);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_1b(input3, out3);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
    size_t gamma1_exponent, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_79 *result) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_gamma1_deserialize_c5(
        Eurydice_slice_subslice_shared_7e(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start = i0 * (gamma1_exponent + (size_t)1U),
                .end = (i0 + (size_t)1U) * (gamma1_exponent + (size_t)1U)})),
        &result->data[i0], gamma1_exponent);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 640
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_c30 *out) {
  libcrux_iot_sha3_portable_shake256(Eurydice_array_to_slice_mut_7d(out),
                                     input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.hash_functions.portable.shake256_x4_29 with const generics
- OUT_LEN= 640
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_c8(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3,
    Eurydice_arr_c30 *out0, Eurydice_arr_c30 *out1, Eurydice_arr_c30 *out2,
    Eurydice_arr_c30 *out3) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(input0, out0);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(input1, out1);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(input2, out2);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(input3, out3);
}

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
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_1b(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_5f0 *out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_1b(input, out);
}

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
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c8(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_c30 *out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(input, out);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_sample_sample_mask_ring_element_1b(
    const Eurydice_arr_a2 *seed, Eurydice_arr_79 *result,
    size_t gamma1_exponent) {
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      Eurydice_arr_5f0 out = {.data = {0U}};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_1b(
          Eurydice_array_to_slice_shared_39(seed), &out);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_fa(&out), result);
      break;
    }
    case 19U: {
      Eurydice_arr_c30 out = {.data = {0U}};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c8(
          Eurydice_array_to_slice_shared_39(seed), &out);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_7d(&out), result);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
    size_t dimension, size_t gamma1_exponent, const Eurydice_arr_06 *seed,
    uint16_t *domain_separator, Eurydice_dst_ref_mut_32 mask) {
  Eurydice_arr_a2 seed0 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice_shared_d8(seed), domain_separator[0U]);
  Eurydice_arr_a2 seed1 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice_shared_d8(seed),
      (uint32_t)domain_separator[0U] + 1U);
  Eurydice_arr_a2 seed2 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice_shared_d8(seed),
      (uint32_t)domain_separator[0U] + 2U);
  Eurydice_arr_a2 seed3 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice_shared_d8(seed),
      (uint32_t)domain_separator[0U] + 3U);
  domain_separator[0U] = (uint32_t)domain_separator[0U] + 4U;
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      Eurydice_arr_5f0 out0 = {.data = {0U}};
      Eurydice_arr_5f0 out1 = {.data = {0U}};
      Eurydice_arr_5f0 out2 = {.data = {0U}};
      Eurydice_arr_5f0 out3 = {.data = {0U}};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_1b(
          Eurydice_array_to_slice_shared_39(&seed0),
          Eurydice_array_to_slice_shared_39(&seed1),
          Eurydice_array_to_slice_shared_39(&seed2),
          Eurydice_array_to_slice_shared_39(&seed3), &out0, &out1, &out2,
          &out3);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_fa(&out0), mask.ptr);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_fa(&out1),
          &mask.ptr[1U]);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_fa(&out2),
          &mask.ptr[2U]);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_fa(&out3),
          &mask.ptr[3U]);
      break;
    }
    case 19U: {
      Eurydice_arr_c30 out0 = {.data = {0U}};
      Eurydice_arr_c30 out1 = {.data = {0U}};
      Eurydice_arr_c30 out2 = {.data = {0U}};
      Eurydice_arr_c30 out3 = {.data = {0U}};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_c8(
          Eurydice_array_to_slice_shared_39(&seed0),
          Eurydice_array_to_slice_shared_39(&seed1),
          Eurydice_array_to_slice_shared_39(&seed2),
          Eurydice_array_to_slice_shared_39(&seed3), &out0, &out1, &out2,
          &out3);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_7d(&out0), mask.ptr);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_7d(&out1),
          &mask.ptr[1U]);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_7d(&out2),
          &mask.ptr[2U]);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_7d(&out3),
          &mask.ptr[3U]);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  for (size_t i = (size_t)4U; i < dimension; i++) {
    size_t i0 = i;
    Eurydice_arr_a2 seed4 =
        libcrux_iot_ml_dsa_sample_add_error_domain_separator(
            Eurydice_array_to_slice_shared_d8(seed), domain_separator[0U]);
    domain_separator[0U] = (uint32_t)domain_separator[0U] + 1U;
    libcrux_iot_ml_dsa_sample_sample_mask_ring_element_1b(&seed4, &mask.ptr[i0],
                                                          gamma1_exponent);
  }
}

/**
 Compute InvertNTT(Â ◦ ŷ)
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_matrix_x_mask
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_dst_ref_shared_32 matrix,
    Eurydice_dst_ref_shared_32 mask, Eurydice_dst_ref_mut_32 result) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      Eurydice_arr_79 product = mask.ptr[j];
      libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
          &product, &matrix.ptr[i1 * columns_in_a + j]);
      libcrux_iot_ml_dsa_polynomial_add_c2_08(&result.ptr[i1], &product);
    }
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&result.ptr[i1]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.decompose_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
    size_t dimension, int32_t gamma2, Eurydice_dst_ref_shared_32 t,
    Eurydice_dst_ref_mut_32 low, Eurydice_dst_ref_mut_32 high) {
  for (size_t i0 = (size_t)0U; i0 < dimension; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_simd_portable_decompose_c5(gamma2, &t.ptr[i1].data[j],
                                                    &low.ptr[i1].data[j],
                                                    &high.ptr[i1].data[j]);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.commitment.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_commitment_serialize_08(
    const Eurydice_arr_79 *re, Eurydice_mut_borrow_slice_u8 serialized) {
  size_t output_bytes_per_simd_unit =
      serialized.meta / ((size_t)8U * (size_t)4U);
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_d4 *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_commitment_serialize_c5(
        simd_unit, Eurydice_slice_subslice_mut_7e(
                       serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                                       .start = i0 * output_bytes_per_simd_unit,
                                       .end = (i0 + (size_t)1U) *
                                              output_bytes_per_simd_unit})));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.commitment.serialize_vector with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
    size_t ring_element_size, Eurydice_dst_ref_shared_32 vector,
    Eurydice_mut_borrow_slice_u8 serialized) {
  size_t offset = (size_t)0U;
  for (size_t i = (size_t)0U; i < vector.meta; i++) {
    size_t _cloop_j = i;
    const Eurydice_arr_79 *ring_element = &vector.ptr[_cloop_j];
    libcrux_iot_ml_dsa_encoding_commitment_serialize_08(
        ring_element, Eurydice_slice_subslice_mut_7e(
                          serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                                          .start = offset,
                                          .end = offset + ring_element_size})));
    offset = offset + ring_element_size;
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_challenge_ring_element with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
    Eurydice_borrow_slice_u8 seed, size_t number_of_ones, Eurydice_arr_79 *re) {
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_a1(seed);
  Eurydice_arr_3d randomness0 =
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_a1(&state);
  Eurydice_array_u8x8 arr;
  memcpy(arr.data,
         Eurydice_array_to_subslice_shared_360(
             &randomness0, (KRML_CLITERAL(core_ops_range_Range_08){
                               .start = (size_t)0U, .end = (size_t)8U}))
             .ptr,
         (size_t)8U * sizeof(uint8_t));
  uint64_t signs = core_num__u64__from_le_bytes(unwrap_26_ab(
      (KRML_CLITERAL(Result_8e){.tag = Ok, .val = {.case_Ok = arr}})));
  Eurydice_arr_c3 result = {.data = {0U}};
  size_t out_index = (size_t)256U - number_of_ones;
  bool done = libcrux_iot_ml_dsa_sample_inside_out_shuffle(
      Eurydice_array_to_subslice_from_shared_8c(&randomness0, (size_t)8U),
      &out_index, &signs, &result);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_3d randomness =
          libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_a1(
              &state);
      done = libcrux_iot_ml_dsa_sample_inside_out_shuffle(
          Eurydice_array_to_slice_shared_d4(&randomness), &out_index, &signs,
          &result);
    }
  }
  libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
      Eurydice_array_to_slice_shared_200(&result), re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.vector_times_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
    Eurydice_dst_ref_mut_32 vector, const Eurydice_arr_79 *ring_element) {
  for (size_t i = (size_t)0U; i < vector.meta; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(&vector.ptr[i0],
                                                      ring_element);
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&vector.ptr[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.add_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_add_vectors_08(
    size_t dimension, Eurydice_dst_ref_mut_32 lhs,
    Eurydice_dst_ref_shared_32 rhs) {
  for (size_t i = (size_t)0U; i < dimension; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_add_c2_08(&lhs.ptr[i0], &rhs.ptr[i0]);
  }
}

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
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_polynomial_subtract_c2_08(
    Eurydice_arr_79 *self, const Eurydice_arr_79 *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_subtract_c5(&self->data[i0],
                                                 &rhs->data[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.subtract_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
    size_t dimension, Eurydice_dst_ref_mut_32 lhs,
    Eurydice_dst_ref_shared_32 rhs) {
  for (size_t i = (size_t)0U; i < dimension; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_subtract_c2_08(&lhs.ptr[i0], &rhs.ptr[i0]);
  }
}

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
static KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_polynomial_infinity_norm_exceeds_c2_08(
    const Eurydice_arr_79 *self, int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    bool uu____0;
    if (result) {
      uu____0 = true;
    } else {
      uu____0 = libcrux_iot_ml_dsa_simd_portable_infinity_norm_exceeds_c5(
          &self->data[i0], bound);
    }
    result = uu____0;
  }
  return result;
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.arithmetic.vector_infinity_norm_exceeds with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
    Eurydice_dst_ref_shared_32 vector, int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U; i < vector.meta; i++) {
    size_t _cloop_j = i;
    const Eurydice_arr_79 *ring_element = &vector.ptr[_cloop_j];
    bool uu____0;
    if (result) {
      uu____0 = true;
    } else {
      uu____0 = libcrux_iot_ml_dsa_polynomial_infinity_norm_exceeds_c2_08(
          ring_element, bound);
    }
    result = uu____0;
  }
  return result;
}

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
static inline Eurydice_arr_c3 libcrux_iot_ml_dsa_polynomial_to_i32_array_c2_08(
    const Eurydice_arr_79 *self) {
  Eurydice_arr_c3 result = {.data = {0U}};
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_d4 *simd_unit = &self->data[i0];
    libcrux_iot_ml_dsa_simd_portable_to_coefficient_array_c5(
        simd_unit,
        Eurydice_array_to_subslice_mut_7f(
            &result,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT})));
  }
  return result;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.make_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE size_t libcrux_iot_ml_dsa_arithmetic_make_hint_08(
    Eurydice_dst_ref_shared_32 low, Eurydice_dst_ref_shared_32 high,
    int32_t gamma2, Eurydice_dst_ref_mut_22 hint) {
  size_t true_hints = (size_t)0U;
  Eurydice_arr_79 hint_simd = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  for (size_t i0 = (size_t)0U; i0 < low.meta; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
      size_t j = i;
      size_t one_hints_count = libcrux_iot_ml_dsa_simd_portable_compute_hint_c5(
          &low.ptr[i1].data[j], &high.ptr[i1].data[j], gamma2,
          &hint_simd.data[j]);
      true_hints = true_hints + one_hints_count;
    }
    Eurydice_arr_c3 uu____0 =
        libcrux_iot_ml_dsa_polynomial_to_i32_array_c2_08(&hint_simd);
    hint.ptr[i1] = uu____0;
  }
  return true_hints;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_gamma1_serialize_08(
    const Eurydice_arr_79 *re, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_d4 *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_gamma1_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice_mut_7e(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start = i0 * (gamma1_exponent + (size_t)1U),
                .end = (i0 + (size_t)1U) * (gamma1_exponent + (size_t)1U)})),
        gamma1_exponent);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_signature_serialize_08(
    Eurydice_borrow_slice_u8 commitment_hash,
    Eurydice_dst_ref_shared_32 signer_response, Eurydice_dst_ref_shared_22 hint,
    size_t commitment_hash_size, size_t columns_in_a, size_t rows_in_a,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, Eurydice_mut_borrow_slice_u8 signature) {
  size_t offset = (size_t)0U;
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_7e(
          signature,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = offset, .end = offset + commitment_hash_size})),
      commitment_hash, uint8_t);
  offset = offset + commitment_hash_size;
  for (size_t i = (size_t)0U; i < columns_in_a; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_gamma1_serialize_08(
        &signer_response.ptr[i0],
        Eurydice_slice_subslice_mut_7e(
            signature,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start = offset, .end = offset + gamma1_ring_element_size})),
        gamma1_exponent);
    offset = offset + gamma1_ring_element_size;
  }
  size_t true_hints_seen = (size_t)0U;
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      size_t j = i;
      if (hint.ptr[i1].data[j] == (int32_t)1) {
        signature.ptr[offset + true_hints_seen] = (uint8_t)j;
        true_hints_seen++;
      }
    }
    signature.ptr[offset + max_ones_in_hint + i1] = (uint8_t)true_hints_seen;
  }
}

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
static KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 remaining_serialized0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_signing = uu____1.fst;
  Eurydice_borrow_slice_u8 remaining_serialized1 = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 verification_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 remaining_serialized2 = uu____2.snd;
  Eurydice_borrow_slice_u8_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s1_serialized = uu____3.fst;
  Eurydice_borrow_slice_u8 remaining_serialized = uu____3.snd;
  Eurydice_borrow_slice_u8_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s2_serialized = uu____4.fst;
  Eurydice_borrow_slice_u8 t0_serialized = uu____4.snd;
  Eurydice_arr_270 s1_as_ntt;
  Eurydice_arr_79 repeat_expression0[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_as_ntt.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_79));
  Eurydice_arr_270 s2_as_ntt;
  Eurydice_arr_79 repeat_expression1[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s2_as_ntt.data, repeat_expression1,
         (size_t)4U * sizeof(Eurydice_arr_79));
  Eurydice_arr_270 t0_as_ntt;
  Eurydice_arr_79 repeat_expression2[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0_as_ntt.data, repeat_expression2,
         (size_t)4U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE,
      s1_serialized, Eurydice_array_to_slice_mut_971(&s1_as_ntt));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE,
      s2_serialized, Eurydice_array_to_slice_mut_971(&s2_as_ntt));
  libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
      t0_serialized, Eurydice_array_to_slice_mut_971(&t0_as_ntt));
  Eurydice_arr_5c matrix;
  Eurydice_arr_79 repeat_expression3[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(matrix.data, repeat_expression3,
         (size_t)16U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice_mut_97(&matrix));
  Eurydice_arr_06 message_representative = {.data = {0U}};
  libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
      verification_key_hash, &domain_separation_context, message,
      &message_representative);
  Eurydice_arr_06 mask_seed = {.data = {0U}};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake0 =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake0,
                                                       seed_for_signing);
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake0, Eurydice_array_to_slice_shared_6e(&randomness));
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake0, Eurydice_array_to_slice_shared_d8(&message_representative));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake0, Eurydice_array_to_slice_mut_d8(&mask_seed));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  Option_90 commitment_hash0 = {.tag = None};
  Option_47 signer_response0 = {.tag = None};
  Option_cf hint0 = {.tag = None};
  while (attempt < LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    Eurydice_arr_270 mask;
    Eurydice_arr_79 repeat_expression4[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression4[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(mask.data, repeat_expression4, (size_t)4U * sizeof(Eurydice_arr_79));
    Eurydice_arr_270 w0;
    Eurydice_arr_79 repeat_expression5[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression5[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(w0.data, repeat_expression5, (size_t)4U * sizeof(Eurydice_arr_79));
    Eurydice_arr_270 commitment;
    Eurydice_arr_79 repeat_expression6[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression6[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(commitment.data, repeat_expression6,
           (size_t)4U * sizeof(Eurydice_arr_79));
    libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT, &mask_seed,
        &domain_separator_for_mask, Eurydice_array_to_slice_mut_971(&mask));
    Eurydice_arr_270 a_x_mask;
    Eurydice_arr_79 repeat_expression[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(a_x_mask.data, repeat_expression,
           (size_t)4U * sizeof(Eurydice_arr_79));
    Eurydice_arr_270 mask_ntt =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)4U, &mask, Eurydice_arr_79, Eurydice_arr_270);
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      size_t i0 = i;
      libcrux_iot_ml_dsa_ntt_ntt_08(&mask_ntt.data[i0]);
    }
    libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
        Eurydice_array_to_slice_shared_97(&matrix),
        Eurydice_array_to_slice_shared_970(&mask_ntt),
        Eurydice_array_to_slice_mut_971(&a_x_mask));
    libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2,
        Eurydice_array_to_slice_shared_970(&a_x_mask),
        Eurydice_array_to_slice_mut_971(&w0),
        Eurydice_array_to_slice_mut_971(&commitment));
    Eurydice_arr_60 commitment_hash_candidate = {.data = {0U}};
    Eurydice_arr_56 commitment_serialized = {.data = {0U}};
    libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
        LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE,
        Eurydice_array_to_slice_shared_970(&commitment),
        Eurydice_array_to_slice_mut_ee(&commitment_serialized));
    libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
        libcrux_iot_ml_dsa_hash_functions_portable_init_88();
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake, Eurydice_array_to_slice_shared_d8(&message_representative));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
        &shake, Eurydice_array_to_slice_shared_ee(&commitment_serialized));
    libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
        &shake, Eurydice_array_to_slice_mut_6e(&commitment_hash_candidate));
    Eurydice_arr_79 verifier_challenge =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
        Eurydice_array_to_slice_shared_6e(&commitment_hash_candidate),
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
    Eurydice_arr_270 challenge_times_s1 =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)4U, &s1_as_ntt, Eurydice_arr_79, Eurydice_arr_270);
    Eurydice_arr_270 challenge_times_s2 =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)4U, &s2_as_ntt, Eurydice_arr_79, Eurydice_arr_270);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice_mut_971(&challenge_times_s1),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice_mut_971(&challenge_times_s2),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_add_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
        Eurydice_array_to_slice_mut_971(&mask),
        Eurydice_array_to_slice_shared_970(&challenge_times_s1));
    libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
        Eurydice_array_to_slice_mut_971(&w0),
        Eurydice_array_to_slice_shared_970(&challenge_times_s2));
    if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice_shared_970(&mask),
            ((int32_t)1 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA)) {
      if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
              Eurydice_array_to_slice_shared_970(&w0),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2 -
                  LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA)) {
        Eurydice_arr_270 challenge_times_t0 =
            core_array__core__clone__Clone_for__Array_T__N___clone(
                (size_t)4U, &t0_as_ntt, Eurydice_arr_79, Eurydice_arr_270);
        libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
            Eurydice_array_to_slice_mut_971(&challenge_times_t0),
            &verifier_challenge);
        if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
                Eurydice_array_to_slice_shared_970(&challenge_times_t0),
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2)) {
          libcrux_iot_ml_dsa_matrix_add_vectors_08(
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
              Eurydice_array_to_slice_mut_971(&w0),
              Eurydice_array_to_slice_shared_970(&challenge_times_t0));
          Eurydice_arr_83 hint_candidate = {.data = {{.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}}}};
          size_t ones_in_hint = libcrux_iot_ml_dsa_arithmetic_make_hint_08(
              Eurydice_array_to_slice_shared_970(&w0),
              Eurydice_array_to_slice_shared_970(&commitment),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2,
              Eurydice_array_to_slice_mut_6d(&hint_candidate));
          if (!(ones_in_hint >
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            commitment_hash0 = (KRML_CLITERAL(Option_90){
                .tag = Some, .f0 = commitment_hash_candidate});
            signer_response0 =
                (KRML_CLITERAL(Option_47){.tag = Some, .f0 = mask});
            hint0 =
                (KRML_CLITERAL(Option_cf){.tag = Some, .f0 = hint_candidate});
          }
        }
      }
    }
  }
  Result_87 uu____5;
  if (commitment_hash0.tag == None) {
    uu____5 = (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    Eurydice_arr_60 commitment_hash = commitment_hash0.f0;
    Eurydice_arr_60 commitment_hash1 = commitment_hash;
    if (signer_response0.tag == None) {
      uu____5 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      Eurydice_arr_270 signer_response = signer_response0.f0;
      Eurydice_arr_270 signer_response1 = signer_response;
      if (!(hint0.tag == None)) {
        Eurydice_arr_83 hint = hint0.f0;
        Eurydice_arr_83 hint1 = hint;
        libcrux_iot_ml_dsa_encoding_signature_serialize_08(
            Eurydice_array_to_slice_shared_6e(&commitment_hash1),
            Eurydice_array_to_slice_shared_970(&signer_response1),
            Eurydice_array_to_slice_shared_6d(&hint1),
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT,
            LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice_mut_180(signature));
        return (KRML_CLITERAL(Result_87){.tag = Ok});
      }
      uu____5 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____5;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
static KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_b5){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
      signing_key, message,
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      randomness, signature);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
static KRML_MUSTINLINE Result_d6
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  Eurydice_arr_400 signature = libcrux_iot_ml_dsa_types_zero_ad_1a();
  Result_87 uu____0 = libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
      signing_key, message, context, randomness, &signature);
  Result_d6 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_d6){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_d6){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign.
*/
static inline Result_d6
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_c4(
      Eurydice_array_to_slice_shared_59(signing_key), message, context,
      randomness);
}

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_d6 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign(
      libcrux_iot_ml_dsa_types_as_ref_f8_ff(signing_key), message, context,
      randomness);
}

/**
 Sign.
*/
static inline Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_mut(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
      Eurydice_array_to_slice_shared_59(signing_key), message, context,
      randomness, signature);
}

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_87 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_mut(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_mut(
      libcrux_iot_ml_dsa_types_as_ref_f8_ff(signing_key), message, context,
      randomness, signature);
}

#define LIBCRUX_IOT_ML_DSA_PRE_HASH_SHAKE128_OID \
  ((KRML_CLITERAL(Eurydice_arr_cb){              \
      .data = {6U, 9U, 96U, 134U, 72U, 1U, 101U, 3U, 4U, 2U, 11U}}))

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
static inline Eurydice_arr_cb libcrux_iot_ml_dsa_pre_hash_oid_0b(void) {
  return LIBCRUX_IOT_ML_DSA_PRE_HASH_SHAKE128_OID;
}

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.pre_hash.hash_0b
with types libcrux_iot_ml_dsa_hash_functions_portable_Shake128
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
    Eurydice_borrow_slice_u8 message, Eurydice_mut_borrow_slice_u8 output) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake128_e2(message, output);
}

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
static KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness,
    Eurydice_arr_400 *signature) {
  if (!(context.meta > LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
    Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
        context, (KRML_CLITERAL(Option_b5){
                     .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
    if (!(uu____0.tag == Ok)) {
      return (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc =
        uu____0.val.case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        domain_separation_context = dsc;
    return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
        signing_key,
        (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                                 .meta = pre_hash_buffer.meta}),
        (KRML_CLITERAL(Option_e3){.tag = Some,
                                  .f0 = domain_separation_context}),
        randomness, signature);
  }
  return (KRML_CLITERAL(Result_87){
      .tag = Err,
      .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
}

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
static KRML_MUSTINLINE Result_d6
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness) {
  Eurydice_arr_400 signature = libcrux_iot_ml_dsa_types_zero_ad_1a();
  Result_87 uu____0 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_mut_36(
          signing_key, message, context, pre_hash_buffer, randomness,
          &signature);
  Result_d6 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_d6){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_d6){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign (pre-hashed).
*/
static inline Result_d6
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_pre_hashed_shake128(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_36(
      Eurydice_array_to_slice_shared_59(signing_key), message, context,
      pre_hash_buffer, randomness);
}

/**
 Generate a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_d6
libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_18 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  Eurydice_arr_60 pre_hash_buffer = {.data = {0U}};
  const Eurydice_arr_18 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_f8_ff(signing_key);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_pre_hashed_shake128(
      uu____0, message, context,
      Eurydice_array_to_slice_mut_6e(&pre_hash_buffer), randomness);
}

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
  Result_8e_tags tag;
  libcrux_iot_ml_dsa_types_VerificationError f0;
} Result_5c;

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static inline void libcrux_iot_ml_dsa_encoding_t1_deserialize_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_79 *result) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_t1_deserialize_c5(
        Eurydice_slice_subslice_shared_7e(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start = i0 * LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW})),
        &result->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.deserialize with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
    size_t rows_in_a, size_t verification_key_size,
    Eurydice_borrow_slice_u8 serialized, Eurydice_dst_ref_mut_32 t1) {
  for (size_t i = (size_t)0U; i < rows_in_a; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_t1_deserialize_08(
        Eurydice_slice_subslice_shared_7e(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE})),
        &t1.ptr[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
    size_t columns_in_a, size_t rows_in_a, size_t commitment_hash_size,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, size_t signature_size,
    Eurydice_borrow_slice_u8 serialized,
    Eurydice_mut_borrow_slice_u8 out_commitment_hash,
    Eurydice_dst_ref_mut_32 out_signer_response,
    Eurydice_dst_ref_mut_22 out_hint) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      serialized, commitment_hash_size, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 commitment_hash = uu____0.fst;
  Eurydice_borrow_slice_u8 rest_of_serialized = uu____0.snd;
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_7e(
          out_commitment_hash,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U, .end = commitment_hash_size})),
      commitment_hash, uint8_t);
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      rest_of_serialized, gamma1_ring_element_size * columns_in_a, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 signer_response_serialized = uu____1.fst;
  Eurydice_borrow_slice_u8 hint_serialized = uu____1.snd;
  for (size_t i = (size_t)0U; i < columns_in_a; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
        gamma1_exponent,
        Eurydice_slice_subslice_shared_7e(
            signer_response_serialized,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start = i0 * gamma1_ring_element_size,
                .end = (i0 + (size_t)1U) * gamma1_ring_element_size})),
        &out_signer_response.ptr[i0]);
  }
  size_t previous_true_hints_seen = (size_t)0U;
  size_t i0 = (size_t)0U;
  bool malformed_hint = false;
  while (true) {
    if (malformed_hint) {
      break;
    } else if (i0 < rows_in_a) {
      size_t current_true_hints_seen =
          (size_t)hint_serialized.ptr[max_ones_in_hint + i0];
      if (current_true_hints_seen < previous_true_hints_seen) {
        malformed_hint = true;
      } else if (previous_true_hints_seen > max_ones_in_hint) {
        malformed_hint = true;
      }
      size_t j = previous_true_hints_seen;
      while (true) {
        if (malformed_hint) {
          break;
        } else if (j < current_true_hints_seen) {
          if (j > previous_true_hints_seen) {
            if (hint_serialized.ptr[j] <= hint_serialized.ptr[j - (size_t)1U]) {
              malformed_hint = true;
            }
          }
          if (!malformed_hint) {
            libcrux_iot_ml_dsa_encoding_signature_set_hint(
                out_hint, i0, (size_t)hint_serialized.ptr[j]);
            j++;
          }
        } else {
          break;
        }
      }
      if (!malformed_hint) {
        previous_true_hints_seen = current_true_hints_seen;
        i0++;
      }
    } else {
      break;
    }
  }
  i0 = previous_true_hints_seen;
  for (size_t i = i0; i < max_ones_in_hint; i++) {
    size_t j = i;
    if (!(hint_serialized.ptr[j] != 0U)) {
      continue;
    }
    malformed_hint = true;
    break;
  }
  if (!malformed_hint) {
    return (KRML_CLITERAL(Result_5c){.tag = Ok});
  }
  return (KRML_CLITERAL(Result_5c){
      .tag = Err,
      .f0 = libcrux_iot_ml_dsa_types_VerificationError_MalformedHintError});
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_ring_element_08(
    Eurydice_borrow_slice_u8 seed, uint8_t_x2 indices, Eurydice_arr_79 *out,
    Eurydice_arr_12 *rand_stack, Eurydice_arr_27 *rand_block,
    Eurydice_arr_13 *tmp_stack) {
  Eurydice_arr_48 domain_separated_seed =
      libcrux_iot_ml_dsa_sample_add_domain_separator(seed, indices);
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_b5(
          Eurydice_array_to_slice_shared_8d(&domain_separated_seed));
  libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_b5(
      &state, rand_stack);
  size_t sampled = (size_t)0U;
  bool done =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice_shared_a8(rand_stack), &sampled, tmp_stack);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_b5(
          &state, rand_block);
      if (!done) {
        done =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice_shared_7b(rand_block), &sampled,
                tmp_stack);
      }
    }
  }
  libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
      Eurydice_array_to_slice_shared_20(tmp_stack), out);
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce with const
generics
- SHIFT_BY= 13
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_84(
    Eurydice_arr_d4 *simd_unit) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    simd_unit->data[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(
            simd_unit->data[i0] << (uint32_t)(int32_t)13);
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.shift_left_then_reduce_c5 with const generics
- SHIFT_BY= 13
*/
static inline void
libcrux_iot_ml_dsa_simd_portable_shift_left_then_reduce_c5_84(
    Eurydice_arr_d4 *simd_unit) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_84(
      simd_unit);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.shift_left_then_reduce
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics
- SHIFT_BY= 13
*/
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_arithmetic_shift_left_then_reduce_41(Eurydice_arr_79 *re) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_shift_left_then_reduce_c5_84(
        &re->data[i0]);
  }
}

/**
 Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_w_approx
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_borrow_slice_u8 seed,
    Eurydice_arr_12 *rand_stack, Eurydice_arr_27 *rand_block,
    Eurydice_arr_13 *tmp_stack, Eurydice_arr_79 *poly_slot,
    Eurydice_dst_ref_shared_32 signer_response,
    const Eurydice_arr_79 *verifier_challenge_as_ntt,
    Eurydice_dst_ref_mut_32 t1) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    Eurydice_arr_79 inner_result = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_sample_sample_ring_element_08(
          seed,
          (KRML_CLITERAL(uint8_t_x2){.fst = (uint8_t)i1, .snd = (uint8_t)j}),
          poly_slot, rand_stack, rand_block, tmp_stack);
      libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
          poly_slot, &signer_response.ptr[j]);
      libcrux_iot_ml_dsa_polynomial_add_c2_08(&inner_result, poly_slot);
    }
    libcrux_iot_ml_dsa_arithmetic_shift_left_then_reduce_41(&t1.ptr[i1]);
    libcrux_iot_ml_dsa_ntt_ntt_08(&t1.ptr[i1]);
    libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
        &t1.ptr[i1], verifier_challenge_as_ntt);
    libcrux_iot_ml_dsa_polynomial_subtract_c2_08(&inner_result, &t1.ptr[i1]);
    t1.ptr[i1] = inner_result;
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&t1.ptr[i1]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.use_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
static KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_use_hint_08(
    int32_t gamma2, Eurydice_dst_ref_shared_22 hint,
    Eurydice_dst_ref_mut_32 re_vector) {
  for (size_t i0 = (size_t)0U; i0 < re_vector.meta; i0++) {
    size_t i1 = i0;
    Eurydice_arr_79 tmp = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
        Eurydice_array_to_slice_shared_200(&hint.ptr[i1]), &tmp);
    for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_simd_portable_use_hint_c5(
          gamma2, &re_vector.ptr[i1].data[j], &tmp.data[j]);
    }
    re_vector.ptr[i1] = tmp;
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_400 *signature_serialized) {
  Eurydice_arr_12 rand_stack = {.data = {0U}};
  Eurydice_arr_27 rand_block = {.data = {0U}};
  Eurydice_arr_13 tmp_stack = {.data = {0U}};
  Eurydice_arr_79 poly_slot = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_bb(verification_key),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 t1_serialized = uu____0.snd;
  Eurydice_arr_270 t1;
  Eurydice_arr_79 repeat_expression0[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression0, (size_t)4U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_VERIFICATION_KEY_SIZE,
      t1_serialized, Eurydice_array_to_slice_mut_971(&t1));
  Eurydice_arr_60 deserialized_commitment_hash = {.data = {0U}};
  Eurydice_arr_270 deserialized_signer_response;
  Eurydice_arr_79 repeat_expression[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(deserialized_signer_response.data, repeat_expression,
         (size_t)4U * sizeof(Eurydice_arr_79));
  Eurydice_arr_83 deserialized_hint = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Result_5c uu____1 = libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_GAMMA1_RING_ELEMENT_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_SIGNATURE_SIZE,
      Eurydice_array_to_slice_shared_180(signature_serialized),
      Eurydice_array_to_slice_mut_6e(&deserialized_commitment_hash),
      Eurydice_array_to_slice_mut_971(&deserialized_signer_response),
      Eurydice_array_to_slice_mut_6d(&deserialized_hint));
  Result_5c uu____2;
  if (uu____1.tag == Ok) {
    if (libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice_shared_970(&deserialized_signer_response),
            ((int32_t)2 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA)) {
      uu____2 = (KRML_CLITERAL(Result_5c){
          .tag = Err,
          .f0 =
              libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      Eurydice_arr_06 verification_key_hash = {.data = {0U}};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
          Eurydice_array_to_slice_shared_bb(verification_key),
          &verification_key_hash);
      Eurydice_arr_06 message_representative = {.data = {0U}};
      libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
          Eurydice_array_to_slice_shared_d8(&verification_key_hash),
          &domain_separation_context, message, &message_representative);
      Eurydice_arr_79 verifier_challenge =
          libcrux_iot_ml_dsa_polynomial_zero_c2_08();
      libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
          Eurydice_array_to_slice_shared_6e(&deserialized_commitment_hash),
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
      for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
        size_t i0 = i;
        libcrux_iot_ml_dsa_ntt_ntt_08(&deserialized_signer_response.data[i0]);
      }
      libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A, seed_for_a,
          &rand_stack, &rand_block, &tmp_stack, &poly_slot,
          Eurydice_array_to_slice_shared_970(&deserialized_signer_response),
          &verifier_challenge, Eurydice_array_to_slice_mut_971(&t1));
      Eurydice_arr_60 recomputed_commitment_hash = {.data = {0U}};
      libcrux_iot_ml_dsa_arithmetic_use_hint_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2,
          Eurydice_array_to_slice_shared_6d(&deserialized_hint),
          Eurydice_array_to_slice_mut_971(&t1));
      Eurydice_arr_56 commitment_serialized = {.data = {0U}};
      libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE,
          Eurydice_array_to_slice_shared_970(&t1),
          Eurydice_array_to_slice_mut_ee(&commitment_serialized));
      libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
          libcrux_iot_ml_dsa_hash_functions_portable_init_88();
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice_shared_d8(&message_representative));
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
          &shake, Eurydice_array_to_slice_shared_ee(&commitment_serialized));
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
          &shake, Eurydice_array_to_slice_mut_6e(&recomputed_commitment_hash));
      if (Eurydice_array_eq((size_t)32U, &deserialized_commitment_hash,
                            &recomputed_commitment_hash, uint8_t)) {
        uu____2 = (KRML_CLITERAL(Result_5c){.tag = Ok});
      } else {
        uu____2 = (KRML_CLITERAL(Result_5c){
            .tag = Err,
            .f0 =
                libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_iot_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 = (KRML_CLITERAL(Result_5c){.tag = Err, .f0 = e});
  }
  return uu____2;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_c4(
    const Eurydice_arr_40 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_400 *signature_serialized) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_b5){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
      verification_key_serialized, message,
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify.
*/
static inline Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_400 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_c4(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_5c libcrux_iot_ml_dsa_ml_dsa_44_portable_verify(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_400 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify(
      libcrux_iot_ml_dsa_types_as_ref_e9_db(verification_key), message, context,
      libcrux_iot_ml_dsa_types_as_ref_ad_1a(signature));
}

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
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_pre_hashed_36(
    const Eurydice_arr_40 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_400 *signature_serialized) {
  libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_b5){
                   .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
      verification_key_serialized,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                               .meta = pre_hash_buffer.meta}),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
static inline Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify_pre_hashed_shake128(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_400 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_pre_hashed_36(
      verification_key, message, context, pre_hash_buffer, signature);
}

/**
 Verify a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_5c
libcrux_iot_ml_dsa_ml_dsa_44_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_40 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_400 *signature) {
  Eurydice_arr_60 pre_hash_buffer = {.data = {0U}};
  const Eurydice_arr_40 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_e9_db(verification_key);
  Eurydice_borrow_slice_u8 uu____1 = message;
  Eurydice_borrow_slice_u8 uu____2 = context;
  Eurydice_mut_borrow_slice_u8 uu____3 =
      Eurydice_array_to_slice_mut_6e(&pre_hash_buffer);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3,
      libcrux_iot_ml_dsa_types_as_ref_ad_1a(signature));
}

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_ERROR_COEFFICIENT))

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $30size_t
*/
typedef struct Eurydice_arr_d2_s {
  Eurydice_arr_79 data[30U];
} Eurydice_arr_d2;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 30
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_972(
    Eurydice_arr_d2 *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)30U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $11size_t
*/
typedef struct Eurydice_arr_74_s {
  Eurydice_arr_79 data[11U];
} Eurydice_arr_74;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 11
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_973(
    Eurydice_arr_74 *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)11U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $6size_t
*/
typedef struct Eurydice_arr_10_s {
  Eurydice_arr_79 data[6U];
} Eurydice_arr_10;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $5size_t
*/
typedef struct Eurydice_arr_1d_s {
  Eurydice_arr_79 data[5U];
} Eurydice_arr_1d;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 5
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_974(
    Eurydice_arr_1d *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)5U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients, core_ops_range_Range
size_t, Eurydice_derefed_slice
libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 11
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_subslice_shared_520(
    const Eurydice_arr_74 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_32){.ptr = a->data + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 30
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_972(
    const Eurydice_arr_d2 *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)30U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 5
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_973(
    const Eurydice_arr_1d *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)5U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 11
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_974(
    const Eurydice_arr_74 *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)11U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 6
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_975(
    Eurydice_arr_10 *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)6U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 6
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_975(
    const Eurydice_arr_10 *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)6U;
  return lit;
}

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
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_c4(
    Eurydice_arr_60 randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key) {
  Eurydice_arr_d1 seed_expanded0 = {.data = {0U}};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice_shared_6e(&randomness));
  /* original Rust expression is not an lvalue in C */
  Eurydice_array_u8x2 lvalue = {
      .data = {(uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
               (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A}};
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, Eurydice_array_to_slice_shared_26(&lvalue));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_18(&seed_expanded0));
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_18(&seed_expanded0),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 seed_expanded = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_error_vectors = uu____1.fst;
  Eurydice_borrow_slice_u8 seed_for_signing = uu____1.snd;
  Eurydice_arr_d2 a_as_ntt;
  Eurydice_arr_79 repeat_expression0[30U];
  for (size_t i = (size_t)0U; i < (size_t)30U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(a_as_ntt.data, repeat_expression0,
         (size_t)30U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice_mut_972(&a_as_ntt));
  Eurydice_arr_74 s1_s2;
  Eurydice_arr_79 repeat_expression1[11U];
  for (size_t i = (size_t)0U; i < (size_t)11U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_s2.data, repeat_expression1, (size_t)11U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA, seed_for_error_vectors,
      Eurydice_array_to_slice_mut_973(&s1_s2));
  Eurydice_arr_10 t0;
  Eurydice_arr_79 repeat_expression2[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0.data, repeat_expression2, (size_t)6U * sizeof(Eurydice_arr_79));
  Eurydice_arr_1d s1_ntt;
  Eurydice_arr_79 repeat_expression3[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_ntt.data, repeat_expression3, (size_t)5U * sizeof(Eurydice_arr_79));
  Eurydice_slice_copy(
      Eurydice_array_to_slice_mut_974(&s1_ntt),
      Eurydice_array_to_subslice_shared_520(
          &s1_s2,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end = LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A})),
      Eurydice_arr_79);
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_08(&s1_ntt.data[i0]);
  }
  libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      Eurydice_array_to_slice_shared_972(&a_as_ntt),
      Eurydice_array_to_slice_shared_973(&s1_ntt),
      Eurydice_array_to_slice_shared_974(&s1_s2),
      Eurydice_array_to_slice_mut_975(&t0));
  Eurydice_arr_10 t1;
  Eurydice_arr_79 repeat_expression[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression, (size_t)6U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
      Eurydice_array_to_slice_mut_975(&t0),
      Eurydice_array_to_slice_mut_975(&t1));
  libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
      seed_for_a, Eurydice_array_to_slice_shared_975(&t1), verification_key);
  libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = verification_key.ptr,
                                               .meta = verification_key.meta}),
      Eurydice_array_to_slice_shared_974(&s1_s2),
      Eurydice_array_to_slice_shared_975(&t0), signing_key);
}

/**
 Generate key pair.
*/
static inline void
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
    Eurydice_arr_60 randomness, Eurydice_arr_d10 *signing_key,
    Eurydice_arr_4a *verification_key) {
  libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_c4(
      randomness, Eurydice_array_to_slice_mut_ef(signing_key),
      Eurydice_array_to_slice_mut_5b(verification_key));
}

/**
 Generate an ML-DSA-65 Key Pair
*/
static inline libcrux_iot_ml_dsa_types_MLDSAKeyPair_06
libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair(
    Eurydice_arr_60 randomness) {
  Eurydice_arr_d10 signing_key = {.data = {0U}};
  Eurydice_arr_4a verification_key = {.data = {0U}};
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
      randomness, &signing_key, &verification_key);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSAKeyPair_06){
      .signing_key = libcrux_iot_ml_dsa_types_new_f8_09(signing_key),
      .verification_key =
          libcrux_iot_ml_dsa_types_new_e9_97(verification_key)});
}

/**
 Generate an ML-DSA-65 Key Pair
*/
static inline void libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair_mut(
    Eurydice_arr_60 randomness, Eurydice_arr_d10 *signing_key,
    Eurydice_arr_4a *verification_key) {
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
      randomness, signing_key, verification_key);
}

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
A monomorphic instance of core.option.Option
with types Eurydice_arr_5f

*/
typedef struct Option_a6_s {
  Option_b5_tags tag;
  Eurydice_arr_5f f0;
} Option_a6;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_b5

*/
typedef struct Option_cb_s {
  Option_b5_tags tag;
  Eurydice_arr_b5 f0;
} Option_cb;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature_8f,
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_74_s {
  Result_8e_tags tag;
  union {
    Eurydice_arr_96 case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} Result_74;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_1d

*/
typedef struct Option_c1_s {
  Option_b5_tags tag;
  Eurydice_arr_1d f0;
} Option_c1;

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
static KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 remaining_serialized0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_signing = uu____1.fst;
  Eurydice_borrow_slice_u8 remaining_serialized1 = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 verification_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 remaining_serialized2 = uu____2.snd;
  Eurydice_borrow_slice_u8_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s1_serialized = uu____3.fst;
  Eurydice_borrow_slice_u8 remaining_serialized = uu____3.snd;
  Eurydice_borrow_slice_u8_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s2_serialized = uu____4.fst;
  Eurydice_borrow_slice_u8 t0_serialized = uu____4.snd;
  Eurydice_arr_1d s1_as_ntt;
  Eurydice_arr_79 repeat_expression0[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_as_ntt.data, repeat_expression0,
         (size_t)5U * sizeof(Eurydice_arr_79));
  Eurydice_arr_10 s2_as_ntt;
  Eurydice_arr_79 repeat_expression1[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s2_as_ntt.data, repeat_expression1,
         (size_t)6U * sizeof(Eurydice_arr_79));
  Eurydice_arr_10 t0_as_ntt;
  Eurydice_arr_79 repeat_expression2[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0_as_ntt.data, repeat_expression2,
         (size_t)6U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      s1_serialized, Eurydice_array_to_slice_mut_974(&s1_as_ntt));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      s2_serialized, Eurydice_array_to_slice_mut_975(&s2_as_ntt));
  libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
      t0_serialized, Eurydice_array_to_slice_mut_975(&t0_as_ntt));
  Eurydice_arr_d2 matrix;
  Eurydice_arr_79 repeat_expression3[30U];
  for (size_t i = (size_t)0U; i < (size_t)30U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(matrix.data, repeat_expression3,
         (size_t)30U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice_mut_972(&matrix));
  Eurydice_arr_06 message_representative = {.data = {0U}};
  libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
      verification_key_hash, &domain_separation_context, message,
      &message_representative);
  Eurydice_arr_06 mask_seed = {.data = {0U}};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake0 =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake0,
                                                       seed_for_signing);
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake0, Eurydice_array_to_slice_shared_6e(&randomness));
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake0, Eurydice_array_to_slice_shared_d8(&message_representative));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake0, Eurydice_array_to_slice_mut_d8(&mask_seed));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  Option_a6 commitment_hash0 = {.tag = None};
  Option_c1 signer_response0 = {.tag = None};
  Option_cb hint0 = {.tag = None};
  while (attempt < LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    Eurydice_arr_1d mask;
    Eurydice_arr_79 repeat_expression4[5U];
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      repeat_expression4[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(mask.data, repeat_expression4, (size_t)5U * sizeof(Eurydice_arr_79));
    Eurydice_arr_10 w0;
    Eurydice_arr_79 repeat_expression5[6U];
    for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
      repeat_expression5[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(w0.data, repeat_expression5, (size_t)6U * sizeof(Eurydice_arr_79));
    Eurydice_arr_10 commitment;
    Eurydice_arr_79 repeat_expression6[6U];
    for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
      repeat_expression6[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(commitment.data, repeat_expression6,
           (size_t)6U * sizeof(Eurydice_arr_79));
    libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT, &mask_seed,
        &domain_separator_for_mask, Eurydice_array_to_slice_mut_974(&mask));
    Eurydice_arr_10 a_x_mask;
    Eurydice_arr_79 repeat_expression[6U];
    for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
      repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(a_x_mask.data, repeat_expression,
           (size_t)6U * sizeof(Eurydice_arr_79));
    Eurydice_arr_1d mask_ntt =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)5U, &mask, Eurydice_arr_79, Eurydice_arr_1d);
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      size_t i0 = i;
      libcrux_iot_ml_dsa_ntt_ntt_08(&mask_ntt.data[i0]);
    }
    libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        Eurydice_array_to_slice_shared_972(&matrix),
        Eurydice_array_to_slice_shared_973(&mask_ntt),
        Eurydice_array_to_slice_mut_975(&a_x_mask));
    libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
        Eurydice_array_to_slice_shared_975(&a_x_mask),
        Eurydice_array_to_slice_mut_975(&w0),
        Eurydice_array_to_slice_mut_975(&commitment));
    Eurydice_arr_5f commitment_hash_candidate = {.data = {0U}};
    Eurydice_arr_56 commitment_serialized = {.data = {0U}};
    libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
        LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE,
        Eurydice_array_to_slice_shared_975(&commitment),
        Eurydice_array_to_slice_mut_ee(&commitment_serialized));
    libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
        libcrux_iot_ml_dsa_hash_functions_portable_init_88();
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake, Eurydice_array_to_slice_shared_d8(&message_representative));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
        &shake, Eurydice_array_to_slice_shared_ee(&commitment_serialized));
    libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
        &shake, Eurydice_array_to_slice_mut_95(&commitment_hash_candidate));
    Eurydice_arr_79 verifier_challenge =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
        Eurydice_array_to_slice_shared_95(&commitment_hash_candidate),
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
    Eurydice_arr_1d challenge_times_s1 =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)5U, &s1_as_ntt, Eurydice_arr_79, Eurydice_arr_1d);
    Eurydice_arr_10 challenge_times_s2 =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)6U, &s2_as_ntt, Eurydice_arr_79, Eurydice_arr_10);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice_mut_974(&challenge_times_s1),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice_mut_975(&challenge_times_s2),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_add_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        Eurydice_array_to_slice_mut_974(&mask),
        Eurydice_array_to_slice_shared_973(&challenge_times_s1));
    libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        Eurydice_array_to_slice_mut_975(&w0),
        Eurydice_array_to_slice_shared_975(&challenge_times_s2));
    if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice_shared_973(&mask),
            ((int32_t)1 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
      if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
              Eurydice_array_to_slice_shared_975(&w0),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2 -
                  LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
        Eurydice_arr_10 challenge_times_t0 =
            core_array__core__clone__Clone_for__Array_T__N___clone(
                (size_t)6U, &t0_as_ntt, Eurydice_arr_79, Eurydice_arr_10);
        libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
            Eurydice_array_to_slice_mut_975(&challenge_times_t0),
            &verifier_challenge);
        if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
                Eurydice_array_to_slice_shared_975(&challenge_times_t0),
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2)) {
          libcrux_iot_ml_dsa_matrix_add_vectors_08(
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
              Eurydice_array_to_slice_mut_975(&w0),
              Eurydice_array_to_slice_shared_975(&challenge_times_t0));
          Eurydice_arr_b5 hint_candidate = {.data = {{.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}}}};
          size_t ones_in_hint = libcrux_iot_ml_dsa_arithmetic_make_hint_08(
              Eurydice_array_to_slice_shared_975(&w0),
              Eurydice_array_to_slice_shared_975(&commitment),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
              Eurydice_array_to_slice_mut_6d0(&hint_candidate));
          if (!(ones_in_hint >
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            commitment_hash0 = (KRML_CLITERAL(Option_a6){
                .tag = Some, .f0 = commitment_hash_candidate});
            signer_response0 =
                (KRML_CLITERAL(Option_c1){.tag = Some, .f0 = mask});
            hint0 =
                (KRML_CLITERAL(Option_cb){.tag = Some, .f0 = hint_candidate});
          }
        }
      }
    }
  }
  Result_87 uu____5;
  if (commitment_hash0.tag == None) {
    uu____5 = (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    Eurydice_arr_5f commitment_hash = commitment_hash0.f0;
    Eurydice_arr_5f commitment_hash1 = commitment_hash;
    if (signer_response0.tag == None) {
      uu____5 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      Eurydice_arr_1d signer_response = signer_response0.f0;
      Eurydice_arr_1d signer_response1 = signer_response;
      if (!(hint0.tag == None)) {
        Eurydice_arr_b5 hint = hint0.f0;
        Eurydice_arr_b5 hint1 = hint;
        libcrux_iot_ml_dsa_encoding_signature_serialize_08(
            Eurydice_array_to_slice_shared_95(&commitment_hash1),
            Eurydice_array_to_slice_shared_973(&signer_response1),
            Eurydice_array_to_slice_shared_6d0(&hint1),
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT,
            LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice_mut_ee0(signature));
        return (KRML_CLITERAL(Result_87){.tag = Ok});
      }
      uu____5 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____5;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
static KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_b5){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
      signing_key, message,
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      randomness, signature);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
static KRML_MUSTINLINE Result_74
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  Eurydice_arr_96 signature = libcrux_iot_ml_dsa_types_zero_ad_fa();
  Result_87 uu____0 = libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
      signing_key, message, context, randomness, &signature);
  Result_74 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_74){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_74){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign.
*/
static inline Result_74
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_c4(
      Eurydice_array_to_slice_shared_ef(signing_key), message, context,
      randomness);
}

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_74 libcrux_iot_ml_dsa_ml_dsa_65_portable_sign(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign(
      libcrux_iot_ml_dsa_types_as_ref_f8_09(signing_key), message, context,
      randomness);
}

/**
 Sign.
*/
static inline Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_mut(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
      Eurydice_array_to_slice_shared_ef(signing_key), message, context,
      randomness, signature);
}

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_87 libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_mut(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_mut(
      signing_key, message, context, randomness, signature);
}

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
static KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness,
    Eurydice_arr_96 *signature) {
  if (!(context.meta > LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
    Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
        context, (KRML_CLITERAL(Option_b5){
                     .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
    if (!(uu____0.tag == Ok)) {
      return (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc =
        uu____0.val.case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        domain_separation_context = dsc;
    return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
        signing_key,
        (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                                 .meta = pre_hash_buffer.meta}),
        (KRML_CLITERAL(Option_e3){.tag = Some,
                                  .f0 = domain_separation_context}),
        randomness, signature);
  }
  return (KRML_CLITERAL(Result_87){
      .tag = Err,
      .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
}

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
static KRML_MUSTINLINE Result_74
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness) {
  Eurydice_arr_96 signature = libcrux_iot_ml_dsa_types_zero_ad_fa();
  Result_87 uu____0 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_36(
          signing_key, message, context, pre_hash_buffer, randomness,
          &signature);
  Result_74 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_74){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_74){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign (pre-hashed).
*/
static inline Result_74
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_pre_hashed_shake128(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_36(
      Eurydice_array_to_slice_shared_ef(signing_key), message, context,
      pre_hash_buffer, randomness);
}

/**
 Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_74
libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_d10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  Eurydice_arr_60 pre_hash_buffer = {.data = {0U}};
  const Eurydice_arr_d10 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_f8_09(signing_key);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_pre_hashed_shake128(
      uu____0, message, context,
      Eurydice_array_to_slice_mut_6e(&pre_hash_buffer), randomness);
}

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
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_96 *signature_serialized) {
  Eurydice_arr_12 rand_stack = {.data = {0U}};
  Eurydice_arr_27 rand_block = {.data = {0U}};
  Eurydice_arr_13 tmp_stack = {.data = {0U}};
  Eurydice_arr_79 poly_slot = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_5b(verification_key),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 t1_serialized = uu____0.snd;
  Eurydice_arr_10 t1;
  Eurydice_arr_79 repeat_expression0[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression0, (size_t)6U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_VERIFICATION_KEY_SIZE,
      t1_serialized, Eurydice_array_to_slice_mut_975(&t1));
  Eurydice_arr_5f deserialized_commitment_hash = {.data = {0U}};
  Eurydice_arr_1d deserialized_signer_response;
  Eurydice_arr_79 repeat_expression[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(deserialized_signer_response.data, repeat_expression,
         (size_t)5U * sizeof(Eurydice_arr_79));
  Eurydice_arr_b5 deserialized_hint = {.data = {{.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}}}};
  Result_5c uu____1 = libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNATURE_SIZE,
      Eurydice_array_to_slice_shared_ee0(signature_serialized),
      Eurydice_array_to_slice_mut_95(&deserialized_commitment_hash),
      Eurydice_array_to_slice_mut_974(&deserialized_signer_response),
      Eurydice_array_to_slice_mut_6d0(&deserialized_hint));
  Result_5c uu____2;
  if (uu____1.tag == Ok) {
    if (libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice_shared_973(&deserialized_signer_response),
            ((int32_t)2 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
      uu____2 = (KRML_CLITERAL(Result_5c){
          .tag = Err,
          .f0 =
              libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      Eurydice_arr_06 verification_key_hash = {.data = {0U}};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
          Eurydice_array_to_slice_shared_5b(verification_key),
          &verification_key_hash);
      Eurydice_arr_06 message_representative = {.data = {0U}};
      libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
          Eurydice_array_to_slice_shared_d8(&verification_key_hash),
          &domain_separation_context, message, &message_representative);
      Eurydice_arr_79 verifier_challenge =
          libcrux_iot_ml_dsa_polynomial_zero_c2_08();
      libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
          Eurydice_array_to_slice_shared_95(&deserialized_commitment_hash),
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
      for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
        size_t i0 = i;
        libcrux_iot_ml_dsa_ntt_ntt_08(&deserialized_signer_response.data[i0]);
      }
      libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
          &rand_stack, &rand_block, &tmp_stack, &poly_slot,
          Eurydice_array_to_slice_shared_973(&deserialized_signer_response),
          &verifier_challenge, Eurydice_array_to_slice_mut_975(&t1));
      Eurydice_arr_5f recomputed_commitment_hash = {.data = {0U}};
      libcrux_iot_ml_dsa_arithmetic_use_hint_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
          Eurydice_array_to_slice_shared_6d0(&deserialized_hint),
          Eurydice_array_to_slice_mut_975(&t1));
      Eurydice_arr_56 commitment_serialized = {.data = {0U}};
      libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE,
          Eurydice_array_to_slice_shared_975(&t1),
          Eurydice_array_to_slice_mut_ee(&commitment_serialized));
      libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
          libcrux_iot_ml_dsa_hash_functions_portable_init_88();
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice_shared_d8(&message_representative));
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
          &shake, Eurydice_array_to_slice_shared_ee(&commitment_serialized));
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
          &shake, Eurydice_array_to_slice_mut_95(&recomputed_commitment_hash));
      if (Eurydice_array_eq((size_t)48U, &deserialized_commitment_hash,
                            &recomputed_commitment_hash, uint8_t)) {
        uu____2 = (KRML_CLITERAL(Result_5c){.tag = Ok});
      } else {
        uu____2 = (KRML_CLITERAL(Result_5c){
            .tag = Err,
            .f0 =
                libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_iot_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 = (KRML_CLITERAL(Result_5c){.tag = Err, .f0 = e});
  }
  return uu____2;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_c4(
    const Eurydice_arr_4a *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_96 *signature_serialized) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_b5){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
      verification_key_serialized, message,
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify.
*/
static inline Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_96 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_c4(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_5c libcrux_iot_ml_dsa_ml_dsa_65_portable_verify(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_96 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify(
      libcrux_iot_ml_dsa_types_as_ref_e9_97(verification_key), message, context,
      libcrux_iot_ml_dsa_types_as_ref_ad_fa(signature));
}

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
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_36(
    const Eurydice_arr_4a *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_96 *signature_serialized) {
  libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_b5){
                   .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
      verification_key_serialized,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                               .meta = pre_hash_buffer.meta}),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
static inline Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify_pre_hashed_shake128(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_96 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_36(
      verification_key, message, context, pre_hash_buffer, signature);
}

/**
 Verify a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_5c
libcrux_iot_ml_dsa_ml_dsa_65_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_4a *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_96 *signature) {
  Eurydice_arr_60 pre_hash_buffer = {.data = {0U}};
  const Eurydice_arr_4a *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_e9_97(verification_key);
  Eurydice_borrow_slice_u8 uu____1 = message;
  Eurydice_borrow_slice_u8 uu____2 = context;
  Eurydice_mut_borrow_slice_u8 uu____3 =
      Eurydice_array_to_slice_mut_6e(&pre_hash_buffer);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3,
      libcrux_iot_ml_dsa_types_as_ref_ad_fa(signature));
}

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_ERROR_COEFFICIENT))

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $56size_t
*/
typedef struct Eurydice_arr_1c_s {
  Eurydice_arr_79 data[56U];
} Eurydice_arr_1c;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 56
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_976(
    Eurydice_arr_1c *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)56U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $15size_t
*/
typedef struct Eurydice_arr_28_s {
  Eurydice_arr_79 data[15U];
} Eurydice_arr_28;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 15
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_977(
    Eurydice_arr_28 *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)15U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $7size_t
*/
typedef struct Eurydice_arr_09_s {
  Eurydice_arr_79 data[7U];
} Eurydice_arr_09;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 7
*/
static inline Eurydice_dst_ref_mut_32 Eurydice_array_to_slice_mut_978(
    Eurydice_arr_09 *a) {
  Eurydice_dst_ref_mut_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)7U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients, core_ops_range_Range
size_t, Eurydice_derefed_slice
libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 15
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_subslice_shared_521(
    const Eurydice_arr_28 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_32){.ptr = a->data + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 56
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_976(
    const Eurydice_arr_1c *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)56U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 7
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_977(
    const Eurydice_arr_09 *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)7U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 15
*/
static inline Eurydice_dst_ref_shared_32 Eurydice_array_to_slice_shared_978(
    const Eurydice_arr_28 *a) {
  Eurydice_dst_ref_shared_32 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)15U;
  return lit;
}

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
static KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_generate_key_pair_c4(
    Eurydice_arr_60 randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key) {
  Eurydice_arr_d1 seed_expanded0 = {.data = {0U}};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice_shared_6e(&randomness));
  /* original Rust expression is not an lvalue in C */
  Eurydice_array_u8x2 lvalue = {
      .data = {(uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
               (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A}};
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, Eurydice_array_to_slice_shared_26(&lvalue));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_18(&seed_expanded0));
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_18(&seed_expanded0),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 seed_expanded = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_error_vectors = uu____1.fst;
  Eurydice_borrow_slice_u8 seed_for_signing = uu____1.snd;
  Eurydice_arr_1c a_as_ntt;
  Eurydice_arr_79 repeat_expression0[56U];
  for (size_t i = (size_t)0U; i < (size_t)56U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(a_as_ntt.data, repeat_expression0,
         (size_t)56U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice_mut_976(&a_as_ntt));
  Eurydice_arr_28 s1_s2;
  Eurydice_arr_79 repeat_expression1[15U];
  for (size_t i = (size_t)0U; i < (size_t)15U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_s2.data, repeat_expression1, (size_t)15U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA, seed_for_error_vectors,
      Eurydice_array_to_slice_mut_977(&s1_s2));
  Eurydice_arr_a5 t0;
  Eurydice_arr_79 repeat_expression2[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0.data, repeat_expression2, (size_t)8U * sizeof(Eurydice_arr_79));
  Eurydice_arr_09 s1_ntt;
  Eurydice_arr_79 repeat_expression3[7U];
  for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_ntt.data, repeat_expression3, (size_t)7U * sizeof(Eurydice_arr_79));
  Eurydice_slice_copy(
      Eurydice_array_to_slice_mut_978(&s1_ntt),
      Eurydice_array_to_subslice_shared_521(
          &s1_s2,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end = LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A})),
      Eurydice_arr_79);
  for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_08(&s1_ntt.data[i0]);
  }
  libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
      Eurydice_array_to_slice_shared_976(&a_as_ntt),
      Eurydice_array_to_slice_shared_977(&s1_ntt),
      Eurydice_array_to_slice_shared_978(&s1_s2),
      Eurydice_array_to_slice_mut_970(&t0));
  Eurydice_arr_a5 t1;
  Eurydice_arr_79 repeat_expression[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression, (size_t)8U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
      Eurydice_array_to_slice_mut_970(&t0),
      Eurydice_array_to_slice_mut_970(&t1));
  libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
      seed_for_a, Eurydice_array_to_slice_shared_971(&t1), verification_key);
  libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = verification_key.ptr,
                                               .meta = verification_key.meta}),
      Eurydice_array_to_slice_shared_978(&s1_s2),
      Eurydice_array_to_slice_shared_971(&t0), signing_key);
}

/**
 Generate key pair.
*/
static inline void
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_generate_key_pair(
    Eurydice_arr_60 randomness, Eurydice_arr_180 *signing_key,
    Eurydice_arr_51 *verification_key) {
  libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_generate_key_pair_c4(
      randomness, Eurydice_array_to_slice_mut_e2(signing_key),
      Eurydice_array_to_slice_mut_f70(verification_key));
}

/**
 Generate an ML-DSA-87 Key Pair
*/
static inline libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d
libcrux_iot_ml_dsa_ml_dsa_87_portable_generate_key_pair(
    Eurydice_arr_60 randomness) {
  Eurydice_arr_180 signing_key = {.data = {0U}};
  Eurydice_arr_51 verification_key = {.data = {0U}};
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_generate_key_pair(
      randomness, &signing_key, &verification_key);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d){
      .signing_key = libcrux_iot_ml_dsa_types_new_f8_32(signing_key),
      .verification_key =
          libcrux_iot_ml_dsa_types_new_e9_d8(verification_key)});
}

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
A monomorphic instance of core.option.Option
with types Eurydice_arr_06

*/
typedef struct Option_7a_s {
  Option_b5_tags tag;
  Eurydice_arr_06 f0;
} Option_7a;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_fb

*/
typedef struct Option_b9_s {
  Option_b5_tags tag;
  Eurydice_arr_fb f0;
} Option_b9;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature_9b,
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_79_s {
  Result_8e_tags tag;
  union {
    Eurydice_arr_380 case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} Result_79;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_09

*/
typedef struct Option_b3_s {
  Option_b5_tags tag;
  Eurydice_arr_09 f0;
} Option_b3;

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
static KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_60 randomness,
    Eurydice_arr_380 *signature) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 remaining_serialized0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_signing = uu____1.fst;
  Eurydice_borrow_slice_u8 remaining_serialized1 = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 verification_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 remaining_serialized2 = uu____2.snd;
  Eurydice_borrow_slice_u8_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s1_serialized = uu____3.fst;
  Eurydice_borrow_slice_u8 remaining_serialized = uu____3.snd;
  Eurydice_borrow_slice_u8_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s2_serialized = uu____4.fst;
  Eurydice_borrow_slice_u8 t0_serialized = uu____4.snd;
  Eurydice_arr_09 s1_as_ntt;
  Eurydice_arr_79 repeat_expression0[7U];
  for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_as_ntt.data, repeat_expression0,
         (size_t)7U * sizeof(Eurydice_arr_79));
  Eurydice_arr_a5 s2_as_ntt;
  Eurydice_arr_79 repeat_expression1[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s2_as_ntt.data, repeat_expression1,
         (size_t)8U * sizeof(Eurydice_arr_79));
  Eurydice_arr_a5 t0_as_ntt;
  Eurydice_arr_79 repeat_expression2[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0_as_ntt.data, repeat_expression2,
         (size_t)8U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE,
      s1_serialized, Eurydice_array_to_slice_mut_978(&s1_as_ntt));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE,
      s2_serialized, Eurydice_array_to_slice_mut_970(&s2_as_ntt));
  libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
      t0_serialized, Eurydice_array_to_slice_mut_970(&t0_as_ntt));
  Eurydice_arr_1c matrix;
  Eurydice_arr_79 repeat_expression3[56U];
  for (size_t i = (size_t)0U; i < (size_t)56U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(matrix.data, repeat_expression3,
         (size_t)56U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice_mut_976(&matrix));
  Eurydice_arr_06 message_representative = {.data = {0U}};
  libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
      verification_key_hash, &domain_separation_context, message,
      &message_representative);
  Eurydice_arr_06 mask_seed = {.data = {0U}};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake0 =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake0,
                                                       seed_for_signing);
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake0, Eurydice_array_to_slice_shared_6e(&randomness));
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake0, Eurydice_array_to_slice_shared_d8(&message_representative));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake0, Eurydice_array_to_slice_mut_d8(&mask_seed));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  Option_7a commitment_hash0 = {.tag = None};
  Option_b3 signer_response0 = {.tag = None};
  Option_b9 hint0 = {.tag = None};
  while (attempt < LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    Eurydice_arr_09 mask;
    Eurydice_arr_79 repeat_expression4[7U];
    for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
      repeat_expression4[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(mask.data, repeat_expression4, (size_t)7U * sizeof(Eurydice_arr_79));
    Eurydice_arr_a5 w0;
    Eurydice_arr_79 repeat_expression5[8U];
    for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
      repeat_expression5[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(w0.data, repeat_expression5, (size_t)8U * sizeof(Eurydice_arr_79));
    Eurydice_arr_a5 commitment;
    Eurydice_arr_79 repeat_expression6[8U];
    for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
      repeat_expression6[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(commitment.data, repeat_expression6,
           (size_t)8U * sizeof(Eurydice_arr_79));
    libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT, &mask_seed,
        &domain_separator_for_mask, Eurydice_array_to_slice_mut_978(&mask));
    Eurydice_arr_a5 a_x_mask;
    Eurydice_arr_79 repeat_expression[8U];
    for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
      repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(a_x_mask.data, repeat_expression,
           (size_t)8U * sizeof(Eurydice_arr_79));
    Eurydice_arr_09 mask_ntt =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)7U, &mask, Eurydice_arr_79, Eurydice_arr_09);
    for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
      size_t i0 = i;
      libcrux_iot_ml_dsa_ntt_ntt_08(&mask_ntt.data[i0]);
    }
    libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
        Eurydice_array_to_slice_shared_976(&matrix),
        Eurydice_array_to_slice_shared_977(&mask_ntt),
        Eurydice_array_to_slice_mut_970(&a_x_mask));
    libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2,
        Eurydice_array_to_slice_shared_971(&a_x_mask),
        Eurydice_array_to_slice_mut_970(&w0),
        Eurydice_array_to_slice_mut_970(&commitment));
    Eurydice_arr_06 commitment_hash_candidate = {.data = {0U}};
    Eurydice_arr_9e commitment_serialized = {.data = {0U}};
    libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
        LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_RING_ELEMENT_SIZE,
        Eurydice_array_to_slice_shared_971(&commitment),
        Eurydice_array_to_slice_mut_fd(&commitment_serialized));
    libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
        libcrux_iot_ml_dsa_hash_functions_portable_init_88();
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake, Eurydice_array_to_slice_shared_d8(&message_representative));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
        &shake, Eurydice_array_to_slice_shared_fd(&commitment_serialized));
    libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
        &shake, Eurydice_array_to_slice_mut_d8(&commitment_hash_candidate));
    Eurydice_arr_79 verifier_challenge =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
        Eurydice_array_to_slice_shared_d8(&commitment_hash_candidate),
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
    Eurydice_arr_09 challenge_times_s1 =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)7U, &s1_as_ntt, Eurydice_arr_79, Eurydice_arr_09);
    Eurydice_arr_a5 challenge_times_s2 =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)8U, &s2_as_ntt, Eurydice_arr_79, Eurydice_arr_a5);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice_mut_978(&challenge_times_s1),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice_mut_970(&challenge_times_s2),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_add_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
        Eurydice_array_to_slice_mut_978(&mask),
        Eurydice_array_to_slice_shared_977(&challenge_times_s1));
    libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
        Eurydice_array_to_slice_mut_970(&w0),
        Eurydice_array_to_slice_shared_971(&challenge_times_s2));
    if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice_shared_977(&mask),
            ((int32_t)1 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA)) {
      if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
              Eurydice_array_to_slice_shared_971(&w0),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2 -
                  LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA)) {
        Eurydice_arr_a5 challenge_times_t0 =
            core_array__core__clone__Clone_for__Array_T__N___clone(
                (size_t)8U, &t0_as_ntt, Eurydice_arr_79, Eurydice_arr_a5);
        libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
            Eurydice_array_to_slice_mut_970(&challenge_times_t0),
            &verifier_challenge);
        if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
                Eurydice_array_to_slice_shared_971(&challenge_times_t0),
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2)) {
          libcrux_iot_ml_dsa_matrix_add_vectors_08(
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
              Eurydice_array_to_slice_mut_970(&w0),
              Eurydice_array_to_slice_shared_971(&challenge_times_t0));
          Eurydice_arr_fb hint_candidate = {.data = {{.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}}}};
          size_t ones_in_hint = libcrux_iot_ml_dsa_arithmetic_make_hint_08(
              Eurydice_array_to_slice_shared_971(&w0),
              Eurydice_array_to_slice_shared_971(&commitment),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2,
              Eurydice_array_to_slice_mut_6d1(&hint_candidate));
          if (!(ones_in_hint >
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            commitment_hash0 = (KRML_CLITERAL(Option_7a){
                .tag = Some, .f0 = commitment_hash_candidate});
            signer_response0 =
                (KRML_CLITERAL(Option_b3){.tag = Some, .f0 = mask});
            hint0 =
                (KRML_CLITERAL(Option_b9){.tag = Some, .f0 = hint_candidate});
          }
        }
      }
    }
  }
  Result_87 uu____5;
  if (commitment_hash0.tag == None) {
    uu____5 = (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    Eurydice_arr_06 commitment_hash = commitment_hash0.f0;
    Eurydice_arr_06 commitment_hash1 = commitment_hash;
    if (signer_response0.tag == None) {
      uu____5 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      Eurydice_arr_09 signer_response = signer_response0.f0;
      Eurydice_arr_09 signer_response1 = signer_response;
      if (!(hint0.tag == None)) {
        Eurydice_arr_fb hint = hint0.f0;
        Eurydice_arr_fb hint1 = hint;
        libcrux_iot_ml_dsa_encoding_signature_serialize_08(
            Eurydice_array_to_slice_shared_d8(&commitment_hash1),
            Eurydice_array_to_slice_shared_977(&signer_response1),
            Eurydice_array_to_slice_shared_6d1(&hint1),
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT,
            LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice_mut_24(signature));
        return (KRML_CLITERAL(Result_87){.tag = Ok});
      }
      uu____5 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____5;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
static KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_380 *signature) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_b5){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
      signing_key, message,
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      randomness, signature);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
static KRML_MUSTINLINE Result_79
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  Eurydice_arr_380 signature = libcrux_iot_ml_dsa_types_zero_ad_c2();
  Result_87 uu____0 = libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
      signing_key, message, context, randomness, &signature);
  Result_79 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_79){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_79){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign.
*/
static inline Result_79
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_c4(
      Eurydice_array_to_slice_shared_e2(signing_key), message, context,
      randomness);
}

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_79 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign(
      libcrux_iot_ml_dsa_types_as_ref_f8_32(signing_key), message, context,
      randomness);
}

/**
 Sign.
*/
static inline Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_mut(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_380 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
      Eurydice_array_to_slice_shared_e2(signing_key), message, context,
      randomness, signature);
}

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_87 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_mut(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness,
    Eurydice_arr_380 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_mut(
      libcrux_iot_ml_dsa_types_as_ref_f8_32(signing_key), message, context,
      randomness, signature);
}

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
static KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness,
    Eurydice_arr_380 *signature) {
  if (!(context.meta > LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
    Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
        context, (KRML_CLITERAL(Option_b5){
                     .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
    if (!(uu____0.tag == Ok)) {
      return (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc =
        uu____0.val.case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        domain_separation_context = dsc;
    return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
        signing_key,
        (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                                 .meta = pre_hash_buffer.meta}),
        (KRML_CLITERAL(Option_e3){.tag = Some,
                                  .f0 = domain_separation_context}),
        randomness, signature);
  }
  return (KRML_CLITERAL(Result_87){
      .tag = Err,
      .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
}

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
static KRML_MUSTINLINE Result_79
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness) {
  Eurydice_arr_380 signature = libcrux_iot_ml_dsa_types_zero_ad_c2();
  Result_87 uu____0 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_mut_36(
          signing_key, message, context, pre_hash_buffer, randomness,
          &signature);
  Result_79 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_79){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_79){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign (pre-hashed).
*/
static inline Result_79
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_pre_hashed_shake128(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_60 randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_36(
      Eurydice_array_to_slice_shared_e2(signing_key), message, context,
      pre_hash_buffer, randomness);
}

/**
 Generate a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_79
libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_180 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_60 randomness) {
  Eurydice_arr_60 pre_hash_buffer = {.data = {0U}};
  const Eurydice_arr_180 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_f8_32(signing_key);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_pre_hashed_shake128(
      uu____0, message, context,
      Eurydice_array_to_slice_mut_6e(&pre_hash_buffer), randomness);
}

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
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
    const Eurydice_arr_51 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_380 *signature_serialized) {
  Eurydice_arr_12 rand_stack = {.data = {0U}};
  Eurydice_arr_27 rand_block = {.data = {0U}};
  Eurydice_arr_13 tmp_stack = {.data = {0U}};
  Eurydice_arr_79 poly_slot = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_f70(verification_key),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 t1_serialized = uu____0.snd;
  Eurydice_arr_a5 t1;
  Eurydice_arr_79 repeat_expression0[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression0, (size_t)8U * sizeof(Eurydice_arr_79));
  libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_VERIFICATION_KEY_SIZE,
      t1_serialized, Eurydice_array_to_slice_mut_970(&t1));
  Eurydice_arr_06 deserialized_commitment_hash = {.data = {0U}};
  Eurydice_arr_09 deserialized_signer_response;
  Eurydice_arr_79 repeat_expression[7U];
  for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(deserialized_signer_response.data, repeat_expression,
         (size_t)7U * sizeof(Eurydice_arr_79));
  Eurydice_arr_fb deserialized_hint = {.data = {{.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}}}};
  Result_5c uu____1 = libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_GAMMA1_RING_ELEMENT_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_SIGNATURE_SIZE,
      Eurydice_array_to_slice_shared_24(signature_serialized),
      Eurydice_array_to_slice_mut_d8(&deserialized_commitment_hash),
      Eurydice_array_to_slice_mut_978(&deserialized_signer_response),
      Eurydice_array_to_slice_mut_6d1(&deserialized_hint));
  Result_5c uu____2;
  if (uu____1.tag == Ok) {
    if (libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice_shared_977(&deserialized_signer_response),
            ((int32_t)2 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA)) {
      uu____2 = (KRML_CLITERAL(Result_5c){
          .tag = Err,
          .f0 =
              libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      Eurydice_arr_06 verification_key_hash = {.data = {0U}};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
          Eurydice_array_to_slice_shared_f70(verification_key),
          &verification_key_hash);
      Eurydice_arr_06 message_representative = {.data = {0U}};
      libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
          Eurydice_array_to_slice_shared_d8(&verification_key_hash),
          &domain_separation_context, message, &message_representative);
      Eurydice_arr_79 verifier_challenge =
          libcrux_iot_ml_dsa_polynomial_zero_c2_08();
      libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
          Eurydice_array_to_slice_shared_d8(&deserialized_commitment_hash),
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
      for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
        size_t i0 = i;
        libcrux_iot_ml_dsa_ntt_ntt_08(&deserialized_signer_response.data[i0]);
      }
      libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A, seed_for_a,
          &rand_stack, &rand_block, &tmp_stack, &poly_slot,
          Eurydice_array_to_slice_shared_977(&deserialized_signer_response),
          &verifier_challenge, Eurydice_array_to_slice_mut_970(&t1));
      Eurydice_arr_06 recomputed_commitment_hash = {.data = {0U}};
      libcrux_iot_ml_dsa_arithmetic_use_hint_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2,
          Eurydice_array_to_slice_shared_6d1(&deserialized_hint),
          Eurydice_array_to_slice_mut_970(&t1));
      Eurydice_arr_9e commitment_serialized = {.data = {0U}};
      libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_RING_ELEMENT_SIZE,
          Eurydice_array_to_slice_shared_971(&t1),
          Eurydice_array_to_slice_mut_fd(&commitment_serialized));
      libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
          libcrux_iot_ml_dsa_hash_functions_portable_init_88();
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice_shared_d8(&message_representative));
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
          &shake, Eurydice_array_to_slice_shared_fd(&commitment_serialized));
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
          &shake, Eurydice_array_to_slice_mut_d8(&recomputed_commitment_hash));
      if (Eurydice_array_eq((size_t)64U, &deserialized_commitment_hash,
                            &recomputed_commitment_hash, uint8_t)) {
        uu____2 = (KRML_CLITERAL(Result_5c){.tag = Ok});
      } else {
        uu____2 = (KRML_CLITERAL(Result_5c){
            .tag = Err,
            .f0 =
                libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_iot_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 = (KRML_CLITERAL(Result_5c){.tag = Err, .f0 = e});
  }
  return uu____2;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_c4(
    const Eurydice_arr_51 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_380 *signature_serialized) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_b5){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
      verification_key_serialized, message,
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify.
*/
static inline Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify(
    const Eurydice_arr_51 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_380 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_c4(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_5c libcrux_iot_ml_dsa_ml_dsa_87_portable_verify(
    const Eurydice_arr_51 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_380 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify(
      libcrux_iot_ml_dsa_types_as_ref_e9_d8(verification_key), message, context,
      libcrux_iot_ml_dsa_types_as_ref_ad_c2(signature));
}

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
static KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_pre_hashed_36(
    const Eurydice_arr_51 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_380 *signature_serialized) {
  libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_b5){
                   .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
      verification_key_serialized,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                               .meta = pre_hash_buffer.meta}),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
static inline Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify_pre_hashed_shake128(
    const Eurydice_arr_51 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_380 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_pre_hashed_36(
      verification_key, message, context, pre_hash_buffer, signature);
}

/**
 Verify a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_5c
libcrux_iot_ml_dsa_ml_dsa_87_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_51 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_380 *signature) {
  Eurydice_arr_60 pre_hash_buffer = {.data = {0U}};
  const Eurydice_arr_51 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_e9_d8(verification_key);
  Eurydice_borrow_slice_u8 uu____1 = message;
  Eurydice_borrow_slice_u8 uu____2 = context;
  Eurydice_mut_borrow_slice_u8 uu____3 =
      Eurydice_array_to_slice_mut_6e(&pre_hash_buffer);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3,
      libcrux_iot_ml_dsa_types_as_ref_ad_c2(signature));
}

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

typedef Eurydice_arr_380
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87Signature;

typedef Eurydice_arr_180
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87SigningKey;

typedef Eurydice_arr_51
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

typedef Result_80 libcrux_iot_ml_dsa_pre_hash_PreHashResult;

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::SigningError}
*/
static inline libcrux_iot_ml_dsa_types_SigningError
libcrux_iot_ml_dsa_pre_hash_from_49(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e) {
  return libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError;
}

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::VerificationError}
*/
static inline libcrux_iot_ml_dsa_types_VerificationError
libcrux_iot_ml_dsa_pre_hash_from_97(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e) {
  return libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError;
}

typedef int32_t libcrux_iot_ml_dsa_simd_portable_vector_type_FieldElement;

typedef int32_t libcrux_iot_ml_dsa_simd_traits_FieldElementTimesMontgomeryR;

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_mldsa65_portable_H_DEFINED
#endif /* libcrux_iot_mldsa65_portable_H */
