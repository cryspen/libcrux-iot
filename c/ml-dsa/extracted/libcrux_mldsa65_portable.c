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

#include "libcrux_mldsa65_portable.h"

#include "internal/libcrux_core.h"
#include "internal/libcrux_iot_sha3.h"
#include "libcrux_core.h"
#include "libcrux_iot_sha3.h"

int32_t libcrux_iot_ml_dsa_constants_beta(
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

size_t libcrux_iot_ml_dsa_constants_commitment_ring_element_size(
    size_t bits_per_commitment_coefficient) {
  return bits_per_commitment_coefficient *
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

size_t libcrux_iot_ml_dsa_constants_commitment_vector_size(
    size_t bits_per_commitment_coefficient, size_t rows_in_a) {
  return libcrux_iot_ml_dsa_constants_commitment_ring_element_size(
             bits_per_commitment_coefficient) *
         rows_in_a;
}

size_t libcrux_iot_ml_dsa_constants_error_ring_element_size(
    size_t bits_per_error_coefficient) {
  return bits_per_error_coefficient *
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

size_t libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(
    size_t bits_per_gamma1_coefficient) {
  return bits_per_gamma1_coefficient *
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

size_t libcrux_iot_ml_dsa_constants_signature_size(
    size_t rows_in_a, size_t columns_in_a, size_t max_ones_in_hint,
    size_t commitment_hash_size, size_t bits_per_gamma1_coefficient) {
  return commitment_hash_size +
         columns_in_a * libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(
                            bits_per_gamma1_coefficient) +
         max_ones_in_hint + rows_in_a;
}

size_t libcrux_iot_ml_dsa_constants_signing_key_size(
    size_t rows_in_a, size_t columns_in_a, size_t error_ring_element_size) {
  return LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
         LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE +
         LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH +
         (rows_in_a + columns_in_a) * error_ring_element_size +
         rows_in_a * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
}

size_t libcrux_iot_ml_dsa_constants_verification_key_size(size_t rows_in_a) {
  return LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * rows_in_a *
             (LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH -
              LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) /
             (size_t)8U;
}

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_dsa::constants::Eta}
*/
inline libcrux_iot_ml_dsa_constants_Eta libcrux_iot_ml_dsa_constants_clone_44(
    libcrux_iot_ml_dsa_constants_Eta *self) {
  return self[0U];
}

KRML_MUSTINLINE size_t libcrux_iot_ml_dsa_encoding_error_chunk_size(
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

KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_signature_set_hint(
    Eurydice_slice out_hint, size_t i, size_t j) {
  Eurydice_slice_index(out_hint, i, int32_t[256U], int32_t(*)[256U])[j] =
      (int32_t)1;
}

KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
    Eurydice_slice input) {
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_sha3_portable_incremental_shake256_init();
  libcrux_iot_sha3_portable_incremental_shake256_absorb_final(&state, input);
  return state;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake128(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_iot_sha3_portable_shake128(out, input);
}

KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_x4(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3) {
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

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state, uint8_t *out0,
    uint8_t *out1, uint8_t *out2, uint8_t *out3) {
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state0, Eurydice_array_to_slice((size_t)840U, out0, uint8_t));
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state1, Eurydice_array_to_slice((size_t)840U, out1, uint8_t));
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state2, Eurydice_array_to_slice((size_t)840U, out2, uint8_t));
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state3, Eurydice_array_to_slice((size_t)840U, out3, uint8_t));
}

KRML_MUSTINLINE uint8_t_168size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state) {
  uint8_t out0[168U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state0, Eurydice_array_to_slice((size_t)168U, out0, uint8_t));
  uint8_t out1[168U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state1, Eurydice_array_to_slice((size_t)168U, out1, uint8_t));
  uint8_t out2[168U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state2, Eurydice_array_to_slice((size_t)168U, out2, uint8_t));
  uint8_t out3[168U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state3, Eurydice_array_to_slice((size_t)168U, out3, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[168U];
  memcpy(copy_of_out0, out0, (size_t)168U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[168U];
  memcpy(copy_of_out1, out1, (size_t)168U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[168U];
  memcpy(copy_of_out2, out2, (size_t)168U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out3[168U];
  memcpy(copy_of_out3, out3, (size_t)168U * sizeof(uint8_t));
  uint8_t_168size_t__x4 lit;
  memcpy(lit.fst, copy_of_out0, (size_t)168U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_out1, (size_t)168U * sizeof(uint8_t));
  memcpy(lit.thd, copy_of_out2, (size_t)168U * sizeof(uint8_t));
  memcpy(lit.f3, copy_of_out3, (size_t)168U * sizeof(uint8_t));
  return lit;
}

KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_init_absorb_x4(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3) {
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

KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_first_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state) {
  uint8_t out0[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state0, Eurydice_array_to_slice((size_t)136U, out0, uint8_t));
  uint8_t out1[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state1, Eurydice_array_to_slice((size_t)136U, out1, uint8_t));
  uint8_t out2[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state2, Eurydice_array_to_slice((size_t)136U, out2, uint8_t));
  uint8_t out3[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state3, Eurydice_array_to_slice((size_t)136U, out3, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[136U];
  memcpy(copy_of_out0, out0, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[136U];
  memcpy(copy_of_out1, out1, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[136U];
  memcpy(copy_of_out2, out2, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out3[136U];
  memcpy(copy_of_out3, out3, (size_t)136U * sizeof(uint8_t));
  uint8_t_136size_t__x4 lit;
  memcpy(lit.fst, copy_of_out0, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_out1, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.thd, copy_of_out2, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.f3, copy_of_out3, (size_t)136U * sizeof(uint8_t));
  return lit;
}

KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state) {
  uint8_t out0[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state0, Eurydice_array_to_slice((size_t)136U, out0, uint8_t));
  uint8_t out1[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state1, Eurydice_array_to_slice((size_t)136U, out1, uint8_t));
  uint8_t out2[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state2, Eurydice_array_to_slice((size_t)136U, out2, uint8_t));
  uint8_t out3[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state3, Eurydice_array_to_slice((size_t)136U, out3, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[136U];
  memcpy(copy_of_out0, out0, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[136U];
  memcpy(copy_of_out1, out1, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[136U];
  memcpy(copy_of_out2, out2, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out3[136U];
  memcpy(copy_of_out3, out3, (size_t)136U * sizeof(uint8_t));
  uint8_t_136size_t__x4 lit;
  memcpy(lit.fst, copy_of_out0, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_out1, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.thd, copy_of_out2, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.f3, copy_of_out3, (size_t)136U * sizeof(uint8_t));
  return lit;
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state, uint8_t ret[136U]) {
  uint8_t out[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
      state, Eurydice_array_to_slice((size_t)136U, out, uint8_t));
  memcpy(ret, out, (size_t)136U * sizeof(uint8_t));
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state, uint8_t ret[136U]) {
  uint8_t out[136U] = {0U};
  libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
      state, Eurydice_array_to_slice((size_t)136U, out, uint8_t));
  memcpy(ret, out, (size_t)136U * sizeof(uint8_t));
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_b5(
    Eurydice_slice input) {
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_sha3_portable_incremental_shake128_init();
  libcrux_iot_sha3_portable_incremental_shake128_absorb_final(&state, input);
  return state;
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_b5(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *out) {
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      self, Eurydice_array_to_slice((size_t)840U, out, uint8_t));
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_b5(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *out) {
  libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
      self, Eurydice_array_to_slice((size_t)168U, out, uint8_t));
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake128_e2(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake128(input, out);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_33(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_x4(
      input0, input1, input2, input3);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self, uint8_t *out0,
    uint8_t *out1, uint8_t *out2, uint8_t *out3) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_x4(
      self, out0, out1, out2, out3);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
KRML_MUSTINLINE uint8_t_168size_t__x4
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
KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_a1(
    Eurydice_slice input) {
  return libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
      input);
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_a1(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t ret[136U]) {
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(self,
                                                                          ret);
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_a1(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t ret[136U]) {
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(self,
                                                                         ret);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice input) {
  libcrux_iot_sha3_portable_incremental_absorb_a5(self, input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice input) {
  libcrux_iot_sha3_portable_incremental_absorb_final_a5(self, input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
libcrux_iot_sha3_keccak_KeccakXofState_c7
libcrux_iot_ml_dsa_hash_functions_portable_init_88(void) {
  return libcrux_iot_sha3_portable_incremental_new_a5();
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice out) {
  libcrux_iot_sha3_portable_incremental_squeeze_a5(self, out);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_x4_29(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake256_init_absorb_x4(
      input0, input1, input2, input3);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_first_block_x4(
      self);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_next_block_x4(
      self);
}

KRML_MUSTINLINE uint16_t
libcrux_iot_ml_dsa_sample_generate_domain_separator(uint8_t_x2 _) {
  uint8_t row = _.fst;
  uint8_t column = _.snd;
  return (uint32_t)(uint16_t)column | (uint32_t)(uint16_t)row << 8U;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_add_domain_separator(
    Eurydice_slice slice, uint8_t_x2 indices, uint8_t ret[34U]) {
  uint8_t out[34U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, (size_t)0U, Eurydice_slice_len(slice, uint8_t), uint8_t *),
      slice, uint8_t);
  uint16_t domain_separator =
      libcrux_iot_ml_dsa_sample_generate_domain_separator(indices);
  out[32U] = (uint8_t)domain_separator;
  out[33U] = (uint8_t)((uint32_t)domain_separator >> 8U);
  memcpy(ret, out, (size_t)34U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_add_error_domain_separator(
    Eurydice_slice slice, uint16_t domain_separator, uint8_t ret[66U]) {
  uint8_t out[66U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, (size_t)0U, Eurydice_slice_len(slice, uint8_t), uint8_t *),
      slice, uint8_t);
  out[64U] = (uint8_t)domain_separator;
  out[65U] = (uint8_t)((uint32_t)domain_separator >> 8U);
  memcpy(ret, out, (size_t)66U * sizeof(uint8_t));
}

libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
libcrux_iot_ml_dsa_simd_portable_vector_type_zero(void) {
  return (
      KRML_CLITERAL(libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients){
          .values = {0U}});
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
libcrux_iot_ml_dsa_simd_portable_zero_c5(void) {
  return libcrux_iot_ml_dsa_simd_portable_vector_type_zero();
}

void libcrux_iot_ml_dsa_simd_portable_vector_type_from_coefficient_array(
    Eurydice_slice array,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out) {
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)8U, out->values, int32_t),
      Eurydice_slice_subslice3(
          array, (size_t)0U,
          LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT, int32_t *),
      int32_t);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_from_coefficient_array_c5(
    Eurydice_slice array,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out) {
  libcrux_iot_ml_dsa_simd_portable_vector_type_from_coefficient_array(array,
                                                                      out);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_vector_type_to_coefficient_array(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *value,
    Eurydice_slice out) {
  Eurydice_slice_copy(
      out, Eurydice_array_to_slice((size_t)8U, value->values, int32_t),
      int32_t);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_to_coefficient_array_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *value,
    Eurydice_slice out) {
  libcrux_iot_ml_dsa_simd_portable_vector_type_to_coefficient_array(value, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_add(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs) {
  for (size_t i = (size_t)0U;
       i <
       Eurydice_slice_len(
           Eurydice_array_to_slice((size_t)8U, lhs->values, int32_t), int32_t);
       i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->values[uu____0] = lhs->values[uu____0] + rhs->values[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_add_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_add(lhs, rhs);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs) {
  for (size_t i = (size_t)0U;
       i <
       Eurydice_slice_len(
           Eurydice_array_to_slice((size_t)8U, lhs->values, int32_t), int32_t);
       i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->values[uu____0] = lhs->values[uu____0] - rhs->values[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_subtract_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(lhs, rhs);
}

KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t bound) {
  bool result = false;
  core_ops_range_Range_08 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end = Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)8U, simd_unit->values,
                                          int32_t),
                  int32_t)}),
          core_ops_range_Range_08, size_t, core_ops_range_Range_08);
  while (true) {
    core_option_Option_08 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_08);
    if (!(uu____0.tag == core_option_None)) {
      size_t i = uu____0.f0;
      int32_t coefficient = simd_unit->values[i];
      EURYDICE_ASSERT(!false, "panic!");
      int32_t sign = coefficient >> 31U;
      int32_t normalized = coefficient - (sign & (int32_t)2 * coefficient);
      bool uu____1;
      if (result) {
        uu____1 = true;
      } else {
        uu____1 = normalized >= bound;
      }
      result = uu____1;
      continue;
    }
    return result;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
bool libcrux_iot_ml_dsa_simd_portable_infinity_norm_exceeds_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t bound) {
  return libcrux_iot_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
      simd_unit, bound);
}

KRML_MUSTINLINE int32_t_x2
libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(int32_t gamma2,
                                                              int32_t r) {
  EURYDICE_ASSERT(!false, "panic!");
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

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose(
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *low,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *high) {
  for (size_t i = (size_t)0U;
       i <
       Eurydice_slice_len(
           Eurydice_array_to_slice((size_t)8U, low->values, int32_t), int32_t);
       i++) {
    size_t i0 = i;
    int32_t_x2 uu____0 =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(
            gamma2, simd_unit->values[i0]);
    int32_t uu____1 = uu____0.snd;
    low->values[i0] = uu____0.fst;
    high->values[i0] = uu____1;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_decompose_c5(
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *low,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *high) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose(gamma2, simd_unit, low,
                                                        high);
}

KRML_MUSTINLINE int32_t
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

KRML_MUSTINLINE size_t libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_hint(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *low,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *high,
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *hint) {
  size_t one_hints_count = (size_t)0U;
  for (size_t i = (size_t)0U;
       i <
       Eurydice_slice_len(
           Eurydice_array_to_slice((size_t)8U, hint->values, int32_t), int32_t);
       i++) {
    size_t i0 = i;
    hint->values[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_one_hint(
            low->values[i0], high->values[i0], gamma2);
    one_hints_count = one_hints_count + (size_t)hint->values[i0];
  }
  return one_hints_count;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t libcrux_iot_ml_dsa_simd_portable_compute_hint_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *low,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *high,
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *hint) {
  return libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_hint(low, high,
                                                                  gamma2, hint);
}

KRML_MUSTINLINE int32_t
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

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_use_hint(
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *hint) {
  for (size_t i = (size_t)0U;
       i <
       Eurydice_slice_len(
           Eurydice_array_to_slice((size_t)8U, hint->values, int32_t), int32_t);
       i++) {
    size_t i0 = i;
    int32_t uu____0 = libcrux_iot_ml_dsa_simd_portable_arithmetic_use_one_hint(
        gamma2, simd_unit->values[i0], hint->values[i0]);
    hint->values[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_use_hint_c5(
    int32_t gamma2,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *hint) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_use_hint(gamma2, simd_unit, hint);
}

KRML_MUSTINLINE uint64_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint64_t value) {
  return value & ((1ULL << (uint32_t)n) - 1ULL);
}

KRML_MUSTINLINE int32_t
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

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs) {
  for (size_t i = (size_t)0U;
       i <
       Eurydice_slice_len(
           Eurydice_array_to_slice((size_t)8U, lhs->values, int32_t), int32_t);
       i++) {
    size_t i0 = i;
    lhs->values[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
            (int64_t)lhs->values[i0] * (int64_t)rhs->values[i0]);
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_montgomery_multiply_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *lhs,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *rhs) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply(lhs, rhs);
}

KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(int32_t fe) {
  int32_t quotient = (fe + ((int32_t)1 << 22U)) >> 23U;
  return fe - quotient * LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS;
}

KRML_MUSTINLINE int32_t_x2
libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round_element(int32_t t) {
  EURYDICE_ASSERT(!false, "panic!");
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

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *t0,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *t1) {
  for (size_t i = (size_t)0U;
       i <
       Eurydice_slice_len(
           Eurydice_array_to_slice((size_t)8U, t0->values, int32_t), int32_t);
       i++) {
    size_t i0 = i;
    int32_t_x2 uu____0 =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round_element(
            t0->values[i0]);
    int32_t uu____1 = uu____0.snd;
    t0->values[i0] = uu____0.fst;
    t1->values[i0] = uu____1;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_power2round_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *t0,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *t1) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round(t0, t1);
}

KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
    Eurydice_slice randomness, Eurydice_slice out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(randomness, uint8_t) / (size_t)3U; i++) {
    size_t _cloop_i = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(randomness, _cloop_i * (size_t)3U,
                                 _cloop_i * (size_t)3U + (size_t)3U, uint8_t *);
    int32_t b0 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *);
    int32_t b1 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *);
    int32_t b2 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *);
    int32_t coefficient = ((b2 << 16U | b1 << 8U) | b0) & (int32_t)8388607;
    if (coefficient < LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS) {
      Eurydice_slice_index(out, sampled, int32_t, int32_t *) = coefficient;
      sampled++;
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_c5(
    Eurydice_slice randomness, Eurydice_slice out) {
  return libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
      randomness, out);
}

KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
    Eurydice_slice randomness, Eurydice_slice out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(randomness, uint8_t);
       i++) {
    size_t _cloop_j = i;
    uint8_t *byte =
        &Eurydice_slice_index(randomness, _cloop_j, uint8_t, uint8_t *);
    uint8_t try_0 =
        core_ops_bit__core__ops__bit__BitAnd_u8__u8__for___a__u8___bitand(byte,
                                                                          15U);
    uint8_t try_1 =
        core_ops_bit__core__ops__bit__Shr_i32__u8__for___a__u8___shr(
            byte, (int32_t)4);
    if (try_0 < 15U) {
      int32_t try_00 = (int32_t)try_0;
      int32_t try_0_mod_5 = try_00 - (try_00 * (int32_t)26 >> 7U) * (int32_t)5;
      Eurydice_slice_index(out, sampled, int32_t, int32_t *) =
          (int32_t)2 - try_0_mod_5;
      sampled++;
    }
    if (try_1 < 15U) {
      int32_t try_10 = (int32_t)try_1;
      int32_t try_1_mod_5 = try_10 - (try_10 * (int32_t)26 >> 7U) * (int32_t)5;
      Eurydice_slice_index(out, sampled, int32_t, int32_t *) =
          (int32_t)2 - try_1_mod_5;
      sampled++;
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_c5(
    Eurydice_slice randomness, Eurydice_slice out) {
  return libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
      randomness, out);
}

KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
    Eurydice_slice randomness, Eurydice_slice out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(randomness, uint8_t);
       i++) {
    size_t _cloop_j = i;
    uint8_t *byte =
        &Eurydice_slice_index(randomness, _cloop_j, uint8_t, uint8_t *);
    uint8_t try_0 =
        core_ops_bit__core__ops__bit__BitAnd_u8__u8__for___a__u8___bitand(byte,
                                                                          15U);
    uint8_t try_1 =
        core_ops_bit__core__ops__bit__Shr_i32__u8__for___a__u8___shr(
            byte, (int32_t)4);
    if (try_0 < 9U) {
      Eurydice_slice_index(out, sampled, int32_t, int32_t *) =
          (int32_t)4 - (int32_t)try_0;
      sampled++;
    }
    if (try_1 < 9U) {
      Eurydice_slice_index(out, sampled, int32_t, int32_t *) =
          (int32_t)4 - (int32_t)try_1;
      sampled++;
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_c5(
    Eurydice_slice randomness, Eurydice_slice out) {
  return libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
      randomness, out);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)8U, simd_unit->values, int32_t),
               int32_t) /
               (size_t)4U;
       i++) {
    size_t i0 = i;
    Eurydice_slice coefficients =
        Eurydice_array_to_subslice3(simd_unit->values, i0 * (size_t)4U,
                                    i0 * (size_t)4U + (size_t)4U, int32_t *);
    int32_t coefficient0 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        Eurydice_slice_index(coefficients, (size_t)0U, int32_t, int32_t *);
    int32_t coefficient1 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        Eurydice_slice_index(coefficients, (size_t)1U, int32_t, int32_t *);
    int32_t coefficient2 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        Eurydice_slice_index(coefficients, (size_t)2U, int32_t, int32_t *);
    int32_t coefficient3 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        Eurydice_slice_index(coefficients, (size_t)3U, int32_t, int32_t *);
    Eurydice_slice_index(serialized, (size_t)9U * i0, uint8_t, uint8_t *) =
        (uint8_t)coefficient0;
    Eurydice_slice_index(serialized, (size_t)9U * i0 + (size_t)1U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient0 >> 8U);
    Eurydice_slice_index(serialized, (size_t)9U * i0 + (size_t)2U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient0 >> 16U);
    size_t uu____0 = (size_t)9U * i0 + (size_t)2U;
    Eurydice_slice_index(serialized, uu____0, uint8_t, uint8_t *) =
        (uint32_t)Eurydice_slice_index(serialized, uu____0, uint8_t,
                                       uint8_t *) |
        (uint32_t)(uint8_t)(coefficient1 << 2U);
    Eurydice_slice_index(serialized, (size_t)9U * i0 + (size_t)3U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient1 >> 6U);
    Eurydice_slice_index(serialized, (size_t)9U * i0 + (size_t)4U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient1 >> 14U);
    size_t uu____1 = (size_t)9U * i0 + (size_t)4U;
    Eurydice_slice_index(serialized, uu____1, uint8_t, uint8_t *) =
        (uint32_t)Eurydice_slice_index(serialized, uu____1, uint8_t,
                                       uint8_t *) |
        (uint32_t)(uint8_t)(coefficient2 << 4U);
    Eurydice_slice_index(serialized, (size_t)9U * i0 + (size_t)5U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient2 >> 4U);
    Eurydice_slice_index(serialized, (size_t)9U * i0 + (size_t)6U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient2 >> 12U);
    size_t uu____2 = (size_t)9U * i0 + (size_t)6U;
    Eurydice_slice_index(serialized, uu____2, uint8_t, uint8_t *) =
        (uint32_t)Eurydice_slice_index(serialized, uu____2, uint8_t,
                                       uint8_t *) |
        (uint32_t)(uint8_t)(coefficient3 << 6U);
    Eurydice_slice_index(serialized, (size_t)9U * i0 + (size_t)7U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient3 >> 2U);
    Eurydice_slice_index(serialized, (size_t)9U * i0 + (size_t)8U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient3 >> 10U);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)8U, simd_unit->values, int32_t),
               int32_t) /
               (size_t)2U;
       i++) {
    size_t i0 = i;
    Eurydice_slice coefficients =
        Eurydice_array_to_subslice3(simd_unit->values, i0 * (size_t)2U,
                                    i0 * (size_t)2U + (size_t)2U, int32_t *);
    int32_t coefficient0 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        Eurydice_slice_index(coefficients, (size_t)0U, int32_t, int32_t *);
    int32_t coefficient1 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        Eurydice_slice_index(coefficients, (size_t)1U, int32_t, int32_t *);
    Eurydice_slice_index(serialized, (size_t)5U * i0, uint8_t, uint8_t *) =
        (uint8_t)coefficient0;
    Eurydice_slice_index(serialized, (size_t)5U * i0 + (size_t)1U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient0 >> 8U);
    Eurydice_slice_index(serialized, (size_t)5U * i0 + (size_t)2U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient0 >> 16U);
    size_t uu____0 = (size_t)5U * i0 + (size_t)2U;
    Eurydice_slice_index(serialized, uu____0, uint8_t, uint8_t *) =
        (uint32_t)Eurydice_slice_index(serialized, uu____0, uint8_t,
                                       uint8_t *) |
        (uint32_t)(uint8_t)(coefficient1 << 4U);
    Eurydice_slice_index(serialized, (size_t)5U * i0 + (size_t)3U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient1 >> 4U);
    Eurydice_slice_index(serialized, (size_t)5U * i0 + (size_t)4U, uint8_t,
                         uint8_t *) = (uint8_t)(coefficient1 >> 12U);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized, size_t gamma1_exponent) {
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
void libcrux_iot_ml_dsa_simd_portable_gamma1_serialize_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized, size_t gamma1_exponent) {
  libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize(
      simd_unit, serialized, gamma1_exponent);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)9U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)9U, i0 * (size_t)9U + (size_t)9U, uint8_t *);
    int32_t coefficient0 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *);
    coefficient0 =
        coefficient0 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *)
            << 8U;
    coefficient0 =
        coefficient0 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *)
            << 16U;
    coefficient0 =
        coefficient0 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient1 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) >>
        2U;
    coefficient1 =
        coefficient1 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *)
            << 6U;
    coefficient1 =
        coefficient1 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *)
            << 14U;
    coefficient1 =
        coefficient1 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient2 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *) >>
        4U;
    coefficient2 =
        coefficient2 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *)
            << 4U;
    coefficient2 =
        coefficient2 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *)
            << 12U;
    coefficient2 =
        coefficient2 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient3 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *) >>
        6U;
    coefficient3 =
        coefficient3 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *)
            << 2U;
    coefficient3 =
        coefficient3 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *)
            << 10U;
    coefficient3 =
        coefficient3 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    simd_unit->values[(size_t)4U * i0] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficient0;
    simd_unit->values[(size_t)4U * i0 + (size_t)1U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficient1;
    simd_unit->values[(size_t)4U * i0 + (size_t)2U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficient2;
    simd_unit->values[(size_t)4U * i0 + (size_t)3U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        coefficient3;
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)5U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)5U, i0 * (size_t)5U + (size_t)5U, uint8_t *);
    int32_t coefficient0 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *);
    coefficient0 =
        coefficient0 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *)
            << 8U;
    coefficient0 =
        coefficient0 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *)
            << 16U;
    coefficient0 =
        coefficient0 &
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient1 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) >>
        4U;
    coefficient1 =
        coefficient1 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *)
            << 4U;
    coefficient1 =
        coefficient1 |
        (int32_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *)
            << 12U;
    simd_unit->values[(size_t)2U * i0] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        coefficient0;
    simd_unit->values[(size_t)2U * i0 + (size_t)1U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        coefficient1;
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out,
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
void libcrux_iot_ml_dsa_simd_portable_gamma1_deserialize_c5(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out,
    size_t gamma1_exponent) {
  libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize(serialized, out,
                                                               gamma1_exponent);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_commitment_serialize(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  void *uu____0 = (void *)0U;
  switch ((uint8_t)Eurydice_slice_len(serialized, uint8_t)) {
    case 4U: {
      break;
    }
    case 6U: {
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice(
                                      (size_t)8U, simd_unit->values, int32_t),
                                  int32_t) /
                   (size_t)4U;
           i++) {
        size_t i0 = i;
        Eurydice_slice coefficients = Eurydice_array_to_subslice3(
            simd_unit->values, i0 * (size_t)4U, i0 * (size_t)4U + (size_t)4U,
            int32_t *);
        uint8_t coefficient0 = (uint8_t)Eurydice_slice_index(
            coefficients, (size_t)0U, int32_t, int32_t *);
        uint8_t coefficient1 = (uint8_t)Eurydice_slice_index(
            coefficients, (size_t)1U, int32_t, int32_t *);
        uint8_t coefficient2 = (uint8_t)Eurydice_slice_index(
            coefficients, (size_t)2U, int32_t, int32_t *);
        uint8_t coefficient3 = (uint8_t)Eurydice_slice_index(
            coefficients, (size_t)3U, int32_t, int32_t *);
        Eurydice_slice_index(serialized, (size_t)3U * i0, uint8_t, uint8_t *) =
            (uint32_t)coefficient1 << 6U | (uint32_t)coefficient0;
        Eurydice_slice_index(serialized, (size_t)3U * i0 + (size_t)1U, uint8_t,
                             uint8_t *) =
            (uint32_t)coefficient2 << 4U | (uint32_t)coefficient1 >> 2U;
        Eurydice_slice_index(serialized, (size_t)3U * i0 + (size_t)2U, uint8_t,
                             uint8_t *) =
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
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)8U, simd_unit->values, int32_t),
               int32_t) /
               (size_t)2U;
       i++) {
    size_t i0 = i;
    Eurydice_slice coefficients =
        Eurydice_array_to_subslice3(simd_unit->values, i0 * (size_t)2U,
                                    i0 * (size_t)2U + (size_t)2U, int32_t *);
    uint8_t coefficient0 = (uint8_t)Eurydice_slice_index(
        coefficients, (size_t)0U, int32_t, int32_t *);
    uint8_t coefficient1 = (uint8_t)Eurydice_slice_index(
        coefficients, (size_t)1U, int32_t, int32_t *);
    Eurydice_slice_index(serialized, i0, uint8_t, uint8_t *) =
        (uint32_t)coefficient1 << 4U | (uint32_t)coefficient0;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_commitment_serialize_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  libcrux_iot_ml_dsa_simd_portable_encoding_commitment_serialize(simd_unit,
                                                                 serialized);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)8U, simd_unit->values, int32_t),
               int32_t) /
               (size_t)2U;
       i++) {
    size_t i0 = i;
    Eurydice_slice coefficients =
        Eurydice_array_to_subslice3(simd_unit->values, i0 * (size_t)2U,
                                    i0 * (size_t)2U + (size_t)2U, int32_t *);
    uint8_t coefficient0 =
        (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA -
                  Eurydice_slice_index(coefficients, (size_t)0U, int32_t,
                                       int32_t *));
    uint8_t coefficient1 =
        (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA -
                  Eurydice_slice_index(coefficients, (size_t)1U, int32_t,
                                       int32_t *));
    Eurydice_slice_index(serialized, i0, uint8_t, uint8_t *) =
        (uint32_t)coefficient1 << 4U | (uint32_t)coefficient0;
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  uint8_t coefficient0 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->values[0U]);
  uint8_t coefficient1 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->values[1U]);
  uint8_t coefficient2 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->values[2U]);
  uint8_t coefficient3 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->values[3U]);
  uint8_t coefficient4 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->values[4U]);
  uint8_t coefficient5 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->values[5U]);
  uint8_t coefficient6 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->values[6U]);
  uint8_t coefficient7 =
      (uint8_t)(LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA -
                simd_unit->values[7U]);
  Eurydice_slice_index(serialized, (size_t)0U, uint8_t, uint8_t *) =
      ((uint32_t)coefficient2 << 6U | (uint32_t)coefficient1 << 3U) |
      (uint32_t)coefficient0;
  Eurydice_slice_index(serialized, (size_t)1U, uint8_t, uint8_t *) =
      (((uint32_t)coefficient5 << 7U | (uint32_t)coefficient4 << 4U) |
       (uint32_t)coefficient3 << 1U) |
      (uint32_t)coefficient2 >> 2U;
  Eurydice_slice_index(serialized, (size_t)2U, uint8_t, uint8_t *) =
      ((uint32_t)coefficient7 << 5U | (uint32_t)coefficient6 << 2U) |
      (uint32_t)coefficient5 >> 1U;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize(
    libcrux_iot_ml_dsa_constants_Eta eta,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  void *uu____0 = (void *)0U;
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
void libcrux_iot_ml_dsa_simd_portable_error_serialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize(eta, simd_unit,
                                                            serialized);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_4(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_units) {
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(serialized, uint8_t);
       i++) {
    size_t i0 = i;
    uint8_t *byte = &Eurydice_slice_index(serialized, i0, uint8_t, uint8_t *);
    uint8_t uu____0 =
        core_ops_bit__core__ops__bit__BitAnd_u8__u8__for___a__u8___bitand(byte,
                                                                          15U);
    simd_units->values[(size_t)2U * i0] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA -
        (int32_t)uu____0;
    uint8_t uu____1 =
        core_ops_bit__core__ops__bit__Shr_i32__u8__for___a__u8___shr(
            byte, (int32_t)4);
    simd_units->values[(size_t)2U * i0 + (size_t)1U] =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA -
        (int32_t)uu____1;
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_2(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit) {
  int32_t byte0 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)0U, uint8_t, uint8_t *);
  int32_t byte1 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)1U, uint8_t, uint8_t *);
  int32_t byte2 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)2U, uint8_t, uint8_t *);
  simd_unit->values[0U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte0 & (int32_t)7);
  simd_unit->values[1U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte0 >> 3U & (int32_t)7);
  simd_unit->values[2U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      ((byte0 >> 6U | byte1 << 2U) & (int32_t)7);
  simd_unit->values[3U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte1 >> 1U & (int32_t)7);
  simd_unit->values[4U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte1 >> 4U & (int32_t)7);
  simd_unit->values[5U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      ((byte1 >> 7U | byte2 << 1U) & (int32_t)7);
  simd_unit->values[6U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte2 >> 2U & (int32_t)7);
  simd_unit->values[7U] =
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte2 >> 5U & (int32_t)7);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out) {
  void *uu____0 = (void *)0U;
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
void libcrux_iot_ml_dsa_simd_portable_error_deserialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize(eta, serialized,
                                                              out);
}

KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(int32_t t0) {
  return ((int32_t)1
          << (uint32_t)(LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T -
                        (size_t)1U)) -
         t0;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_t0_serialize(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  int32_t coefficient0 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->values[0U]);
  int32_t coefficient1 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->values[1U]);
  int32_t coefficient2 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->values[2U]);
  int32_t coefficient3 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->values[3U]);
  int32_t coefficient4 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->values[4U]);
  int32_t coefficient5 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->values[5U]);
  int32_t coefficient6 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->values[6U]);
  int32_t coefficient7 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->values[7U]);
  Eurydice_slice_index(serialized, (size_t)0U, uint8_t, uint8_t *) =
      (uint8_t)coefficient0;
  Eurydice_slice_index(serialized, (size_t)1U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient0 >> 8U);
  size_t uu____0 = (size_t)1U;
  Eurydice_slice_index(serialized, uu____0, uint8_t, uint8_t *) =
      (uint32_t)Eurydice_slice_index(serialized, uu____0, uint8_t, uint8_t *) |
      (uint32_t)(uint8_t)(coefficient1 << 5U);
  Eurydice_slice_index(serialized, (size_t)2U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient1 >> 3U);
  Eurydice_slice_index(serialized, (size_t)3U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient1 >> 11U);
  size_t uu____1 = (size_t)3U;
  Eurydice_slice_index(serialized, uu____1, uint8_t, uint8_t *) =
      (uint32_t)Eurydice_slice_index(serialized, uu____1, uint8_t, uint8_t *) |
      (uint32_t)(uint8_t)(coefficient2 << 2U);
  Eurydice_slice_index(serialized, (size_t)4U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient2 >> 6U);
  size_t uu____2 = (size_t)4U;
  Eurydice_slice_index(serialized, uu____2, uint8_t, uint8_t *) =
      (uint32_t)Eurydice_slice_index(serialized, uu____2, uint8_t, uint8_t *) |
      (uint32_t)(uint8_t)(coefficient3 << 7U);
  Eurydice_slice_index(serialized, (size_t)5U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient3 >> 1U);
  Eurydice_slice_index(serialized, (size_t)6U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient3 >> 9U);
  size_t uu____3 = (size_t)6U;
  Eurydice_slice_index(serialized, uu____3, uint8_t, uint8_t *) =
      (uint32_t)Eurydice_slice_index(serialized, uu____3, uint8_t, uint8_t *) |
      (uint32_t)(uint8_t)(coefficient4 << 4U);
  Eurydice_slice_index(serialized, (size_t)7U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient4 >> 4U);
  Eurydice_slice_index(serialized, (size_t)8U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient4 >> 12U);
  size_t uu____4 = (size_t)8U;
  Eurydice_slice_index(serialized, uu____4, uint8_t, uint8_t *) =
      (uint32_t)Eurydice_slice_index(serialized, uu____4, uint8_t, uint8_t *) |
      (uint32_t)(uint8_t)(coefficient5 << 1U);
  Eurydice_slice_index(serialized, (size_t)9U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient5 >> 7U);
  size_t uu____5 = (size_t)9U;
  Eurydice_slice_index(serialized, uu____5, uint8_t, uint8_t *) =
      (uint32_t)Eurydice_slice_index(serialized, uu____5, uint8_t, uint8_t *) |
      (uint32_t)(uint8_t)(coefficient6 << 6U);
  Eurydice_slice_index(serialized, (size_t)10U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient6 >> 2U);
  Eurydice_slice_index(serialized, (size_t)11U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient6 >> 10U);
  size_t uu____6 = (size_t)11U;
  Eurydice_slice_index(serialized, uu____6, uint8_t, uint8_t *) =
      (uint32_t)Eurydice_slice_index(serialized, uu____6, uint8_t, uint8_t *) |
      (uint32_t)(uint8_t)(coefficient7 << 3U);
  Eurydice_slice_index(serialized, (size_t)12U, uint8_t, uint8_t *) =
      (uint8_t)(coefficient7 >> 5U);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_serialize_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t0_serialize(simd_unit, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_t0_deserialize(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit) {
  int32_t byte0 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)0U, uint8_t, uint8_t *);
  int32_t byte1 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)1U, uint8_t, uint8_t *);
  int32_t byte2 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)2U, uint8_t, uint8_t *);
  int32_t byte3 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)3U, uint8_t, uint8_t *);
  int32_t byte4 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)4U, uint8_t, uint8_t *);
  int32_t byte5 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)5U, uint8_t, uint8_t *);
  int32_t byte6 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)6U, uint8_t, uint8_t *);
  int32_t byte7 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)7U, uint8_t, uint8_t *);
  int32_t byte8 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)8U, uint8_t, uint8_t *);
  int32_t byte9 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)9U, uint8_t, uint8_t *);
  int32_t byte10 = (int32_t)Eurydice_slice_index(serialized, (size_t)10U,
                                                 uint8_t, uint8_t *);
  int32_t byte11 = (int32_t)Eurydice_slice_index(serialized, (size_t)11U,
                                                 uint8_t, uint8_t *);
  int32_t byte12 = (int32_t)Eurydice_slice_index(serialized, (size_t)12U,
                                                 uint8_t, uint8_t *);
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
  simd_unit->values[0U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient0);
  simd_unit->values[1U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient1);
  simd_unit->values[2U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient2);
  simd_unit->values[3U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient3);
  simd_unit->values[4U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient4);
  simd_unit->values[5U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient5);
  simd_unit->values[6U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient6);
  simd_unit->values[7U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient7);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_deserialize_c5(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t0_deserialize(serialized, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_t1_serialize(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)8U, simd_unit->values, int32_t),
               int32_t) /
               (size_t)4U;
       i++) {
    size_t i0 = i;
    Eurydice_slice coefficients =
        Eurydice_array_to_subslice3(simd_unit->values, i0 * (size_t)4U,
                                    i0 * (size_t)4U + (size_t)4U, int32_t *);
    Eurydice_slice_index(serialized, (size_t)5U * i0, uint8_t, uint8_t *) =
        (uint8_t)(Eurydice_slice_index(coefficients, (size_t)0U, int32_t,
                                       int32_t *) &
                  (int32_t)255);
    Eurydice_slice_index(serialized, (size_t)5U * i0 + (size_t)1U, uint8_t,
                         uint8_t *) =
        (uint32_t)(uint8_t)(Eurydice_slice_index(coefficients, (size_t)1U,
                                                 int32_t, int32_t *) &
                            (int32_t)63)
            << 2U |
        (uint32_t)(uint8_t)(Eurydice_slice_index(coefficients, (size_t)0U,
                                                 int32_t, int32_t *) >>
                                8U &
                            (int32_t)3);
    Eurydice_slice_index(serialized, (size_t)5U * i0 + (size_t)2U, uint8_t,
                         uint8_t *) =
        (uint32_t)(uint8_t)(Eurydice_slice_index(coefficients, (size_t)2U,
                                                 int32_t, int32_t *) &
                            (int32_t)15)
            << 4U |
        (uint32_t)(uint8_t)(Eurydice_slice_index(coefficients, (size_t)1U,
                                                 int32_t, int32_t *) >>
                                6U &
                            (int32_t)15);
    Eurydice_slice_index(serialized, (size_t)5U * i0 + (size_t)3U, uint8_t,
                         uint8_t *) =
        (uint32_t)(uint8_t)(Eurydice_slice_index(coefficients, (size_t)3U,
                                                 int32_t, int32_t *) &
                            (int32_t)3)
            << 6U |
        (uint32_t)(uint8_t)(Eurydice_slice_index(coefficients, (size_t)2U,
                                                 int32_t, int32_t *) >>
                                4U &
                            (int32_t)63);
    Eurydice_slice_index(serialized, (size_t)5U * i0 + (size_t)4U, uint8_t,
                         uint8_t *) =
        (uint8_t)(Eurydice_slice_index(coefficients, (size_t)3U, int32_t,
                                       int32_t *) >>
                      2U &
                  (int32_t)255);
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_serialize_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    Eurydice_slice out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t1_serialize(simd_unit, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_t1_deserialize(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit) {
  int32_t mask = ((int32_t)1 << (uint32_t)
                      LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T) -
                 (int32_t)1;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)5U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)5U, i0 * (size_t)5U + (size_t)5U, uint8_t *);
    int32_t byte0 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *);
    int32_t byte1 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *);
    int32_t byte2 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *);
    int32_t byte3 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *);
    int32_t byte4 =
        (int32_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *);
    simd_unit->values[(size_t)4U * i0] = (byte0 | byte1 << 8U) & mask;
    simd_unit->values[(size_t)4U * i0 + (size_t)1U] =
        (byte1 >> 2U | byte2 << 6U) & mask;
    simd_unit->values[(size_t)4U * i0 + (size_t)2U] =
        (byte2 >> 4U | byte3 << 4U) & mask;
    simd_unit->values[(size_t)4U * i0 + (size_t)3U] =
        (byte3 >> 6U | byte4 << 2U) & mask;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_deserialize_c5(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t1_deserialize(serialized, out);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t c) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)8U, simd_unit->values, int32_t),
               int32_t);
       i++) {
    size_t i0 = i;
    simd_unit->values[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
            (int64_t)simd_unit->values[i0] * (int64_t)c);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_99(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)16U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)16U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)25847);
    re[j + (size_t)16U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)16U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_7(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_99(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -2608894
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_990(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)8U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)8U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2608894);
    re[j + (size_t)8U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)8U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -518909
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)8U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)8U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-518909);
    re[j + (size_t)8U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)8U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_6(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_991(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)237124);
    re[j + (size_t)4U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)4U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -777960
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a8(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-777960);
    re[j + (size_t)4U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)4U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -876248
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-876248);
    re[j + (size_t)4U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)4U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 466468
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d9(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)466468);
    re[j + (size_t)4U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)4U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_992(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)1826347);
    re[j + (size_t)2U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 2353451
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)2353451);
    re[j + (size_t)2U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -359251
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a80(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-359251);
    re[j + (size_t)2U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= -2091905
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_95(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2091905);
    re[j + (size_t)2U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= 3119733
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)3119733);
    re[j + (size_t)2U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -2884855
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2884855);
    re[j + (size_t)2U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 3111497
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d90(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)3111497);
    re[j + (size_t)2U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 2680103
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)2680103);
    re[j + (size_t)2U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_993(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)2725464);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 1024112
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1c(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)2U; i < (size_t)2U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)1024112);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -1079900
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_6b0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-1079900);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 3585928
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_44(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)6U; i < (size_t)6U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)3585928);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -549488
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a81(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-549488);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1119584
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1f(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)10U; i < (size_t)10U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-1119584);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= 2619752
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_950(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)2619752);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2108549
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)14U; i < (size_t)14U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2108549);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2118186
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_7a2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-2118186);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= -3859737
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_e4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)18U; i < (size_t)18U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-3859737);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1399561
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_de0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-1399561);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -3277672
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_05(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)22U; i < (size_t)22U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-3277672);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 1757237
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d91(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)1757237);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -19422
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3a(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)26U; i < (size_t)26U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)-19422);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 4010497
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_3b1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)4010497);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 280005
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_a0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)30U; i < (size_t)30U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients tmp =
        re[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, (int32_t)280005);
    re[j + (size_t)1U] = re[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_3(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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

KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int32_t fe, int32_t fer) {
  return libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
      (int64_t)fe * (int64_t)fer);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta) {
  int32_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[4U], zeta);
  simd_unit->values[4U] = simd_unit->values[0U] - t;
  simd_unit->values[0U] = simd_unit->values[0U] + t;
  int32_t t0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[5U], zeta);
  simd_unit->values[5U] = simd_unit->values[1U] - t0;
  simd_unit->values[1U] = simd_unit->values[1U] + t0;
  int32_t t1 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[6U], zeta);
  simd_unit->values[6U] = simd_unit->values[2U] - t1;
  simd_unit->values[2U] = simd_unit->values[2U] + t1;
  int32_t t2 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[7U], zeta);
  simd_unit->values[7U] = simd_unit->values[3U] - t2;
  simd_unit->values[3U] = simd_unit->values[3U] + t2;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta) {
  libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(&re[index],
                                                                zeta);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta1, int32_t zeta2) {
  int32_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[2U], zeta1);
  simd_unit->values[2U] = simd_unit->values[0U] - t;
  simd_unit->values[0U] = simd_unit->values[0U] + t;
  int32_t t0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[3U], zeta1);
  simd_unit->values[3U] = simd_unit->values[1U] - t0;
  simd_unit->values[1U] = simd_unit->values[1U] + t0;
  int32_t t1 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[6U], zeta2);
  simd_unit->values[6U] = simd_unit->values[4U] - t1;
  simd_unit->values[4U] = simd_unit->values[4U] + t1;
  int32_t t2 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[7U], zeta2);
  simd_unit->values[7U] = simd_unit->values[5U] - t2;
  simd_unit->values[5U] = simd_unit->values[5U] + t2;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta_0, int32_t zeta_1) {
  libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(&re[index],
                                                                zeta_0, zeta_1);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta0, int32_t zeta1, int32_t zeta2, int32_t zeta3) {
  int32_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[1U], zeta0);
  simd_unit->values[1U] = simd_unit->values[0U] - t;
  simd_unit->values[0U] = simd_unit->values[0U] + t;
  int32_t t0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[3U], zeta1);
  simd_unit->values[3U] = simd_unit->values[2U] - t0;
  simd_unit->values[2U] = simd_unit->values[2U] + t0;
  int32_t t1 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[5U], zeta2);
  simd_unit->values[5U] = simd_unit->values[4U] - t1;
  simd_unit->values[4U] = simd_unit->values[4U] + t1;
  int32_t t2 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->values[7U], zeta3);
  simd_unit->values[7U] = simd_unit->values[6U] - t2;
  simd_unit->values[6U] = simd_unit->values[6U] + t2;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta_0, int32_t zeta_1, int32_t zeta_2, int32_t zeta_3) {
  libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
      &re[index], zeta_0, zeta_1, zeta_2, zeta_3);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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
void libcrux_iot_ml_dsa_simd_portable_ntt_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_units) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt(simd_units);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta0, int32_t zeta1, int32_t zeta2, int32_t zeta3) {
  int32_t a_minus_b = simd_unit->values[1U] - simd_unit->values[0U];
  simd_unit->values[0U] = simd_unit->values[0U] + simd_unit->values[1U];
  simd_unit->values[1U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta0);
  int32_t a_minus_b0 = simd_unit->values[3U] - simd_unit->values[2U];
  simd_unit->values[2U] = simd_unit->values[2U] + simd_unit->values[3U];
  simd_unit->values[3U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, zeta1);
  int32_t a_minus_b1 = simd_unit->values[5U] - simd_unit->values[4U];
  simd_unit->values[4U] = simd_unit->values[4U] + simd_unit->values[5U];
  simd_unit->values[5U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, zeta2);
  int32_t a_minus_b2 = simd_unit->values[7U] - simd_unit->values[6U];
  simd_unit->values[6U] = simd_unit->values[6U] + simd_unit->values[7U];
  simd_unit->values[7U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, zeta3);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta0, int32_t zeta1, int32_t zeta2, int32_t zeta3) {
  libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
      &re[index], zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta0, int32_t zeta1) {
  int32_t a_minus_b = simd_unit->values[2U] - simd_unit->values[0U];
  simd_unit->values[0U] = simd_unit->values[0U] + simd_unit->values[2U];
  simd_unit->values[2U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta0);
  int32_t a_minus_b0 = simd_unit->values[3U] - simd_unit->values[1U];
  simd_unit->values[1U] = simd_unit->values[1U] + simd_unit->values[3U];
  simd_unit->values[3U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, zeta0);
  int32_t a_minus_b1 = simd_unit->values[6U] - simd_unit->values[4U];
  simd_unit->values[4U] = simd_unit->values[4U] + simd_unit->values[6U];
  simd_unit->values[6U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, zeta1);
  int32_t a_minus_b2 = simd_unit->values[7U] - simd_unit->values[5U];
  simd_unit->values[5U] = simd_unit->values[5U] + simd_unit->values[7U];
  simd_unit->values[7U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, zeta1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta_00, int32_t zeta_01) {
  libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
      &re[index], zeta_00, zeta_01);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit,
    int32_t zeta) {
  int32_t a_minus_b = simd_unit->values[4U] - simd_unit->values[0U];
  simd_unit->values[0U] = simd_unit->values[0U] + simd_unit->values[4U];
  simd_unit->values[4U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta);
  int32_t a_minus_b0 = simd_unit->values[5U] - simd_unit->values[1U];
  simd_unit->values[1U] = simd_unit->values[1U] + simd_unit->values[5U];
  simd_unit->values[5U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, zeta);
  int32_t a_minus_b1 = simd_unit->values[6U] - simd_unit->values[2U];
  simd_unit->values[2U] = simd_unit->values[2U] + simd_unit->values[6U];
  simd_unit->values[6U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, zeta);
  int32_t a_minus_b2 = simd_unit->values[7U] - simd_unit->values[3U];
  simd_unit->values[3U] = simd_unit->values[3U] + simd_unit->values[7U];
  simd_unit->values[7U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, zeta);
}

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re, size_t index,
    int32_t zeta1) {
  libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
      &re[index], zeta1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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
inline libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *self) {
  return self[0U];
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 280005
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_99(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)280005);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 4010497
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1c(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)2U; i < (size_t)2U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)4010497);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -19422
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)-19422);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 1757237
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_44(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)6U; i < (size_t)6U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)1757237);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -3277672
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a8(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)-3277672);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1399561
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1f(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)10U; i < (size_t)10U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)-1399561);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= -3859737
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_95(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)-3859737);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2118186
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)14U; i < (size_t)14U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)-2118186);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2108549
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)-2108549);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= 2619752
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_e4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)18U; i < (size_t)18U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)2619752);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1119584
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)-1119584);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -549488
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_05(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)22U; i < (size_t)22U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)-549488);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 3585928
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d9(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)3585928);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -1079900
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3a(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)26U; i < (size_t)26U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)-1079900);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 1024112
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)1024112);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 2725464
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)30U; i < (size_t)30U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)1U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)1U], (int32_t)2725464);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_990(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)2U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)2U], (int32_t)2680103);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 3111497
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_6b0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)2U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)2U], (int32_t)3111497);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -2884855
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a80(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)2U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)2U], (int32_t)-2884855);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= 3119733
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_950(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)2U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)2U], (int32_t)3119733);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= -2091905
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)2U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)2U], (int32_t)-2091905);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -359251
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_de0(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)2U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)2U], (int32_t)-359251);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 2353451
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d90(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)2U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)2U], (int32_t)2353451);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 1826347
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_3b1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)2U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)2U], (int32_t)1826347);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_991(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)4U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)4U], (int32_t)466468);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -876248
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_a81(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)4U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)4U], (int32_t)-876248);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -777960
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a1(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)4U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)4U], (int32_t)-777960);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 237124
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d91(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)4U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)4U], (int32_t)237124);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_992(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)8U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)8U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)8U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)8U], (int32_t)-518909);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -2608894
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_7a2(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)8U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)8U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)8U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)8U], (int32_t)-2608894);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_993(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)16U; i++) {
    size_t j = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re[j + (size_t)16U]);
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b, &re[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re[j], &rejs);
    re[j + (size_t)16U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[j + (size_t)16U], (int32_t)25847);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_993(re);
}

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(re);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, re,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re[i0], (int32_t)41978);
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_invert_ntt_montgomery_c5(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_units) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(simd_units);
}

uint8_t_x2 libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
    size_t index, size_t width) {
  return (KRML_CLITERAL(uint8_t_x2){.fst = (uint8_t)(index / width),
                                    .snd = (uint8_t)(index % width)});
}

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
libcrux_iot_ml_dsa_polynomial_zero_c2_08(void) {
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d lit;
  libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
      repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_simd_portable_zero_c5();
  }
  memcpy(lit.simd_units, repeat_expression,
         (size_t)32U *
             sizeof(libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients));
  return lit;
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_field_modulus with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out) {
  bool done = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(randomness, uint8_t) / (size_t)24U; i++) {
    size_t _cloop_i = i;
    Eurydice_slice random_bytes = Eurydice_slice_subslice3(
        randomness, _cloop_i * (size_t)24U,
        _cloop_i * (size_t)24U + (size_t)24U, uint8_t *);
    if (!done) {
      Eurydice_slice uu____0 = random_bytes;
      size_t sampled =
          libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_c5(
              uu____0, Eurydice_array_to_subslice_from(
                           (size_t)263U, out, sampled_coefficients[0U], int32_t,
                           size_t, int32_t[]));
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
void libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
    Eurydice_slice array,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_SIMD_UNITS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_from_coefficient_array_c5(
        Eurydice_slice_subslice3(
            array,
            i0 * LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
            int32_t *),
        &result->simd_units[i0]);
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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
    size_t columns, Eurydice_slice seed, Eurydice_slice matrix,
    uint8_t *rand_stack0, uint8_t *rand_stack1, uint8_t *rand_stack2,
    uint8_t *rand_stack3, Eurydice_slice tmp_stack, size_t start_index,
    size_t elements_requested) {
  uint8_t seed0[34U];
  libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed,
      libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
          start_index, columns),
      seed0);
  uint8_t seed1[34U];
  libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed,
      libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
          start_index + (size_t)1U, columns),
      seed1);
  uint8_t seed2[34U];
  libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed,
      libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
          start_index + (size_t)2U, columns),
      seed2);
  uint8_t seed3[34U];
  libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed,
      libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
          start_index + (size_t)3U, columns),
      seed3);
  libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 state =
      libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_33(
          Eurydice_array_to_slice((size_t)34U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)34U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)34U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)34U, seed3, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_33(
      &state, rand_stack0, rand_stack1, rand_stack2, rand_stack3);
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  bool done0 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice((size_t)840U, rand_stack0, uint8_t),
          &sampled0,
          Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                               int32_t(*)[263U]));
  bool done1 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice((size_t)840U, rand_stack1, uint8_t),
          &sampled1,
          Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                               int32_t(*)[263U]));
  bool done2 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice((size_t)840U, rand_stack2, uint8_t),
          &sampled2,
          Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                               int32_t(*)[263U]));
  bool done3 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice((size_t)840U, rand_stack3, uint8_t),
          &sampled3,
          Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                               int32_t(*)[263U]));
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            uint8_t_168size_t__x4 randomnesses =
                libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
                    &state);
            if (!done0) {
              done0 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                              uint8_t),
                      &sampled0,
                      Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                                           int32_t(*)[263U]));
            }
            if (!done1) {
              done1 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                              uint8_t),
                      &sampled1,
                      Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                                           int32_t(*)[263U]));
            }
            if (!done2) {
              done2 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                              uint8_t),
                      &sampled2,
                      Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                                           int32_t(*)[263U]));
            }
            if (!done3) {
              done3 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.f3,
                                              uint8_t),
                      &sampled3,
                      Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                                           int32_t(*)[263U]));
            }
          }
        } else {
          uint8_t_168size_t__x4 randomnesses =
              libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
                  &state);
          if (!done0) {
            done0 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                            uint8_t),
                    &sampled0,
                    Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                                         int32_t(*)[263U]));
          }
          if (!done1) {
            done1 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                            uint8_t),
                    &sampled1,
                    Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                                         int32_t(*)[263U]));
          }
          if (!done2) {
            done2 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                            uint8_t),
                    &sampled2,
                    Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                                         int32_t(*)[263U]));
          }
          if (!done3) {
            done3 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.f3,
                                            uint8_t),
                    &sampled3,
                    Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                                         int32_t(*)[263U]));
          }
        }
      } else {
        uint8_t_168size_t__x4 randomnesses =
            libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
                &state);
        if (!done0) {
          done0 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                          uint8_t),
                  &sampled0,
                  Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                                       int32_t(*)[263U]));
        }
        if (!done1) {
          done1 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                          uint8_t),
                  &sampled1,
                  Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                                       int32_t(*)[263U]));
        }
        if (!done2) {
          done2 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                          uint8_t),
                  &sampled2,
                  Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                                       int32_t(*)[263U]));
        }
        if (!done3) {
          done3 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.f3,
                                          uint8_t),
                  &sampled3,
                  Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                                       int32_t(*)[263U]));
        }
      }
    } else {
      uint8_t_168size_t__x4 randomnesses =
          libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
              &state);
      if (!done0) {
        done0 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                        uint8_t),
                &sampled0,
                Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                                     int32_t(*)[263U]));
      }
      if (!done1) {
        done1 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                        uint8_t),
                &sampled1,
                Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                                     int32_t(*)[263U]));
      }
      if (!done2) {
        done2 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                        uint8_t),
                &sampled2,
                Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                                     int32_t(*)[263U]));
      }
      if (!done3) {
        done3 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice((size_t)168U, randomnesses.f3, uint8_t),
                &sampled3,
                Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                                     int32_t(*)[263U]));
      }
    }
  }
  for (size_t i = (size_t)0U; i < elements_requested; i++) {
    size_t k = i;
    libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
        Eurydice_array_to_slice(
            (size_t)263U,
            Eurydice_slice_index(tmp_stack, k, int32_t[263U], int32_t(*)[263U]),
            int32_t),
        &Eurydice_slice_index(
            matrix, start_index + k,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.matrix_flat
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_samplex4_matrix_flat_15(
    size_t columns, Eurydice_slice seed, Eurydice_slice matrix) {
  uint8_t rand_stack0[840U] = {0U};
  uint8_t rand_stack1[840U] = {0U};
  uint8_t rand_stack2[840U] = {0U};
  uint8_t rand_stack3[840U] = {0U};
  int32_t tmp_stack[4U][263U] = {{0U}};
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               matrix, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d) /
               (size_t)4U;
       i++) {
    size_t start_index = i;
    size_t start_index0 = start_index * (size_t)4U;
    size_t uu____0 = start_index0 + (size_t)4U;
    size_t elements_requested;
    if (uu____0 <=
        Eurydice_slice_len(
            matrix, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d)) {
      elements_requested = (size_t)4U;
    } else {
      elements_requested =
          Eurydice_slice_len(
              matrix, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d) -
          start_index0;
    }
    libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
        columns, seed, matrix, rand_stack0, rand_stack1, rand_stack2,
        rand_stack3,
        Eurydice_array_to_slice((size_t)4U, tmp_stack, int32_t[263U]),
        start_index0, elements_requested);
  }
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
void libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
    size_t columns, Eurydice_slice seed, Eurydice_slice matrix) {
  libcrux_iot_ml_dsa_samplex4_matrix_flat_15(columns, seed, matrix);
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_4 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_08(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out) {
  bool done = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i++) {
    size_t _cloop_i = i;
    Eurydice_slice random_bytes =
        Eurydice_slice_subslice3(randomness, _cloop_i * (size_t)4U,
                                 _cloop_i * (size_t)4U + (size_t)4U, uint8_t *);
    if (!done) {
      Eurydice_slice uu____0 = random_bytes;
      size_t sampled =
          libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_c5(
              uu____0, Eurydice_array_to_subslice_from(
                           (size_t)263U, out, sampled_coefficients[0U], int32_t,
                           size_t, int32_t[]));
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
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_08(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out) {
  bool done = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i++) {
    size_t _cloop_i = i;
    Eurydice_slice random_bytes =
        Eurydice_slice_subslice3(randomness, _cloop_i * (size_t)4U,
                                 _cloop_i * (size_t)4U + (size_t)4U, uint8_t *);
    if (!done) {
      Eurydice_slice uu____0 = random_bytes;
      size_t sampled =
          libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_c5(
              uu____0, Eurydice_array_to_subslice_from(
                           (size_t)263U, out, sampled_coefficients[0U], int32_t,
                           size_t, int32_t[]));
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
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice randomness,
    size_t *sampled, int32_t *out) {
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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice seed,
    uint16_t start_index, Eurydice_slice re) {
  uint8_t seed0[66U];
  libcrux_iot_ml_dsa_sample_add_error_domain_separator(seed, start_index,
                                                       seed0);
  uint8_t seed1[66U];
  libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 1U, seed1);
  uint8_t seed2[66U];
  libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 2U, seed2);
  uint8_t seed3[66U];
  libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 3U, seed3);
  libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 state =
      libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_x4_29(
          Eurydice_array_to_slice((size_t)66U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed3, uint8_t));
  uint8_t_136size_t__x4 randomnesses0 =
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_x4_29(
          &state);
  int32_t out[4U][263U] = {{0U}};
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  bool done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      eta, Eurydice_array_to_slice((size_t)136U, randomnesses0.fst, uint8_t),
      &sampled0, out[0U]);
  bool done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      eta, Eurydice_array_to_slice((size_t)136U, randomnesses0.snd, uint8_t),
      &sampled1, out[1U]);
  bool done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      eta, Eurydice_array_to_slice((size_t)136U, randomnesses0.thd, uint8_t),
      &sampled2, out[2U]);
  bool done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      eta, Eurydice_array_to_slice((size_t)136U, randomnesses0.f3, uint8_t),
      &sampled3, out[3U]);
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            uint8_t_136size_t__x4 randomnesses =
                libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
                    &state);
            if (!done0) {
              done0 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      eta,
                      Eurydice_array_to_slice((size_t)136U, randomnesses.fst,
                                              uint8_t),
                      &sampled0, out[0U]);
            }
            if (!done1) {
              done1 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      eta,
                      Eurydice_array_to_slice((size_t)136U, randomnesses.snd,
                                              uint8_t),
                      &sampled1, out[1U]);
            }
            if (!done2) {
              done2 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      eta,
                      Eurydice_array_to_slice((size_t)136U, randomnesses.thd,
                                              uint8_t),
                      &sampled2, out[2U]);
            }
            if (!done3) {
              done3 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      eta,
                      Eurydice_array_to_slice((size_t)136U, randomnesses.f3,
                                              uint8_t),
                      &sampled3, out[3U]);
            }
          }
        } else {
          uint8_t_136size_t__x4 randomnesses =
              libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
                  &state);
          if (!done0) {
            done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                eta,
                Eurydice_array_to_slice((size_t)136U, randomnesses.fst,
                                        uint8_t),
                &sampled0, out[0U]);
          }
          if (!done1) {
            done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                eta,
                Eurydice_array_to_slice((size_t)136U, randomnesses.snd,
                                        uint8_t),
                &sampled1, out[1U]);
          }
          if (!done2) {
            done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                eta,
                Eurydice_array_to_slice((size_t)136U, randomnesses.thd,
                                        uint8_t),
                &sampled2, out[2U]);
          }
          if (!done3) {
            done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                eta,
                Eurydice_array_to_slice((size_t)136U, randomnesses.f3, uint8_t),
                &sampled3, out[3U]);
          }
        }
      } else {
        uint8_t_136size_t__x4 randomnesses =
            libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
                &state);
        if (!done0) {
          done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              eta,
              Eurydice_array_to_slice((size_t)136U, randomnesses.fst, uint8_t),
              &sampled0, out[0U]);
        }
        if (!done1) {
          done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              eta,
              Eurydice_array_to_slice((size_t)136U, randomnesses.snd, uint8_t),
              &sampled1, out[1U]);
        }
        if (!done2) {
          done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              eta,
              Eurydice_array_to_slice((size_t)136U, randomnesses.thd, uint8_t),
              &sampled2, out[2U]);
        }
        if (!done3) {
          done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              eta,
              Eurydice_array_to_slice((size_t)136U, randomnesses.f3, uint8_t),
              &sampled3, out[3U]);
        }
      }
    } else {
      uint8_t_136size_t__x4 randomnesses =
          libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
              &state);
      if (!done0) {
        done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            eta,
            Eurydice_array_to_slice((size_t)136U, randomnesses.fst, uint8_t),
            &sampled0, out[0U]);
      }
      if (!done1) {
        done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            eta,
            Eurydice_array_to_slice((size_t)136U, randomnesses.snd, uint8_t),
            &sampled1, out[1U]);
      }
      if (!done2) {
        done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            eta,
            Eurydice_array_to_slice((size_t)136U, randomnesses.thd, uint8_t),
            &sampled2, out[2U]);
      }
      if (!done3) {
        done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            eta,
            Eurydice_array_to_slice((size_t)136U, randomnesses.f3, uint8_t),
            &sampled3, out[3U]);
      }
    }
  }
  size_t max0 = (size_t)start_index + (size_t)4U;
  size_t max;
  if (Eurydice_slice_len(
          re, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d) < max0) {
    max = Eurydice_slice_len(
        re, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
  } else {
    max = max0;
  }
  for (size_t i = (size_t)start_index; i < max; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
        Eurydice_array_to_slice((size_t)263U, out[i0 % (size_t)4U], int32_t),
        &Eurydice_slice_index(
            re, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.sample_s1_and_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice seed,
    Eurydice_slice s1_s2) {
  size_t len = Eurydice_slice_len(
      s1_s2, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
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
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_ntt_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_c5(re->simd_units);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt_multiply_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *lhs,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, lhs->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_montgomery_multiply_c5(
        &lhs->simd_units[i0], &rhs->simd_units[i0]);
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_polynomial_add_c2_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *self,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, self->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_add_c5(&self->simd_units[i0],
                                            &rhs->simd_units[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.invert_ntt_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re) {
  libcrux_iot_ml_dsa_simd_portable_invert_ntt_montgomery_c5(re->simd_units);
}

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
    Eurydice_slice s1_ntt, Eurydice_slice s1_s2, Eurydice_slice result) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d product =
          Eurydice_slice_index(
              a_as_ntt, i1 * columns_in_a + j,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *);
      libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
          &product,
          &Eurydice_slice_index(
              s1_ntt, j, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      libcrux_iot_ml_dsa_polynomial_add_c2_08(
          &Eurydice_slice_index(
              result, i1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
          &product);
    }
  }
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               result, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&Eurydice_slice_index(
        result, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
    libcrux_iot_ml_dsa_polynomial_add_c2_08(
        &Eurydice_slice_index(
            result, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
        &Eurydice_slice_index(
            s1_s2, columns_in_a + i0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.power2round_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
    Eurydice_slice t, Eurydice_slice t1) {
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                t, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i <
         Eurydice_slice_len(
             Eurydice_array_to_slice(
                 (size_t)32U,
                 Eurydice_slice_index(
                     t, i1,
                     libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
                     libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
                     .simd_units,
                 libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
             libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
         i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_simd_portable_power2round_c5(
          &Eurydice_slice_index(
               t, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
               .simd_units[j],
          &Eurydice_slice_index(
               t1, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
               .simd_units[j]);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_t1_serialize_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, re->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit =
        &re->simd_units[i0];
    libcrux_iot_ml_dsa_simd_portable_t1_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice3(
            serialized,
            i0 *
                LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT,
            uint8_t *));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
    Eurydice_slice seed, Eurydice_slice t1,
    Eurydice_slice verification_key_serialized) {
  Eurydice_slice_copy(
      Eurydice_slice_subslice3(verification_key_serialized, (size_t)0U,
                               LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE,
                               uint8_t *),
      seed, uint8_t);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               t1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *ring_element =
        &Eurydice_slice_index(
            t1, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *);
    size_t offset = LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
                    i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE;
    libcrux_iot_ml_dsa_encoding_t1_serialize_08(
        ring_element,
        Eurydice_slice_subslice3(
            verification_key_serialized, offset,
            offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE,
            uint8_t *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 64
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_24(
    Eurydice_slice input, uint8_t *out) {
  libcrux_iot_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)64U, out, uint8_t), input);
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
    Eurydice_slice input, uint8_t *out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_24(input, out);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_error_serialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized) {
  size_t output_bytes_per_simd_unit =
      libcrux_iot_ml_dsa_encoding_error_chunk_size(eta);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, re->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit =
        &re->simd_units[i0];
    libcrux_iot_ml_dsa_simd_portable_error_serialize_c5(
        eta, simd_unit,
        Eurydice_slice_subslice3(serialized, i0 * output_bytes_per_simd_unit,
                                 (i0 + (size_t)1U) * output_bytes_per_simd_unit,
                                 uint8_t *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_t0_serialize_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, re->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit =
        &re->simd_units[i0];
    libcrux_iot_ml_dsa_simd_portable_t0_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice3(
            serialized,
            i0 * LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
            uint8_t *));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.signing_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t error_ring_element_size,
    Eurydice_slice seed_matrix, Eurydice_slice seed_signing,
    Eurydice_slice verification_key, Eurydice_slice s1_2, Eurydice_slice t0,
    Eurydice_slice signing_key_serialized) {
  size_t offset = (size_t)0U;
  Eurydice_slice_copy(
      Eurydice_slice_subslice3(
          signing_key_serialized, offset,
          offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t *),
      seed_matrix, uint8_t);
  offset = offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE;
  Eurydice_slice_copy(
      Eurydice_slice_subslice3(
          signing_key_serialized, offset,
          offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
          uint8_t *),
      seed_signing, uint8_t);
  offset = offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE;
  uint8_t verification_key_hash[64U] = {0U};
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
      verification_key, verification_key_hash);
  Eurydice_slice_copy(
      Eurydice_slice_subslice3(
          signing_key_serialized, offset,
          offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH,
          uint8_t *),
      Eurydice_array_to_slice((size_t)64U, verification_key_hash, uint8_t),
      uint8_t);
  offset =
      offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               s1_2, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_error_serialize_08(
        eta,
        &Eurydice_slice_index(
            s1_2, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
        Eurydice_slice_subslice3(signing_key_serialized, offset,
                                 offset + error_ring_element_size, uint8_t *));
    offset = offset + error_ring_element_size;
  }
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               t0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t _cloop_j = i;
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *ring_element =
        &Eurydice_slice_index(
            t0, _cloop_j,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *);
    libcrux_iot_ml_dsa_encoding_t0_serialize_08(
        ring_element,
        Eurydice_slice_subslice3(
            signing_key_serialized, offset,
            offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE,
            uint8_t *));
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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_generate_key_pair_c4(
    uint8_t randomness[32U], Eurydice_slice signing_key,
    Eurydice_slice verification_key) {
  uint8_t seed_expanded0[128U] = {0U};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  uint8_t buf[2U] = {
      (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A};
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, Eurydice_array_to_slice((size_t)2U, buf, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice seed_expanded = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_error_vectors = uu____1.fst;
  Eurydice_slice seed_for_signing = uu____1.snd;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d a_as_ntt[16U];
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U,
                   a_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice(
          (size_t)16U, a_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s1_s2[8U];
  KRML_MAYBE_FOR8(i, (size_t)0U, (size_t)8U, (size_t)1U,
                  s1_s2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA, seed_for_error_vectors,
      Eurydice_array_to_slice(
          (size_t)8U, s1_s2,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  t0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s1_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  s1_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)4U, s1_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_subslice3(
          s1_s2, (size_t)0U,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, s1_ntt,
                   libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_08(&s1_ntt[i0]);
  }
  libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
      Eurydice_array_to_slice(
          (size_t)16U, a_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)4U, s1_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)8U, s1_s2,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)4U, t0,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  t1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
      Eurydice_array_to_slice(
          (size_t)4U, t0,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)4U, t1,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
      seed_for_a,
      Eurydice_array_to_slice(
          (size_t)4U, t1,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      verification_key);
  libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing, verification_key,
      Eurydice_array_to_slice(
          (size_t)8U, s1_s2,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)4U, t0,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      signing_key);
}

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_generate_key_pair(
    uint8_t randomness[32U], uint8_t *signing_key, uint8_t *verification_key) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_generate_key_pair_c4(
      copy_of_randomness,
      Eurydice_array_to_slice((size_t)2560U, signing_key, uint8_t),
      Eurydice_array_to_slice((size_t)1312U, verification_key, uint8_t));
}

/**
 Generate an ML-DSA-44 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2
libcrux_iot_ml_dsa_ml_dsa_44_portable_generate_key_pair(
    uint8_t randomness[32U]) {
  uint8_t signing_key[2560U] = {0U};
  uint8_t verification_key[1312U] = {0U};
  uint8_t uu____0[32U];
  memcpy(uu____0, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_generate_key_pair(
      uu____0, signing_key, verification_key);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_signing_key[2560U];
  memcpy(copy_of_signing_key, signing_key, (size_t)2560U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 uu____2 =
      libcrux_iot_ml_dsa_types_new_f8_ff(copy_of_signing_key);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_verification_key[1312U];
  memcpy(copy_of_verification_key, verification_key,
         (size_t)1312U * sizeof(uint8_t));
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSAKeyPair_c2){
      .signing_key = uu____2,
      .verification_key =
          libcrux_iot_ml_dsa_types_new_e9_db(copy_of_verification_key)});
}

/**
 `context` must be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
core_result_Result_80 libcrux_iot_ml_dsa_pre_hash_new_c9(
    Eurydice_slice context, core_option_Option_30 pre_hash_oid) {
  if (!(Eurydice_slice_len(context, uint8_t) >
        LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    return (KRML_CLITERAL(core_result_Result_80){
        .tag = core_result_Ok,
        .val = {
            .case_Ok = {.context = context, .pre_hash_oid = pre_hash_oid}}});
  }
  return (KRML_CLITERAL(core_result_Result_80){
      .tag = core_result_Err,
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
core_option_Option_30 *libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self) {
  return &self->pre_hash_oid;
}

/**
 Returns the context, guaranteed to be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
Eurydice_slice libcrux_iot_ml_dsa_pre_hash_context_c9(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self) {
  return self->context;
}

KRML_MUSTINLINE bool libcrux_iot_ml_dsa_sample_inside_out_shuffle(
    Eurydice_slice randomness, size_t *out_index, uint64_t *signs,
    int32_t *result) {
  bool done = false;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(randomness, uint8_t);
       i++) {
    size_t _cloop_j = i;
    uint8_t *byte =
        &Eurydice_slice_index(randomness, _cloop_j, uint8_t, uint8_t *);
    if (!done) {
      size_t sample_at = (size_t)byte[0U];
      if (sample_at <= out_index[0U]) {
        result[out_index[0U]] = result[sample_at];
        out_index[0U] = out_index[0U] + (size_t)1U;
        result[sample_at] =
            (int32_t)1 - (int32_t)2 * (int32_t)(signs[0U] & 1ULL);
        signs[0U] = signs[0U] >> 1U;
      }
      size_t uu____0 = out_index[0U];
      done = uu____0 == Eurydice_slice_len(Eurydice_array_to_slice(
                                               (size_t)256U, result, int32_t),
                                           int32_t);
    }
  }
  return done;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_error_deserialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_slice serialized,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result) {
  size_t chunk_size = libcrux_iot_ml_dsa_encoding_error_chunk_size(eta);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, result->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_error_deserialize_c5(
        eta,
        Eurydice_slice_subslice3(serialized, i0 * chunk_size,
                                 (i0 + (size_t)1U) * chunk_size, uint8_t *),
        &result->simd_units[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.error.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t ring_element_size,
    Eurydice_slice serialized, Eurydice_slice ring_elements) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / ring_element_size; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * ring_element_size,
        i0 * ring_element_size + ring_element_size, uint8_t *);
    libcrux_iot_ml_dsa_encoding_error_deserialize_08(
        eta, bytes,
        &Eurydice_slice_index(
            ring_elements, i0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
    libcrux_iot_ml_dsa_ntt_ntt_08(&Eurydice_slice_index(
        ring_elements, i0,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_t0_deserialize_08(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, result->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_t0_deserialize_c5(
        Eurydice_slice_subslice3(
            serialized,
            i0 * LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
            uint8_t *),
        &result->simd_units[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.t0.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
    Eurydice_slice serialized, Eurydice_slice ring_elements) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) /
               LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE,
        i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE +
            LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE,
        uint8_t *);
    libcrux_iot_ml_dsa_encoding_t0_deserialize_08(
        bytes, &Eurydice_slice_index(
                   ring_elements, i0,
                   libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
                   libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
    libcrux_iot_ml_dsa_ntt_ntt_08(&Eurydice_slice_index(
        ring_elements, i0,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
    Eurydice_slice verification_key_hash,
    core_option_Option_e3 *domain_separation_context, Eurydice_slice message,
    uint8_t *message_representative) {
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake,
                                                       verification_key_hash);
  if (domain_separation_context->tag == core_option_Some) {
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        *domain_separation_context0 = &domain_separation_context->f0;
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *uu____0 = &shake;
    uint8_t buf0[1U] = {
        (uint8_t)core_option__core__option__Option_T__TraitClause_0___is_some(
            libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(
                domain_separation_context0),
            uint8_t[11U], bool)};
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        uu____0, Eurydice_array_to_slice((size_t)1U, buf0, uint8_t));
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *uu____1 = &shake;
    uint8_t buf[1U] = {(uint8_t)Eurydice_slice_len(
        libcrux_iot_ml_dsa_pre_hash_context_c9(domain_separation_context0),
        uint8_t)};
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        uu____1, Eurydice_array_to_slice((size_t)1U, buf, uint8_t));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake,
        libcrux_iot_ml_dsa_pre_hash_context_c9(domain_separation_context0));
    core_option_Option_30 *uu____2 =
        libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(domain_separation_context0);
    if (uu____2->tag == core_option_Some) {
      uint8_t *pre_hash_oid = uu____2->f0;
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice((size_t)11U, pre_hash_oid, uint8_t));
    }
  }
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(&shake, message);
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake,
      Eurydice_array_to_slice((size_t)64U, message_representative, uint8_t));
}

/**
A monomorphic instance of core.option.Option
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients[4size_t]

*/
typedef struct Option_16_s {
  core_option_Option_08_tags tag;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d f0[4U];
} Option_16;

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 576
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_1b(
    Eurydice_slice input, uint8_t *out) {
  libcrux_iot_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)576U, out, uint8_t), input);
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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_1b(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, uint8_t *out0, uint8_t *out1, uint8_t *out2,
    uint8_t *out3) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
    size_t gamma1_exponent, Eurydice_slice serialized,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, result->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_gamma1_deserialize_c5(
        Eurydice_slice_subslice3(
            serialized, i0 * (gamma1_exponent + (size_t)1U),
            (i0 + (size_t)1U) * (gamma1_exponent + (size_t)1U), uint8_t *),
        &result->simd_units[i0], gamma1_exponent);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 640
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(
    Eurydice_slice input, uint8_t *out) {
  libcrux_iot_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)640U, out, uint8_t), input);
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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_c8(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, uint8_t *out0, uint8_t *out1, uint8_t *out2,
    uint8_t *out3) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_1b(
    Eurydice_slice input, uint8_t *out) {
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c8(
    Eurydice_slice input, uint8_t *out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_c8(input, out);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_mask_ring_element_1b(
    uint8_t *seed,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result,
    size_t gamma1_exponent) {
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      uint8_t out[576U] = {0U};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_1b(
          Eurydice_array_to_slice((size_t)66U, seed, uint8_t), out);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out, uint8_t),
          result);
      break;
    }
    case 19U: {
      uint8_t out[640U] = {0U};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c8(
          Eurydice_array_to_slice((size_t)66U, seed, uint8_t), out);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out, uint8_t),
          result);
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
    size_t dimension, size_t gamma1_exponent, uint8_t *seed,
    uint16_t *domain_separator, Eurydice_slice mask) {
  uint8_t seed0[66U];
  libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice((size_t)64U, seed, uint8_t), domain_separator[0U],
      seed0);
  uint8_t seed1[66U];
  libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice((size_t)64U, seed, uint8_t),
      (uint32_t)domain_separator[0U] + 1U, seed1);
  uint8_t seed2[66U];
  libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice((size_t)64U, seed, uint8_t),
      (uint32_t)domain_separator[0U] + 2U, seed2);
  uint8_t seed3[66U];
  libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice((size_t)64U, seed, uint8_t),
      (uint32_t)domain_separator[0U] + 3U, seed3);
  domain_separator[0U] = (uint32_t)domain_separator[0U] + 4U;
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      uint8_t out0[576U] = {0U};
      uint8_t out1[576U] = {0U};
      uint8_t out2[576U] = {0U};
      uint8_t out3[576U] = {0U};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_1b(
          Eurydice_array_to_slice((size_t)66U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed3, uint8_t), out0, out1,
          out2, out3);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out0, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)0U,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out1, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)1U,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out2, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)2U,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out3, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)3U,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      break;
    }
    case 19U: {
      uint8_t out0[640U] = {0U};
      uint8_t out1[640U] = {0U};
      uint8_t out2[640U] = {0U};
      uint8_t out3[640U] = {0U};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_c8(
          Eurydice_array_to_slice((size_t)66U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed3, uint8_t), out0, out1,
          out2, out3);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out0, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)0U,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out1, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)1U,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out2, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)2U,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out3, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)3U,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
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
    uint8_t seed4[66U];
    libcrux_iot_ml_dsa_sample_add_error_domain_separator(
        Eurydice_array_to_slice((size_t)64U, seed, uint8_t),
        domain_separator[0U], seed4);
    domain_separator[0U] = (uint32_t)domain_separator[0U] + 1U;
    libcrux_iot_ml_dsa_sample_sample_mask_ring_element_1b(
        seed4,
        &Eurydice_slice_index(
            mask, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_slice matrix,
    Eurydice_slice mask, Eurydice_slice result) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d product =
          Eurydice_slice_index(
              mask, j, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *);
      libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
          &product,
          &Eurydice_slice_index(
              matrix, i1 * columns_in_a + j,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      libcrux_iot_ml_dsa_polynomial_add_c2_08(
          &Eurydice_slice_index(
              result, i1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
          &product);
    }
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&Eurydice_slice_index(
        result, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.decompose_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
    size_t dimension, int32_t gamma2, Eurydice_slice t, Eurydice_slice low,
    Eurydice_slice high) {
  for (size_t i0 = (size_t)0U; i0 < dimension; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i <
         Eurydice_slice_len(
             Eurydice_array_to_slice(
                 (size_t)32U,
                 Eurydice_slice_index(
                     low, (size_t)0U,
                     libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
                     libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
                     .simd_units,
                 libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
             libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
         i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_simd_portable_decompose_c5(
          gamma2,
          &Eurydice_slice_index(
               t, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
               .simd_units[j],
          &Eurydice_slice_index(
               low, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
               .simd_units[j],
          &Eurydice_slice_index(
               high, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
               .simd_units[j]);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.commitment.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_commitment_serialize_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized) {
  size_t output_bytes_per_simd_unit =
      Eurydice_slice_len(serialized, uint8_t) / ((size_t)8U * (size_t)4U);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, re->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit =
        &re->simd_units[i0];
    libcrux_iot_ml_dsa_simd_portable_commitment_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice3(serialized, i0 * output_bytes_per_simd_unit,
                                 (i0 + (size_t)1U) * output_bytes_per_simd_unit,
                                 uint8_t *));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.commitment.serialize_vector with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
    size_t ring_element_size, Eurydice_slice vector,
    Eurydice_slice serialized) {
  size_t offset = (size_t)0U;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               vector, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t _cloop_j = i;
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *ring_element =
        &Eurydice_slice_index(
            vector, _cloop_j,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *);
    libcrux_iot_ml_dsa_encoding_commitment_serialize_08(
        ring_element,
        Eurydice_slice_subslice3(serialized, offset, offset + ring_element_size,
                                 uint8_t *));
    offset = offset + ring_element_size;
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_challenge_ring_element with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
    Eurydice_slice seed, size_t number_of_ones,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re) {
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_a1(seed);
  uint8_t randomness0[136U];
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_a1(
      &state, randomness0);
  uint8_t ret[8U];
  core_result_Result_15 dst;
  Eurydice_slice_to_array2(&dst,
                           Eurydice_array_to_subslice3(randomness0, (size_t)0U,
                                                       (size_t)8U, uint8_t *),
                           Eurydice_slice, uint8_t[8U],
                           core_array_TryFromSliceError);
  core_result_unwrap_26_68(dst, ret);
  uint64_t signs = core_num__u64__from_le_bytes(ret);
  int32_t result[256U] = {0U};
  size_t out_index =
      Eurydice_slice_len(Eurydice_array_to_slice((size_t)256U, result, int32_t),
                         int32_t) -
      number_of_ones;
  bool done = libcrux_iot_ml_dsa_sample_inside_out_shuffle(
      Eurydice_array_to_subslice_from((size_t)136U, randomness0, (size_t)8U,
                                      uint8_t, size_t, uint8_t[]),
      &out_index, &signs, result);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[136U];
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_a1(
          &state, randomness);
      done = libcrux_iot_ml_dsa_sample_inside_out_shuffle(
          Eurydice_array_to_slice((size_t)136U, randomness, uint8_t),
          &out_index, &signs, result);
    }
  }
  libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
      Eurydice_array_to_slice((size_t)256U, result, int32_t), re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.vector_times_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
    Eurydice_slice vector,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *ring_element) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               vector, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
        &Eurydice_slice_index(
            vector, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
        ring_element);
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&Eurydice_slice_index(
        vector, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.add_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_add_vectors_08(
    size_t dimension, Eurydice_slice lhs, Eurydice_slice rhs) {
  for (size_t i = (size_t)0U; i < dimension; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_add_c2_08(
        &Eurydice_slice_index(
            lhs, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
        &Eurydice_slice_index(
            rhs, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_polynomial_subtract_c2_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *self,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, self->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_subtract_c5(&self->simd_units[i0],
                                                 &rhs->simd_units[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.subtract_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
    size_t dimension, Eurydice_slice lhs, Eurydice_slice rhs) {
  for (size_t i = (size_t)0U; i < dimension; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_subtract_c2_08(
        &Eurydice_slice_index(
            lhs, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
        &Eurydice_slice_index(
            rhs, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
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
KRML_MUSTINLINE bool libcrux_iot_ml_dsa_polynomial_infinity_norm_exceeds_c2_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *self,
    int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, self->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    bool uu____0;
    if (result) {
      uu____0 = true;
    } else {
      uu____0 = libcrux_iot_ml_dsa_simd_portable_infinity_norm_exceeds_c5(
          &self->simd_units[i0], bound);
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
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
    Eurydice_slice vector, int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               vector, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t _cloop_j = i;
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *ring_element =
        &Eurydice_slice_index(
            vector, _cloop_j,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *);
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
void libcrux_iot_ml_dsa_polynomial_to_i32_array_c2_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *self,
    int32_t ret[256U]) {
  int32_t result[256U] = {0U};
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, self->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit =
        &self->simd_units[i0];
    libcrux_iot_ml_dsa_simd_portable_to_coefficient_array_c5(
        simd_unit,
        Eurydice_array_to_subslice3(
            result,
            i0 * LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
            int32_t *));
  }
  memcpy(ret, result, (size_t)256U * sizeof(int32_t));
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.make_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE size_t libcrux_iot_ml_dsa_arithmetic_make_hint_08(
    Eurydice_slice low, Eurydice_slice high, int32_t gamma2,
    Eurydice_slice hint) {
  size_t true_hints = (size_t)0U;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d hint_simd =
      libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                low, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)32U, hint_simd.simd_units,
                     libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
                 libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
         i++) {
      size_t j = i;
      size_t one_hints_count = libcrux_iot_ml_dsa_simd_portable_compute_hint_c5(
          &Eurydice_slice_index(
               low, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
               .simd_units[j],
          &Eurydice_slice_index(
               high, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
               .simd_units[j],
          gamma2, &hint_simd.simd_units[j]);
      true_hints = true_hints + one_hints_count;
    }
    int32_t uu____0[256U];
    libcrux_iot_ml_dsa_polynomial_to_i32_array_c2_08(&hint_simd, uu____0);
    memcpy(Eurydice_slice_index(hint, i1, int32_t[256U], int32_t(*)[256U]),
           uu____0, (size_t)256U * sizeof(int32_t));
  }
  return true_hints;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_gamma1_serialize_08(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re,
    Eurydice_slice serialized, size_t gamma1_exponent) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, re->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit =
        &re->simd_units[i0];
    libcrux_iot_ml_dsa_simd_portable_gamma1_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice3(
            serialized, i0 * (gamma1_exponent + (size_t)1U),
            (i0 + (size_t)1U) * (gamma1_exponent + (size_t)1U), uint8_t *),
        gamma1_exponent);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_signature_serialize_08(
    Eurydice_slice commitment_hash, Eurydice_slice signer_response,
    Eurydice_slice hint, size_t commitment_hash_size, size_t columns_in_a,
    size_t rows_in_a, size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, Eurydice_slice signature) {
  size_t offset = (size_t)0U;
  Eurydice_slice_copy(
      Eurydice_slice_subslice3(signature, offset, offset + commitment_hash_size,
                               uint8_t *),
      commitment_hash, uint8_t);
  offset = offset + commitment_hash_size;
  for (size_t i = (size_t)0U; i < columns_in_a; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_gamma1_serialize_08(
        &Eurydice_slice_index(
            signer_response, i0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
        Eurydice_slice_subslice3(signature, offset,
                                 offset + gamma1_ring_element_size, uint8_t *),
        gamma1_exponent);
    offset = offset + gamma1_ring_element_size;
  }
  size_t true_hints_seen = (size_t)0U;
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i <
         Eurydice_slice_len(Eurydice_array_to_slice(
                                (size_t)256U,
                                Eurydice_slice_index(hint, i1, int32_t[256U],
                                                     int32_t(*)[256U]),
                                int32_t),
                            int32_t);
         i++) {
      size_t j = i;
      if (Eurydice_slice_index(hint, i1, int32_t[256U], int32_t(*)[256U])[j] ==
          (int32_t)1) {
        Eurydice_slice_index(signature, offset + true_hints_seen, uint8_t,
                             uint8_t *) = (uint8_t)j;
        true_hints_seen++;
      }
    }
    Eurydice_slice_index(signature, offset + max_ones_in_hint + i1, uint8_t,
                         uint8_t *) = (uint8_t)true_hints_seen;
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
KRML_MUSTINLINE core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
    Eurydice_slice signing_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context, uint8_t randomness[32U],
    uint8_t *signature) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice remaining_serialized0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_signing = uu____1.fst;
  Eurydice_slice remaining_serialized1 = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice verification_key_hash = uu____2.fst;
  Eurydice_slice remaining_serialized2 = uu____2.snd;
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice s1_serialized = uu____3.fst;
  Eurydice_slice remaining_serialized = uu____3.snd;
  Eurydice_slice_uint8_t_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice s2_serialized = uu____4.fst;
  Eurydice_slice t0_serialized = uu____4.snd;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s1_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  s1_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s2_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  s2_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t0_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  t0_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE,
      s1_serialized,
      Eurydice_array_to_slice(
          (size_t)4U, s1_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE,
      s2_serialized,
      Eurydice_array_to_slice(
          (size_t)4U, s2_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
      t0_serialized,
      Eurydice_array_to_slice(
          (size_t)4U, t0_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d matrix[16U];
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U,
                   matrix[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice(
          (size_t)16U, matrix,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  uint8_t message_representative[64U] = {0U};
  libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
      verification_key_hash, &domain_separation_context, message,
      message_representative);
  uint8_t mask_seed[64U] = {0U};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake0 =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake0,
                                                       seed_for_signing);
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake0, Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake0,
      Eurydice_array_to_slice((size_t)64U, message_representative, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake0, Eurydice_array_to_slice((size_t)64U, mask_seed, uint8_t));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  core_option_Option_85 commitment_hash0 = {.tag = core_option_None};
  Option_16 signer_response0 = {.tag = core_option_None};
  core_option_Option_a8 hint0 = {.tag = core_option_None};
  while (attempt < LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d mask[4U];
    KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                    mask[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d w0[4U];
    KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                    w0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d commitment[4U];
    KRML_MAYBE_FOR4(
        i, (size_t)0U, (size_t)4U, (size_t)1U,
        commitment[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT, mask_seed,
        &domain_separator_for_mask,
        Eurydice_array_to_slice(
            (size_t)4U, mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d a_x_mask[4U];
    KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                    a_x_mask[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d mask_ntt[4U];
    core_array__core__clone__Clone_for__Array_T__N___clone(
        (size_t)4U, mask, mask_ntt,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)4U, mask_ntt,
                     libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
                 libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
         i++) {
      size_t i0 = i;
      libcrux_iot_ml_dsa_ntt_ntt_08(&mask_ntt[i0]);
    }
    libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
        Eurydice_array_to_slice(
            (size_t)16U, matrix,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)4U, mask_ntt,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)4U, a_x_mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2,
        Eurydice_array_to_slice(
            (size_t)4U, a_x_mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)4U, w0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)4U, commitment,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    uint8_t commitment_hash_candidate[32U] = {0U};
    uint8_t commitment_serialized[768U] = {0U};
    libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
        LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE,
        Eurydice_array_to_slice(
            (size_t)4U, commitment,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice((size_t)768U, commitment_serialized, uint8_t));
    libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
        libcrux_iot_ml_dsa_hash_functions_portable_init_88();
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake,
        Eurydice_array_to_slice((size_t)64U, message_representative, uint8_t));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
        &shake,
        Eurydice_array_to_slice((size_t)768U, commitment_serialized, uint8_t));
    libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
        &shake, Eurydice_array_to_slice((size_t)32U, commitment_hash_candidate,
                                        uint8_t));
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d verifier_challenge =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
        Eurydice_array_to_slice((size_t)32U, commitment_hash_candidate,
                                uint8_t),
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
        challenge_times_s1[4U];
    core_array__core__clone__Clone_for__Array_T__N___clone(
        (size_t)4U, s1_as_ntt, challenge_times_s1,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
        challenge_times_s2[4U];
    core_array__core__clone__Clone_for__Array_T__N___clone(
        (size_t)4U, s2_as_ntt, challenge_times_s2,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice(
            (size_t)4U, challenge_times_s1,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice(
            (size_t)4U, challenge_times_s2,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_add_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
        Eurydice_array_to_slice(
            (size_t)4U, mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)4U, challenge_times_s1,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
        Eurydice_array_to_slice(
            (size_t)4U, w0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)4U, challenge_times_s2,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice(
                (size_t)4U, mask,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            ((int32_t)1 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA)) {
      if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
              Eurydice_array_to_slice(
                  (size_t)4U, w0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2 -
                  LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA)) {
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
            challenge_times_t0[4U];
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)4U, t0_as_ntt, challenge_times_t0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
        libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
            Eurydice_array_to_slice(
                (size_t)4U, challenge_times_t0,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            &verifier_challenge);
        if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
                Eurydice_array_to_slice(
                    (size_t)4U, challenge_times_t0,
                    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2)) {
          libcrux_iot_ml_dsa_matrix_add_vectors_08(
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
              Eurydice_array_to_slice(
                  (size_t)4U, w0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              Eurydice_array_to_slice(
                  (size_t)4U, challenge_times_t0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
          int32_t hint_candidate[4U][256U] = {{0U}};
          size_t ones_in_hint = libcrux_iot_ml_dsa_arithmetic_make_hint_08(
              Eurydice_array_to_slice(
                  (size_t)4U, w0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              Eurydice_array_to_slice(
                  (size_t)4U, commitment,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2,
              Eurydice_array_to_slice((size_t)4U, hint_candidate,
                                      int32_t[256U]));
          if (!(ones_in_hint >
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            /* Passing arrays by value in Rust generates a copy in C */
            uint8_t copy_of_commitment_hash_candidate[32U];
            memcpy(copy_of_commitment_hash_candidate, commitment_hash_candidate,
                   (size_t)32U * sizeof(uint8_t));
            core_option_Option_85 lit0;
            lit0.tag = core_option_Some;
            memcpy(lit0.f0, copy_of_commitment_hash_candidate,
                   (size_t)32U * sizeof(uint8_t));
            commitment_hash0 = lit0;
            /* Passing arrays by value in Rust generates a copy in C */
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
                copy_of_mask[4U];
            memcpy(
                copy_of_mask, mask,
                (size_t)4U *
                    sizeof(
                        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
            Option_16 lit1;
            lit1.tag = core_option_Some;
            memcpy(
                lit1.f0, copy_of_mask,
                (size_t)4U *
                    sizeof(
                        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
            signer_response0 = lit1;
            /* Passing arrays by value in Rust generates a copy in C */
            int32_t copy_of_hint_candidate[4U][256U];
            memcpy(copy_of_hint_candidate, hint_candidate,
                   (size_t)4U * sizeof(int32_t[256U]));
            core_option_Option_a8 lit;
            lit.tag = core_option_Some;
            memcpy(lit.f0, copy_of_hint_candidate,
                   (size_t)4U * sizeof(int32_t[256U]));
            hint0 = lit;
          }
        }
      }
    }
  }
  core_result_Result_87 uu____8;
  if (commitment_hash0.tag == core_option_None) {
    uu____8 = (KRML_CLITERAL(core_result_Result_87){
        .tag = core_result_Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    uint8_t commitment_hash1[32U];
    memcpy(commitment_hash1, commitment_hash0.f0,
           (size_t)32U * sizeof(uint8_t));
    uint8_t commitment_hash[32U];
    memcpy(commitment_hash, commitment_hash1, (size_t)32U * sizeof(uint8_t));
    if (signer_response0.tag == core_option_None) {
      uu____8 = (KRML_CLITERAL(core_result_Result_87){
          .tag = core_result_Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
          signer_response1[4U];
      memcpy(
          signer_response1, signer_response0.f0,
          (size_t)4U *
              sizeof(libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
          signer_response[4U];
      memcpy(
          signer_response, signer_response1,
          (size_t)4U *
              sizeof(libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      if (!(hint0.tag == core_option_None)) {
        int32_t hint1[4U][256U];
        memcpy(hint1, hint0.f0, (size_t)4U * sizeof(int32_t[256U]));
        int32_t hint[4U][256U];
        memcpy(hint, hint1, (size_t)4U * sizeof(int32_t[256U]));
        libcrux_iot_ml_dsa_encoding_signature_serialize_08(
            Eurydice_array_to_slice((size_t)32U, commitment_hash, uint8_t),
            Eurydice_array_to_slice(
                (size_t)4U, signer_response,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            Eurydice_array_to_slice((size_t)4U, hint, int32_t[256U]),
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT,
            LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice((size_t)2420U, signature, uint8_t));
        return (KRML_CLITERAL(core_result_Result_87){.tag = core_result_Ok});
      }
      uu____8 = (KRML_CLITERAL(core_result_Result_87){
          .tag = core_result_Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____8;
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
KRML_MUSTINLINE core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  core_result_Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(core_option_Option_30){.tag = core_option_None}));
  if (!(uu____0.tag == core_result_Ok)) {
    return (KRML_CLITERAL(core_result_Result_87){
        .tag = core_result_Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  Eurydice_slice uu____1 = signing_key;
  Eurydice_slice uu____2 = message;
  core_option_Option_e3 uu____3 = {.tag = core_option_Some,
                                   .f0 = domain_separation_context};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
      uu____1, uu____2, uu____3, copy_of_randomness, signature);
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
KRML_MUSTINLINE core_result_Result_ba
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_c4(Eurydice_slice signing_key,
                                                    Eurydice_slice message,
                                                    Eurydice_slice context,
                                                    uint8_t randomness[32U]) {
  libcrux_iot_ml_dsa_types_MLDSASignature_64 signature =
      libcrux_iot_ml_dsa_types_zero_ad_1a();
  Eurydice_slice uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  core_result_Result_87 uu____4 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
          uu____0, uu____1, uu____2, copy_of_randomness, signature.value);
  core_result_Result_ba uu____5;
  if (uu____4.tag == core_result_Ok) {
    uu____5 = (KRML_CLITERAL(core_result_Result_ba){
        .tag = core_result_Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____4.f0;
    uu____5 = (KRML_CLITERAL(core_result_Result_ba){.tag = core_result_Err,
                                                    .val = {.case_Err = e}});
  }
  return uu____5;
}

/**
 Sign.
*/
core_result_Result_ba
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)2560U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_c4(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_ba libcrux_iot_ml_dsa_ml_dsa_44_portable_sign(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t *uu____0 = libcrux_iot_ml_dsa_types_as_ref_f8_ff(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 Sign.
*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)2560U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
      uu____0, uu____1, uu____2, copy_of_randomness, signature);
}

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_87 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_mut(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U],
    uint8_t *signature) {
  uint8_t *uu____0 = libcrux_iot_ml_dsa_types_as_ref_f8_ff(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_mut(
      uu____0, uu____1, uu____2, copy_of_randomness, signature);
}

const uint8_t libcrux_iot_ml_dsa_pre_hash_SHAKE128_OID[11U] = {
    6U, 9U, 96U, 134U, 72U, 1U, 101U, 3U, 4U, 2U, 11U};

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
void libcrux_iot_ml_dsa_pre_hash_oid_0b(uint8_t ret[11U]) {
  memcpy(ret, libcrux_iot_ml_dsa_pre_hash_SHAKE128_OID,
         (size_t)11U * sizeof(uint8_t));
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
    Eurydice_slice message, Eurydice_slice output) {
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
KRML_MUSTINLINE core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_mut_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U],
    uint8_t *signature) {
  if (!(Eurydice_slice_len(context, uint8_t) >
        LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
    Eurydice_slice uu____0 = context;
    core_option_Option_30 lit;
    lit.tag = core_option_Some;
    uint8_t ret[11U];
    libcrux_iot_ml_dsa_pre_hash_oid_0b(ret);
    memcpy(lit.f0, ret, (size_t)11U * sizeof(uint8_t));
    core_result_Result_80 uu____1 =
        libcrux_iot_ml_dsa_pre_hash_new_c9(uu____0, lit);
    if (!(uu____1.tag == core_result_Ok)) {
      return (KRML_CLITERAL(core_result_Result_87){
          .tag = core_result_Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc =
        uu____1.val.case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        domain_separation_context = dsc;
    Eurydice_slice uu____2 = signing_key;
    Eurydice_slice uu____3 = pre_hash_buffer;
    core_option_Option_e3 uu____4 = {.tag = core_option_Some,
                                     .f0 = domain_separation_context};
    /* Passing arrays by value in Rust generates a copy in C */
    uint8_t copy_of_randomness[32U];
    memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
    return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
        uu____2, uu____3, uu____4, copy_of_randomness, signature);
  }
  return (KRML_CLITERAL(core_result_Result_87){
      .tag = core_result_Err,
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
KRML_MUSTINLINE core_result_Result_ba
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]) {
  libcrux_iot_ml_dsa_types_MLDSASignature_64 signature =
      libcrux_iot_ml_dsa_types_zero_ad_1a();
  Eurydice_slice uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 = pre_hash_buffer;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  core_result_Result_87 uu____5 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_mut_36(
          uu____0, uu____1, uu____2, uu____3, copy_of_randomness,
          signature.value);
  core_result_Result_ba uu____6;
  if (uu____5.tag == core_result_Ok) {
    uu____6 = (KRML_CLITERAL(core_result_Result_ba){
        .tag = core_result_Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____5.f0;
    uu____6 = (KRML_CLITERAL(core_result_Result_ba){.tag = core_result_Err,
                                                    .val = {.case_Err = e}});
  }
  return uu____6;
}

/**
 Sign (pre-hashed).
*/
core_result_Result_ba
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_pre_hashed_shake128(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)2560U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 = pre_hash_buffer;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_36(
      uu____0, uu____1, uu____2, uu____3, copy_of_randomness);
}

/**
 Generate a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_ba
libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_pre_hashed_shake128(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t pre_hash_buffer[32U] = {0U};
  uint8_t *uu____0 = libcrux_iot_ml_dsa_types_as_ref_f8_ff(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 =
      Eurydice_array_to_slice((size_t)32U, pre_hash_buffer, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3, copy_of_randomness);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t1_deserialize_08(
    Eurydice_slice serialized,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *result) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, result->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_t1_deserialize_c5(
        Eurydice_slice_subslice3(
            serialized, i0 * LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW,
            (i0 + (size_t)1U) *
                LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW,
            uint8_t *),
        &result->simd_units[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.deserialize with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
    size_t rows_in_a, size_t verification_key_size, Eurydice_slice serialized,
    Eurydice_slice t1) {
  for (size_t i = (size_t)0U; i < rows_in_a; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_t1_deserialize_08(
        Eurydice_slice_subslice3(
            serialized,
            i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE,
            (i0 + (size_t)1U) *
                LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE,
            uint8_t *),
        &Eurydice_slice_index(
            t1, i0, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
    size_t columns_in_a, size_t rows_in_a, size_t commitment_hash_size,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, size_t signature_size, Eurydice_slice serialized,
    Eurydice_slice out_commitment_hash, Eurydice_slice out_signer_response,
    Eurydice_slice out_hint) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      serialized, commitment_hash_size, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice commitment_hash = uu____0.fst;
  Eurydice_slice rest_of_serialized = uu____0.snd;
  Eurydice_slice_copy(Eurydice_slice_subslice3(out_commitment_hash, (size_t)0U,
                                               commitment_hash_size, uint8_t *),
                      commitment_hash, uint8_t);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      rest_of_serialized, gamma1_ring_element_size * columns_in_a, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice signer_response_serialized = uu____1.fst;
  Eurydice_slice hint_serialized = uu____1.snd;
  for (size_t i = (size_t)0U; i < columns_in_a; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
        gamma1_exponent,
        Eurydice_slice_subslice3(
            signer_response_serialized, i0 * gamma1_ring_element_size,
            (i0 + (size_t)1U) * gamma1_ring_element_size, uint8_t *),
        &Eurydice_slice_index(
            out_signer_response, i0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
  }
  size_t previous_true_hints_seen = (size_t)0U;
  size_t i0 = (size_t)0U;
  bool malformed_hint = false;
  while (true) {
    if (malformed_hint) {
      break;
    } else if (i0 < rows_in_a) {
      size_t current_true_hints_seen = (size_t)Eurydice_slice_index(
          hint_serialized, max_ones_in_hint + i0, uint8_t, uint8_t *);
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
            if (Eurydice_slice_index(hint_serialized, j, uint8_t, uint8_t *) <=
                Eurydice_slice_index(hint_serialized, j - (size_t)1U, uint8_t,
                                     uint8_t *)) {
              malformed_hint = true;
            }
          }
          if (!malformed_hint) {
            libcrux_iot_ml_dsa_encoding_signature_set_hint(
                out_hint, i0,
                (size_t)Eurydice_slice_index(hint_serialized, j, uint8_t,
                                             uint8_t *));
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
    if (!(Eurydice_slice_index(hint_serialized, j, uint8_t, uint8_t *) != 0U)) {
      continue;
    }
    malformed_hint = true;
    break;
  }
  if (!malformed_hint) {
    return (KRML_CLITERAL(core_result_Result_5c){.tag = core_result_Ok});
  }
  return (KRML_CLITERAL(core_result_Result_5c){
      .tag = core_result_Err,
      .f0 = libcrux_iot_ml_dsa_types_VerificationError_MalformedHintError});
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_ring_element_08(
    Eurydice_slice seed, uint8_t_x2 indices,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *out,
    uint8_t *rand_stack, uint8_t *rand_block, int32_t *tmp_stack) {
  uint8_t domain_separated_seed[34U];
  libcrux_iot_ml_dsa_sample_add_domain_separator(seed, indices,
                                                 domain_separated_seed);
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_b5(
          Eurydice_array_to_slice((size_t)34U, domain_separated_seed, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_b5(
      &state, rand_stack);
  size_t sampled = (size_t)0U;
  bool done =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          Eurydice_array_to_slice((size_t)840U, rand_stack, uint8_t), &sampled,
          tmp_stack);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_b5(
          &state, rand_block);
      if (!done) {
        done =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice((size_t)168U, rand_block, uint8_t),
                &sampled, tmp_stack);
      }
    }
  }
  libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
      Eurydice_array_to_slice((size_t)263U, tmp_stack, int32_t), out);
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce with const
generics
- SHIFT_BY= 13
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_84(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)8U, simd_unit->values, int32_t),
               int32_t);
       i++) {
    size_t i0 = i;
    simd_unit->values[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(
            simd_unit->values[i0] << (uint32_t)(int32_t)13);
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
void libcrux_iot_ml_dsa_simd_portable_shift_left_then_reduce_c5_84(
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients *simd_unit) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_84(
      simd_unit);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.shift_left_then_reduce
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics
- SHIFT_BY= 13
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_shift_left_then_reduce_41(
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, re->simd_units,
                   libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
               libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_shift_left_then_reduce_c5_84(
        &re->simd_units[i0]);
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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_slice seed,
    uint8_t *rand_stack, uint8_t *rand_block, int32_t *tmp_stack,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *poly_slot,
    Eurydice_slice signer_response,
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
        *verifier_challenge_as_ntt,
    Eurydice_slice t1) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d inner_result =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_sample_sample_ring_element_08(
          seed,
          (KRML_CLITERAL(uint8_t_x2){.fst = (uint8_t)i1, .snd = (uint8_t)j}),
          poly_slot, rand_stack, rand_block, tmp_stack);
      libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
          poly_slot,
          &Eurydice_slice_index(
              signer_response, j,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
      libcrux_iot_ml_dsa_polynomial_add_c2_08(&inner_result, poly_slot);
    }
    libcrux_iot_ml_dsa_arithmetic_shift_left_then_reduce_41(
        &Eurydice_slice_index(
            t1, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
    libcrux_iot_ml_dsa_ntt_ntt_08(&Eurydice_slice_index(
        t1, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
    libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
        &Eurydice_slice_index(
            t1, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
        verifier_challenge_as_ntt);
    libcrux_iot_ml_dsa_polynomial_subtract_c2_08(
        &inner_result,
        &Eurydice_slice_index(
            t1, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
    Eurydice_slice_index(
        t1, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *) =
        inner_result;
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&Eurydice_slice_index(
        t1, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.use_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_use_hint_08(
    int32_t gamma2, Eurydice_slice hint, Eurydice_slice re_vector) {
  for (size_t i0 = (size_t)0U;
       i0 <
       Eurydice_slice_len(
           re_vector, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i0++) {
    size_t i1 = i0;
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d tmp =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
        Eurydice_array_to_slice(
            (size_t)256U,
            Eurydice_slice_index(hint, i1, int32_t[256U], int32_t(*)[256U]),
            int32_t),
        &tmp);
    for (size_t i = (size_t)0U;
         i <
         Eurydice_slice_len(
             Eurydice_array_to_slice(
                 (size_t)32U,
                 Eurydice_slice_index(
                     re_vector, (size_t)0U,
                     libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
                     libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
                     .simd_units,
                 libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients),
             libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients);
         i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_simd_portable_use_hint_c5(
          gamma2,
          &Eurydice_slice_index(
               re_vector, i1,
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *)
               .simd_units[j],
          &tmp.simd_units[j]);
    }
    Eurydice_slice_index(
        re_vector, i1, libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *) = tmp;
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
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
    uint8_t *verification_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context,
    uint8_t *signature_serialized) {
  uint8_t rand_stack[840U] = {0U};
  uint8_t rand_block[168U] = {0U};
  int32_t tmp_stack[263U] = {0U};
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d poly_slot =
      libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)1312U, verification_key, uint8_t),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice t1_serialized = uu____0.snd;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  t1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_VERIFICATION_KEY_SIZE,
      t1_serialized,
      Eurydice_array_to_slice(
          (size_t)4U, t1,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  uint8_t deserialized_commitment_hash[32U] = {0U};
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
      deserialized_signer_response[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  deserialized_signer_response[i] =
                      libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  int32_t deserialized_hint[4U][256U] = {{0U}};
  core_result_Result_5c uu____1 =
      libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT,
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_GAMMA1_RING_ELEMENT_SIZE,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT,
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_SIGNATURE_SIZE,
          Eurydice_array_to_slice((size_t)2420U, signature_serialized, uint8_t),
          Eurydice_array_to_slice((size_t)32U, deserialized_commitment_hash,
                                  uint8_t),
          Eurydice_array_to_slice(
              (size_t)4U, deserialized_signer_response,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
          Eurydice_array_to_slice((size_t)4U, deserialized_hint,
                                  int32_t[256U]));
  core_result_Result_5c uu____2;
  if (uu____1.tag == core_result_Ok) {
    if (libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice(
                (size_t)4U, deserialized_signer_response,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            ((int32_t)2 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA)) {
      uu____2 = (KRML_CLITERAL(core_result_Result_5c){
          .tag = core_result_Err,
          .f0 =
              libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      uint8_t verification_key_hash[64U] = {0U};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
          Eurydice_array_to_slice((size_t)1312U, verification_key, uint8_t),
          verification_key_hash);
      uint8_t message_representative[64U] = {0U};
      libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
          Eurydice_array_to_slice((size_t)64U, verification_key_hash, uint8_t),
          &domain_separation_context, message, message_representative);
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
          verifier_challenge = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
      libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
          Eurydice_array_to_slice((size_t)32U, deserialized_commitment_hash,
                                  uint8_t),
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)4U, deserialized_signer_response,
                       libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
                   libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
           i++) {
        size_t i0 = i;
        libcrux_iot_ml_dsa_ntt_ntt_08(&deserialized_signer_response[i0]);
      }
      libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A, seed_for_a,
          rand_stack, rand_block, tmp_stack, &poly_slot,
          Eurydice_array_to_slice(
              (size_t)4U, deserialized_signer_response,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
          &verifier_challenge,
          Eurydice_array_to_slice(
              (size_t)4U, t1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      uint8_t recomputed_commitment_hash[32U] = {0U};
      libcrux_iot_ml_dsa_arithmetic_use_hint_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2,
          Eurydice_array_to_slice((size_t)4U, deserialized_hint, int32_t[256U]),
          Eurydice_array_to_slice(
              (size_t)4U, t1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      uint8_t commitment_serialized[768U] = {0U};
      libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE,
          Eurydice_array_to_slice(
              (size_t)4U, t1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
          Eurydice_array_to_slice((size_t)768U, commitment_serialized,
                                  uint8_t));
      libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
          libcrux_iot_ml_dsa_hash_functions_portable_init_88();
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice((size_t)64U, message_representative,
                                          uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
          &shake, Eurydice_array_to_slice((size_t)768U, commitment_serialized,
                                          uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
          &shake, Eurydice_array_to_slice((size_t)32U,
                                          recomputed_commitment_hash, uint8_t));
      if (Eurydice_array_eq((size_t)32U, deserialized_commitment_hash,
                            recomputed_commitment_hash, uint8_t)) {
        uu____2 = (KRML_CLITERAL(core_result_Result_5c){.tag = core_result_Ok});
      } else {
        uu____2 = (KRML_CLITERAL(core_result_Result_5c){
            .tag = core_result_Err,
            .f0 =
                libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_iot_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 =
        (KRML_CLITERAL(core_result_Result_5c){.tag = core_result_Err, .f0 = e});
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
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_c4(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, uint8_t *signature_serialized) {
  core_result_Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(core_option_Option_30){.tag = core_option_None}));
  if (!(uu____0.tag == core_result_Ok)) {
    return (KRML_CLITERAL(core_result_Result_5c){
        .tag = core_result_Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
      verification_key_serialized, message,
      (KRML_CLITERAL(core_option_Option_e3){.tag = core_option_Some,
                                            .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify.
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_c4(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_5c libcrux_iot_ml_dsa_ml_dsa_44_portable_verify(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_iot_ml_dsa_types_MLDSASignature_64 *signature) {
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
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_pre_hashed_36(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, Eurydice_slice pre_hash_buffer,
    uint8_t *signature_serialized) {
  libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
  Eurydice_slice uu____0 = context;
  core_option_Option_30 lit;
  lit.tag = core_option_Some;
  uint8_t ret[11U];
  libcrux_iot_ml_dsa_pre_hash_oid_0b(ret);
  memcpy(lit.f0, ret, (size_t)11U * sizeof(uint8_t));
  core_result_Result_80 uu____1 =
      libcrux_iot_ml_dsa_pre_hash_new_c9(uu____0, lit);
  if (!(uu____1.tag == core_result_Ok)) {
    return (KRML_CLITERAL(core_result_Result_5c){
        .tag = core_result_Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____1.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
      verification_key_serialized, pre_hash_buffer,
      (KRML_CLITERAL(core_option_Option_e3){.tag = core_option_Some,
                                            .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify_pre_hashed_shake128(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_pre_hashed_36(
      verification_key, message, context, pre_hash_buffer, signature);
}

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
    libcrux_iot_ml_dsa_types_MLDSASignature_64 *signature) {
  uint8_t pre_hash_buffer[32U] = {0U};
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify_pre_hashed_shake128(
      libcrux_iot_ml_dsa_types_as_ref_e9_db(verification_key), message, context,
      Eurydice_array_to_slice((size_t)32U, pre_hash_buffer, uint8_t),
      libcrux_iot_ml_dsa_types_as_ref_ad_1a(signature));
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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_c4(
    uint8_t randomness[32U], Eurydice_slice signing_key,
    Eurydice_slice verification_key) {
  uint8_t seed_expanded0[128U] = {0U};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  uint8_t buf[2U] = {
      (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A};
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, Eurydice_array_to_slice((size_t)2U, buf, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice seed_expanded = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_error_vectors = uu____1.fst;
  Eurydice_slice seed_for_signing = uu____1.snd;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d a_as_ntt[30U];
  for (size_t i = (size_t)0U; i < (size_t)30U; i++) {
    a_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice(
          (size_t)30U, a_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s1_s2[11U];
  KRML_MAYBE_FOR11(i, (size_t)0U, (size_t)11U, (size_t)1U,
                   s1_s2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA, seed_for_error_vectors,
      Eurydice_array_to_slice(
          (size_t)11U, s1_s2,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t0[6U];
  KRML_MAYBE_FOR6(i, (size_t)0U, (size_t)6U, (size_t)1U,
                  t0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s1_ntt[5U];
  KRML_MAYBE_FOR5(i, (size_t)0U, (size_t)5U, (size_t)1U,
                  s1_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)5U, s1_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_subslice3(
          s1_s2, (size_t)0U,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)5U, s1_ntt,
                   libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_08(&s1_ntt[i0]);
  }
  libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      Eurydice_array_to_slice(
          (size_t)30U, a_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)5U, s1_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)11U, s1_s2,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)6U, t0,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t1[6U];
  KRML_MAYBE_FOR6(i, (size_t)0U, (size_t)6U, (size_t)1U,
                  t1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
      Eurydice_array_to_slice(
          (size_t)6U, t0,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)6U, t1,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
      seed_for_a,
      Eurydice_array_to_slice(
          (size_t)6U, t1,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      verification_key);
  libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing, verification_key,
      Eurydice_array_to_slice(
          (size_t)11U, s1_s2,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)6U, t0,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      signing_key);
}

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
    uint8_t randomness[32U], uint8_t *signing_key, uint8_t *verification_key) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_c4(
      copy_of_randomness,
      Eurydice_array_to_slice((size_t)4032U, signing_key, uint8_t),
      Eurydice_array_to_slice((size_t)1952U, verification_key, uint8_t));
}

/**
 Generate an ML-DSA-65 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_06
libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair(
    uint8_t randomness[32U]) {
  uint8_t signing_key[4032U] = {0U};
  uint8_t verification_key[1952U] = {0U};
  uint8_t uu____0[32U];
  memcpy(uu____0, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
      uu____0, signing_key, verification_key);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_signing_key[4032U];
  memcpy(copy_of_signing_key, signing_key, (size_t)4032U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_types_MLDSASigningKey_22 uu____2 =
      libcrux_iot_ml_dsa_types_new_f8_09(copy_of_signing_key);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_verification_key[1952U];
  memcpy(copy_of_verification_key, verification_key,
         (size_t)1952U * sizeof(uint8_t));
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSAKeyPair_06){
      .signing_key = uu____2,
      .verification_key =
          libcrux_iot_ml_dsa_types_new_e9_97(copy_of_verification_key)});
}

/**
 Generate an ML-DSA-65 Key Pair
*/
void libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair_mut(
    uint8_t randomness[32U], uint8_t *signing_key, uint8_t *verification_key) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
      copy_of_randomness, signing_key, verification_key);
}

/**
A monomorphic instance of core.option.Option
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients[5size_t]

*/
typedef struct Option_88_s {
  core_option_Option_08_tags tag;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d f0[5U];
} Option_88;

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
KRML_MUSTINLINE core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
    Eurydice_slice signing_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context, uint8_t randomness[32U],
    uint8_t *signature) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice remaining_serialized0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_signing = uu____1.fst;
  Eurydice_slice remaining_serialized1 = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice verification_key_hash = uu____2.fst;
  Eurydice_slice remaining_serialized2 = uu____2.snd;
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice s1_serialized = uu____3.fst;
  Eurydice_slice remaining_serialized = uu____3.snd;
  Eurydice_slice_uint8_t_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice s2_serialized = uu____4.fst;
  Eurydice_slice t0_serialized = uu____4.snd;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s1_as_ntt[5U];
  KRML_MAYBE_FOR5(i, (size_t)0U, (size_t)5U, (size_t)1U,
                  s1_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s2_as_ntt[6U];
  KRML_MAYBE_FOR6(i, (size_t)0U, (size_t)6U, (size_t)1U,
                  s2_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t0_as_ntt[6U];
  KRML_MAYBE_FOR6(i, (size_t)0U, (size_t)6U, (size_t)1U,
                  t0_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      s1_serialized,
      Eurydice_array_to_slice(
          (size_t)5U, s1_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      s2_serialized,
      Eurydice_array_to_slice(
          (size_t)6U, s2_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
      t0_serialized,
      Eurydice_array_to_slice(
          (size_t)6U, t0_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d matrix[30U];
  for (size_t i = (size_t)0U; i < (size_t)30U; i++) {
    matrix[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice(
          (size_t)30U, matrix,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  uint8_t message_representative[64U] = {0U};
  libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
      verification_key_hash, &domain_separation_context, message,
      message_representative);
  uint8_t mask_seed[64U] = {0U};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake0 =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake0,
                                                       seed_for_signing);
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake0, Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake0,
      Eurydice_array_to_slice((size_t)64U, message_representative, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake0, Eurydice_array_to_slice((size_t)64U, mask_seed, uint8_t));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  core_option_Option_67 commitment_hash0 = {.tag = core_option_None};
  Option_88 signer_response0 = {.tag = core_option_None};
  core_option_Option_f0 hint0 = {.tag = core_option_None};
  while (attempt < LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d mask[5U];
    KRML_MAYBE_FOR5(i, (size_t)0U, (size_t)5U, (size_t)1U,
                    mask[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d w0[6U];
    KRML_MAYBE_FOR6(i, (size_t)0U, (size_t)6U, (size_t)1U,
                    w0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d commitment[6U];
    KRML_MAYBE_FOR6(
        i, (size_t)0U, (size_t)6U, (size_t)1U,
        commitment[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT, mask_seed,
        &domain_separator_for_mask,
        Eurydice_array_to_slice(
            (size_t)5U, mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d a_x_mask[6U];
    KRML_MAYBE_FOR6(i, (size_t)0U, (size_t)6U, (size_t)1U,
                    a_x_mask[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d mask_ntt[5U];
    core_array__core__clone__Clone_for__Array_T__N___clone(
        (size_t)5U, mask, mask_ntt,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)5U, mask_ntt,
                     libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
                 libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
         i++) {
      size_t i0 = i;
      libcrux_iot_ml_dsa_ntt_ntt_08(&mask_ntt[i0]);
    }
    libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        Eurydice_array_to_slice(
            (size_t)30U, matrix,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)5U, mask_ntt,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)6U, a_x_mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
        Eurydice_array_to_slice(
            (size_t)6U, a_x_mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)6U, w0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)6U, commitment,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    uint8_t commitment_hash_candidate[48U] = {0U};
    uint8_t commitment_serialized[768U] = {0U};
    libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
        LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE,
        Eurydice_array_to_slice(
            (size_t)6U, commitment,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice((size_t)768U, commitment_serialized, uint8_t));
    libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
        libcrux_iot_ml_dsa_hash_functions_portable_init_88();
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake,
        Eurydice_array_to_slice((size_t)64U, message_representative, uint8_t));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
        &shake,
        Eurydice_array_to_slice((size_t)768U, commitment_serialized, uint8_t));
    libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
        &shake, Eurydice_array_to_slice((size_t)48U, commitment_hash_candidate,
                                        uint8_t));
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d verifier_challenge =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
        Eurydice_array_to_slice((size_t)48U, commitment_hash_candidate,
                                uint8_t),
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
        challenge_times_s1[5U];
    core_array__core__clone__Clone_for__Array_T__N___clone(
        (size_t)5U, s1_as_ntt, challenge_times_s1,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
        challenge_times_s2[6U];
    core_array__core__clone__Clone_for__Array_T__N___clone(
        (size_t)6U, s2_as_ntt, challenge_times_s2,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice(
            (size_t)5U, challenge_times_s1,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice(
            (size_t)6U, challenge_times_s2,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_add_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        Eurydice_array_to_slice(
            (size_t)5U, mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)5U, challenge_times_s1,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        Eurydice_array_to_slice(
            (size_t)6U, w0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)6U, challenge_times_s2,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice(
                (size_t)5U, mask,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            ((int32_t)1 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
      if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
              Eurydice_array_to_slice(
                  (size_t)6U, w0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2 -
                  LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
            challenge_times_t0[6U];
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)6U, t0_as_ntt, challenge_times_t0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
        libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
            Eurydice_array_to_slice(
                (size_t)6U, challenge_times_t0,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            &verifier_challenge);
        if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
                Eurydice_array_to_slice(
                    (size_t)6U, challenge_times_t0,
                    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2)) {
          libcrux_iot_ml_dsa_matrix_add_vectors_08(
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
              Eurydice_array_to_slice(
                  (size_t)6U, w0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              Eurydice_array_to_slice(
                  (size_t)6U, challenge_times_t0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
          int32_t hint_candidate[6U][256U] = {{0U}};
          size_t ones_in_hint = libcrux_iot_ml_dsa_arithmetic_make_hint_08(
              Eurydice_array_to_slice(
                  (size_t)6U, w0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              Eurydice_array_to_slice(
                  (size_t)6U, commitment,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
              Eurydice_array_to_slice((size_t)6U, hint_candidate,
                                      int32_t[256U]));
          if (!(ones_in_hint >
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            /* Passing arrays by value in Rust generates a copy in C */
            uint8_t copy_of_commitment_hash_candidate[48U];
            memcpy(copy_of_commitment_hash_candidate, commitment_hash_candidate,
                   (size_t)48U * sizeof(uint8_t));
            core_option_Option_67 lit0;
            lit0.tag = core_option_Some;
            memcpy(lit0.f0, copy_of_commitment_hash_candidate,
                   (size_t)48U * sizeof(uint8_t));
            commitment_hash0 = lit0;
            /* Passing arrays by value in Rust generates a copy in C */
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
                copy_of_mask[5U];
            memcpy(
                copy_of_mask, mask,
                (size_t)5U *
                    sizeof(
                        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
            Option_88 lit1;
            lit1.tag = core_option_Some;
            memcpy(
                lit1.f0, copy_of_mask,
                (size_t)5U *
                    sizeof(
                        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
            signer_response0 = lit1;
            /* Passing arrays by value in Rust generates a copy in C */
            int32_t copy_of_hint_candidate[6U][256U];
            memcpy(copy_of_hint_candidate, hint_candidate,
                   (size_t)6U * sizeof(int32_t[256U]));
            core_option_Option_f0 lit;
            lit.tag = core_option_Some;
            memcpy(lit.f0, copy_of_hint_candidate,
                   (size_t)6U * sizeof(int32_t[256U]));
            hint0 = lit;
          }
        }
      }
    }
  }
  core_result_Result_87 uu____8;
  if (commitment_hash0.tag == core_option_None) {
    uu____8 = (KRML_CLITERAL(core_result_Result_87){
        .tag = core_result_Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    uint8_t commitment_hash1[48U];
    memcpy(commitment_hash1, commitment_hash0.f0,
           (size_t)48U * sizeof(uint8_t));
    uint8_t commitment_hash[48U];
    memcpy(commitment_hash, commitment_hash1, (size_t)48U * sizeof(uint8_t));
    if (signer_response0.tag == core_option_None) {
      uu____8 = (KRML_CLITERAL(core_result_Result_87){
          .tag = core_result_Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
          signer_response1[5U];
      memcpy(
          signer_response1, signer_response0.f0,
          (size_t)5U *
              sizeof(libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
          signer_response[5U];
      memcpy(
          signer_response, signer_response1,
          (size_t)5U *
              sizeof(libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      if (!(hint0.tag == core_option_None)) {
        int32_t hint1[6U][256U];
        memcpy(hint1, hint0.f0, (size_t)6U * sizeof(int32_t[256U]));
        int32_t hint[6U][256U];
        memcpy(hint, hint1, (size_t)6U * sizeof(int32_t[256U]));
        libcrux_iot_ml_dsa_encoding_signature_serialize_08(
            Eurydice_array_to_slice((size_t)48U, commitment_hash, uint8_t),
            Eurydice_array_to_slice(
                (size_t)5U, signer_response,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            Eurydice_array_to_slice((size_t)6U, hint, int32_t[256U]),
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT,
            LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice((size_t)3309U, signature, uint8_t));
        return (KRML_CLITERAL(core_result_Result_87){.tag = core_result_Ok});
      }
      uu____8 = (KRML_CLITERAL(core_result_Result_87){
          .tag = core_result_Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____8;
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
KRML_MUSTINLINE core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  core_result_Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(core_option_Option_30){.tag = core_option_None}));
  if (!(uu____0.tag == core_result_Ok)) {
    return (KRML_CLITERAL(core_result_Result_87){
        .tag = core_result_Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  Eurydice_slice uu____1 = signing_key;
  Eurydice_slice uu____2 = message;
  core_option_Option_e3 uu____3 = {.tag = core_option_Some,
                                   .f0 = domain_separation_context};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
      uu____1, uu____2, uu____3, copy_of_randomness, signature);
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
KRML_MUSTINLINE core_result_Result_3e
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_c4(Eurydice_slice signing_key,
                                                    Eurydice_slice message,
                                                    Eurydice_slice context,
                                                    uint8_t randomness[32U]) {
  libcrux_iot_ml_dsa_types_MLDSASignature_8f signature =
      libcrux_iot_ml_dsa_types_zero_ad_fa();
  Eurydice_slice uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  core_result_Result_87 uu____4 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
          uu____0, uu____1, uu____2, copy_of_randomness, signature.value);
  core_result_Result_3e uu____5;
  if (uu____4.tag == core_result_Ok) {
    uu____5 = (KRML_CLITERAL(core_result_Result_3e){
        .tag = core_result_Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____4.f0;
    uu____5 = (KRML_CLITERAL(core_result_Result_3e){.tag = core_result_Err,
                                                    .val = {.case_Err = e}});
  }
  return uu____5;
}

/**
 Sign.
*/
core_result_Result_3e
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)4032U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_c4(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_3e libcrux_iot_ml_dsa_ml_dsa_65_portable_sign(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_22 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t *uu____0 = libcrux_iot_ml_dsa_types_as_ref_f8_09(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 Sign.
*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)4032U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
      uu____0, uu____1, uu____2, copy_of_randomness, signature);
}

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_87 libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  uint8_t *uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_mut(
      uu____0, uu____1, uu____2, copy_of_randomness, signature);
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
KRML_MUSTINLINE core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U],
    uint8_t *signature) {
  if (!(Eurydice_slice_len(context, uint8_t) >
        LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
    Eurydice_slice uu____0 = context;
    core_option_Option_30 lit;
    lit.tag = core_option_Some;
    uint8_t ret[11U];
    libcrux_iot_ml_dsa_pre_hash_oid_0b(ret);
    memcpy(lit.f0, ret, (size_t)11U * sizeof(uint8_t));
    core_result_Result_80 uu____1 =
        libcrux_iot_ml_dsa_pre_hash_new_c9(uu____0, lit);
    if (!(uu____1.tag == core_result_Ok)) {
      return (KRML_CLITERAL(core_result_Result_87){
          .tag = core_result_Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc =
        uu____1.val.case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        domain_separation_context = dsc;
    Eurydice_slice uu____2 = signing_key;
    Eurydice_slice uu____3 = pre_hash_buffer;
    core_option_Option_e3 uu____4 = {.tag = core_option_Some,
                                     .f0 = domain_separation_context};
    /* Passing arrays by value in Rust generates a copy in C */
    uint8_t copy_of_randomness[32U];
    memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
    return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
        uu____2, uu____3, uu____4, copy_of_randomness, signature);
  }
  return (KRML_CLITERAL(core_result_Result_87){
      .tag = core_result_Err,
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
KRML_MUSTINLINE core_result_Result_3e
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]) {
  libcrux_iot_ml_dsa_types_MLDSASignature_8f signature =
      libcrux_iot_ml_dsa_types_zero_ad_fa();
  Eurydice_slice uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 = pre_hash_buffer;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  core_result_Result_87 uu____5 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_36(
          uu____0, uu____1, uu____2, uu____3, copy_of_randomness,
          signature.value);
  core_result_Result_3e uu____6;
  if (uu____5.tag == core_result_Ok) {
    uu____6 = (KRML_CLITERAL(core_result_Result_3e){
        .tag = core_result_Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____5.f0;
    uu____6 = (KRML_CLITERAL(core_result_Result_3e){.tag = core_result_Err,
                                                    .val = {.case_Err = e}});
  }
  return uu____6;
}

/**
 Sign (pre-hashed).
*/
core_result_Result_3e
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_pre_hashed_shake128(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)4032U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 = pre_hash_buffer;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_36(
      uu____0, uu____1, uu____2, uu____3, copy_of_randomness);
}

/**
 Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_3e
libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_pre_hashed_shake128(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_22 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t pre_hash_buffer[32U] = {0U};
  uint8_t *uu____0 = libcrux_iot_ml_dsa_types_as_ref_f8_09(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 =
      Eurydice_array_to_slice((size_t)32U, pre_hash_buffer, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3, copy_of_randomness);
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
    uint8_t *verification_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context,
    uint8_t *signature_serialized) {
  uint8_t rand_stack[840U] = {0U};
  uint8_t rand_block[168U] = {0U};
  int32_t tmp_stack[263U] = {0U};
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d poly_slot =
      libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)1952U, verification_key, uint8_t),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice t1_serialized = uu____0.snd;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t1[6U];
  KRML_MAYBE_FOR6(i, (size_t)0U, (size_t)6U, (size_t)1U,
                  t1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_VERIFICATION_KEY_SIZE,
      t1_serialized,
      Eurydice_array_to_slice(
          (size_t)6U, t1,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  uint8_t deserialized_commitment_hash[48U] = {0U};
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
      deserialized_signer_response[5U];
  KRML_MAYBE_FOR5(i, (size_t)0U, (size_t)5U, (size_t)1U,
                  deserialized_signer_response[i] =
                      libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  int32_t deserialized_hint[6U][256U] = {{0U}};
  core_result_Result_5c uu____1 =
      libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT,
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNATURE_SIZE,
          Eurydice_array_to_slice((size_t)3309U, signature_serialized, uint8_t),
          Eurydice_array_to_slice((size_t)48U, deserialized_commitment_hash,
                                  uint8_t),
          Eurydice_array_to_slice(
              (size_t)5U, deserialized_signer_response,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
          Eurydice_array_to_slice((size_t)6U, deserialized_hint,
                                  int32_t[256U]));
  core_result_Result_5c uu____2;
  if (uu____1.tag == core_result_Ok) {
    if (libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice(
                (size_t)5U, deserialized_signer_response,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            ((int32_t)2 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
      uu____2 = (KRML_CLITERAL(core_result_Result_5c){
          .tag = core_result_Err,
          .f0 =
              libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      uint8_t verification_key_hash[64U] = {0U};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
          Eurydice_array_to_slice((size_t)1952U, verification_key, uint8_t),
          verification_key_hash);
      uint8_t message_representative[64U] = {0U};
      libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
          Eurydice_array_to_slice((size_t)64U, verification_key_hash, uint8_t),
          &domain_separation_context, message, message_representative);
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
          verifier_challenge = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
      libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
          Eurydice_array_to_slice((size_t)48U, deserialized_commitment_hash,
                                  uint8_t),
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)5U, deserialized_signer_response,
                       libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
                   libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
           i++) {
        size_t i0 = i;
        libcrux_iot_ml_dsa_ntt_ntt_08(&deserialized_signer_response[i0]);
      }
      libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
          rand_stack, rand_block, tmp_stack, &poly_slot,
          Eurydice_array_to_slice(
              (size_t)5U, deserialized_signer_response,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
          &verifier_challenge,
          Eurydice_array_to_slice(
              (size_t)6U, t1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      uint8_t recomputed_commitment_hash[48U] = {0U};
      libcrux_iot_ml_dsa_arithmetic_use_hint_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
          Eurydice_array_to_slice((size_t)6U, deserialized_hint, int32_t[256U]),
          Eurydice_array_to_slice(
              (size_t)6U, t1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      uint8_t commitment_serialized[768U] = {0U};
      libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE,
          Eurydice_array_to_slice(
              (size_t)6U, t1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
          Eurydice_array_to_slice((size_t)768U, commitment_serialized,
                                  uint8_t));
      libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
          libcrux_iot_ml_dsa_hash_functions_portable_init_88();
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice((size_t)64U, message_representative,
                                          uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
          &shake, Eurydice_array_to_slice((size_t)768U, commitment_serialized,
                                          uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
          &shake, Eurydice_array_to_slice((size_t)48U,
                                          recomputed_commitment_hash, uint8_t));
      if (Eurydice_array_eq((size_t)48U, deserialized_commitment_hash,
                            recomputed_commitment_hash, uint8_t)) {
        uu____2 = (KRML_CLITERAL(core_result_Result_5c){.tag = core_result_Ok});
      } else {
        uu____2 = (KRML_CLITERAL(core_result_Result_5c){
            .tag = core_result_Err,
            .f0 =
                libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_iot_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 =
        (KRML_CLITERAL(core_result_Result_5c){.tag = core_result_Err, .f0 = e});
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
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_c4(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, uint8_t *signature_serialized) {
  core_result_Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(core_option_Option_30){.tag = core_option_None}));
  if (!(uu____0.tag == core_result_Ok)) {
    return (KRML_CLITERAL(core_result_Result_5c){
        .tag = core_result_Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
      verification_key_serialized, message,
      (KRML_CLITERAL(core_option_Option_e3){.tag = core_option_Some,
                                            .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify.
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_c4(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_5c libcrux_iot_ml_dsa_ml_dsa_65_portable_verify(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_iot_ml_dsa_types_MLDSASignature_8f *signature) {
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
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_36(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, Eurydice_slice pre_hash_buffer,
    uint8_t *signature_serialized) {
  libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
  Eurydice_slice uu____0 = context;
  core_option_Option_30 lit;
  lit.tag = core_option_Some;
  uint8_t ret[11U];
  libcrux_iot_ml_dsa_pre_hash_oid_0b(ret);
  memcpy(lit.f0, ret, (size_t)11U * sizeof(uint8_t));
  core_result_Result_80 uu____1 =
      libcrux_iot_ml_dsa_pre_hash_new_c9(uu____0, lit);
  if (!(uu____1.tag == core_result_Ok)) {
    return (KRML_CLITERAL(core_result_Result_5c){
        .tag = core_result_Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____1.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
      verification_key_serialized, pre_hash_buffer,
      (KRML_CLITERAL(core_option_Option_e3){.tag = core_option_Some,
                                            .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify_pre_hashed_shake128(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_36(
      verification_key, message, context, pre_hash_buffer, signature);
}

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
    libcrux_iot_ml_dsa_types_MLDSASignature_8f *signature) {
  uint8_t pre_hash_buffer[32U] = {0U};
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify_pre_hashed_shake128(
      libcrux_iot_ml_dsa_types_as_ref_e9_97(verification_key), message, context,
      Eurydice_array_to_slice((size_t)32U, pre_hash_buffer, uint8_t),
      libcrux_iot_ml_dsa_types_as_ref_ad_fa(signature));
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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_generate_key_pair_c4(
    uint8_t randomness[32U], Eurydice_slice signing_key,
    Eurydice_slice verification_key) {
  uint8_t seed_expanded0[128U] = {0U};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  uint8_t buf[2U] = {
      (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A};
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, Eurydice_array_to_slice((size_t)2U, buf, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice seed_expanded = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_error_vectors = uu____1.fst;
  Eurydice_slice seed_for_signing = uu____1.snd;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d a_as_ntt[56U];
  for (size_t i = (size_t)0U; i < (size_t)56U; i++) {
    a_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice(
          (size_t)56U, a_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s1_s2[15U];
  KRML_MAYBE_FOR15(i, (size_t)0U, (size_t)15U, (size_t)1U,
                   s1_s2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA, seed_for_error_vectors,
      Eurydice_array_to_slice(
          (size_t)15U, s1_s2,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t0[8U];
  KRML_MAYBE_FOR8(i, (size_t)0U, (size_t)8U, (size_t)1U,
                  t0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s1_ntt[7U];
  KRML_MAYBE_FOR7(i, (size_t)0U, (size_t)7U, (size_t)1U,
                  s1_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)7U, s1_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_subslice3(
          s1_s2, (size_t)0U,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d *),
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)7U, s1_ntt,
                   libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
               libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_08(&s1_ntt[i0]);
  }
  libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
      Eurydice_array_to_slice(
          (size_t)56U, a_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)7U, s1_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)15U, s1_s2,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)8U, t0,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t1[8U];
  KRML_MAYBE_FOR8(i, (size_t)0U, (size_t)8U, (size_t)1U,
                  t1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
      Eurydice_array_to_slice(
          (size_t)8U, t0,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)8U, t1,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
      seed_for_a,
      Eurydice_array_to_slice(
          (size_t)8U, t1,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      verification_key);
  libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing, verification_key,
      Eurydice_array_to_slice(
          (size_t)15U, s1_s2,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      Eurydice_array_to_slice(
          (size_t)8U, t0,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
      signing_key);
}

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_generate_key_pair(
    uint8_t randomness[32U], uint8_t *signing_key, uint8_t *verification_key) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_generate_key_pair_c4(
      copy_of_randomness,
      Eurydice_array_to_slice((size_t)4896U, signing_key, uint8_t),
      Eurydice_array_to_slice((size_t)2592U, verification_key, uint8_t));
}

/**
 Generate an ML-DSA-87 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d
libcrux_iot_ml_dsa_ml_dsa_87_portable_generate_key_pair(
    uint8_t randomness[32U]) {
  uint8_t signing_key[4896U] = {0U};
  uint8_t verification_key[2592U] = {0U};
  uint8_t uu____0[32U];
  memcpy(uu____0, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_generate_key_pair(
      uu____0, signing_key, verification_key);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_signing_key[4896U];
  memcpy(copy_of_signing_key, signing_key, (size_t)4896U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 uu____2 =
      libcrux_iot_ml_dsa_types_new_f8_32(copy_of_signing_key);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_verification_key[2592U];
  memcpy(copy_of_verification_key, verification_key,
         (size_t)2592U * sizeof(uint8_t));
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSAKeyPair_2d){
      .signing_key = uu____2,
      .verification_key =
          libcrux_iot_ml_dsa_types_new_e9_d8(copy_of_verification_key)});
}

/**
A monomorphic instance of core.option.Option
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients[7size_t]

*/
typedef struct Option_63_s {
  core_option_Option_08_tags tag;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d f0[7U];
} Option_63;

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
KRML_MUSTINLINE core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
    Eurydice_slice signing_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context, uint8_t randomness[32U],
    uint8_t *signature) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice remaining_serialized0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_signing = uu____1.fst;
  Eurydice_slice remaining_serialized1 = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice verification_key_hash = uu____2.fst;
  Eurydice_slice remaining_serialized2 = uu____2.snd;
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice s1_serialized = uu____3.fst;
  Eurydice_slice remaining_serialized = uu____3.snd;
  Eurydice_slice_uint8_t_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice s2_serialized = uu____4.fst;
  Eurydice_slice t0_serialized = uu____4.snd;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s1_as_ntt[7U];
  KRML_MAYBE_FOR7(i, (size_t)0U, (size_t)7U, (size_t)1U,
                  s1_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d s2_as_ntt[8U];
  KRML_MAYBE_FOR8(i, (size_t)0U, (size_t)8U, (size_t)1U,
                  s2_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t0_as_ntt[8U];
  KRML_MAYBE_FOR8(i, (size_t)0U, (size_t)8U, (size_t)1U,
                  t0_as_ntt[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE,
      s1_serialized,
      Eurydice_array_to_slice(
          (size_t)7U, s1_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE,
      s2_serialized,
      Eurydice_array_to_slice(
          (size_t)8U, s2_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
      t0_serialized,
      Eurydice_array_to_slice(
          (size_t)8U, t0_as_ntt,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d matrix[56U];
  for (size_t i = (size_t)0U; i < (size_t)56U; i++) {
    matrix[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice(
          (size_t)56U, matrix,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  uint8_t message_representative[64U] = {0U};
  libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
      verification_key_hash, &domain_separation_context, message,
      message_representative);
  uint8_t mask_seed[64U] = {0U};
  libcrux_iot_sha3_keccak_KeccakXofState_c7 shake0 =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake0,
                                                       seed_for_signing);
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake0, Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake0,
      Eurydice_array_to_slice((size_t)64U, message_representative, uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake0, Eurydice_array_to_slice((size_t)64U, mask_seed, uint8_t));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  core_option_Option_880 commitment_hash0 = {.tag = core_option_None};
  Option_63 signer_response0 = {.tag = core_option_None};
  core_option_Option_d6 hint0 = {.tag = core_option_None};
  while (attempt < LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d mask[7U];
    KRML_MAYBE_FOR7(i, (size_t)0U, (size_t)7U, (size_t)1U,
                    mask[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d w0[8U];
    KRML_MAYBE_FOR8(i, (size_t)0U, (size_t)8U, (size_t)1U,
                    w0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d commitment[8U];
    KRML_MAYBE_FOR8(
        i, (size_t)0U, (size_t)8U, (size_t)1U,
        commitment[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT, mask_seed,
        &domain_separator_for_mask,
        Eurydice_array_to_slice(
            (size_t)7U, mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d a_x_mask[8U];
    KRML_MAYBE_FOR8(i, (size_t)0U, (size_t)8U, (size_t)1U,
                    a_x_mask[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d mask_ntt[7U];
    core_array__core__clone__Clone_for__Array_T__N___clone(
        (size_t)7U, mask, mask_ntt,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)7U, mask_ntt,
                     libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
                 libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
         i++) {
      size_t i0 = i;
      libcrux_iot_ml_dsa_ntt_ntt_08(&mask_ntt[i0]);
    }
    libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
        Eurydice_array_to_slice(
            (size_t)56U, matrix,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)7U, mask_ntt,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)8U, a_x_mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2,
        Eurydice_array_to_slice(
            (size_t)8U, a_x_mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)8U, w0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)8U, commitment,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    uint8_t commitment_hash_candidate[64U] = {0U};
    uint8_t commitment_serialized[1024U] = {0U};
    libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
        LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_RING_ELEMENT_SIZE,
        Eurydice_array_to_slice(
            (size_t)8U, commitment,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice((size_t)1024U, commitment_serialized, uint8_t));
    libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
        libcrux_iot_ml_dsa_hash_functions_portable_init_88();
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake,
        Eurydice_array_to_slice((size_t)64U, message_representative, uint8_t));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
        &shake,
        Eurydice_array_to_slice((size_t)1024U, commitment_serialized, uint8_t));
    libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
        &shake, Eurydice_array_to_slice((size_t)64U, commitment_hash_candidate,
                                        uint8_t));
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d verifier_challenge =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
        Eurydice_array_to_slice((size_t)64U, commitment_hash_candidate,
                                uint8_t),
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
        challenge_times_s1[7U];
    core_array__core__clone__Clone_for__Array_T__N___clone(
        (size_t)7U, s1_as_ntt, challenge_times_s1,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
        challenge_times_s2[8U];
    core_array__core__clone__Clone_for__Array_T__N___clone(
        (size_t)8U, s2_as_ntt, challenge_times_s2,
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice(
            (size_t)7U, challenge_times_s1,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        Eurydice_array_to_slice(
            (size_t)8U, challenge_times_s2,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_add_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
        Eurydice_array_to_slice(
            (size_t)7U, mask,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)7U, challenge_times_s1,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
        Eurydice_array_to_slice(
            (size_t)8U, w0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
        Eurydice_array_to_slice(
            (size_t)8U, challenge_times_s2,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
    if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice(
                (size_t)7U, mask,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            ((int32_t)1 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA)) {
      if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
              Eurydice_array_to_slice(
                  (size_t)8U, w0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2 -
                  LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA)) {
        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
            challenge_times_t0[8U];
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)8U, t0_as_ntt, challenge_times_t0,
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, void *);
        libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
            Eurydice_array_to_slice(
                (size_t)8U, challenge_times_t0,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            &verifier_challenge);
        if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
                Eurydice_array_to_slice(
                    (size_t)8U, challenge_times_t0,
                    libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2)) {
          libcrux_iot_ml_dsa_matrix_add_vectors_08(
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
              Eurydice_array_to_slice(
                  (size_t)8U, w0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              Eurydice_array_to_slice(
                  (size_t)8U, challenge_times_t0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
          int32_t hint_candidate[8U][256U] = {{0U}};
          size_t ones_in_hint = libcrux_iot_ml_dsa_arithmetic_make_hint_08(
              Eurydice_array_to_slice(
                  (size_t)8U, w0,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              Eurydice_array_to_slice(
                  (size_t)8U, commitment,
                  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2,
              Eurydice_array_to_slice((size_t)8U, hint_candidate,
                                      int32_t[256U]));
          if (!(ones_in_hint >
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            /* Passing arrays by value in Rust generates a copy in C */
            uint8_t copy_of_commitment_hash_candidate[64U];
            memcpy(copy_of_commitment_hash_candidate, commitment_hash_candidate,
                   (size_t)64U * sizeof(uint8_t));
            core_option_Option_880 lit0;
            lit0.tag = core_option_Some;
            memcpy(lit0.f0, copy_of_commitment_hash_candidate,
                   (size_t)64U * sizeof(uint8_t));
            commitment_hash0 = lit0;
            /* Passing arrays by value in Rust generates a copy in C */
            libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
                copy_of_mask[7U];
            memcpy(
                copy_of_mask, mask,
                (size_t)7U *
                    sizeof(
                        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
            Option_63 lit1;
            lit1.tag = core_option_Some;
            memcpy(
                lit1.f0, copy_of_mask,
                (size_t)7U *
                    sizeof(
                        libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
            signer_response0 = lit1;
            /* Passing arrays by value in Rust generates a copy in C */
            int32_t copy_of_hint_candidate[8U][256U];
            memcpy(copy_of_hint_candidate, hint_candidate,
                   (size_t)8U * sizeof(int32_t[256U]));
            core_option_Option_d6 lit;
            lit.tag = core_option_Some;
            memcpy(lit.f0, copy_of_hint_candidate,
                   (size_t)8U * sizeof(int32_t[256U]));
            hint0 = lit;
          }
        }
      }
    }
  }
  core_result_Result_87 uu____8;
  if (commitment_hash0.tag == core_option_None) {
    uu____8 = (KRML_CLITERAL(core_result_Result_87){
        .tag = core_result_Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    uint8_t commitment_hash1[64U];
    memcpy(commitment_hash1, commitment_hash0.f0,
           (size_t)64U * sizeof(uint8_t));
    uint8_t commitment_hash[64U];
    memcpy(commitment_hash, commitment_hash1, (size_t)64U * sizeof(uint8_t));
    if (signer_response0.tag == core_option_None) {
      uu____8 = (KRML_CLITERAL(core_result_Result_87){
          .tag = core_result_Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
          signer_response1[7U];
      memcpy(
          signer_response1, signer_response0.f0,
          (size_t)7U *
              sizeof(libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
          signer_response[7U];
      memcpy(
          signer_response, signer_response1,
          (size_t)7U *
              sizeof(libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      if (!(hint0.tag == core_option_None)) {
        int32_t hint1[8U][256U];
        memcpy(hint1, hint0.f0, (size_t)8U * sizeof(int32_t[256U]));
        int32_t hint[8U][256U];
        memcpy(hint, hint1, (size_t)8U * sizeof(int32_t[256U]));
        libcrux_iot_ml_dsa_encoding_signature_serialize_08(
            Eurydice_array_to_slice((size_t)64U, commitment_hash, uint8_t),
            Eurydice_array_to_slice(
                (size_t)7U, signer_response,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            Eurydice_array_to_slice((size_t)8U, hint, int32_t[256U]),
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT,
            LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice((size_t)4627U, signature, uint8_t));
        return (KRML_CLITERAL(core_result_Result_87){.tag = core_result_Ok});
      }
      uu____8 = (KRML_CLITERAL(core_result_Result_87){
          .tag = core_result_Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____8;
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
KRML_MUSTINLINE core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  core_result_Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(core_option_Option_30){.tag = core_option_None}));
  if (!(uu____0.tag == core_result_Ok)) {
    return (KRML_CLITERAL(core_result_Result_87){
        .tag = core_result_Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  Eurydice_slice uu____1 = signing_key;
  Eurydice_slice uu____2 = message;
  core_option_Option_e3 uu____3 = {.tag = core_option_Some,
                                   .f0 = domain_separation_context};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
      uu____1, uu____2, uu____3, copy_of_randomness, signature);
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
KRML_MUSTINLINE core_result_Result_f2
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_c4(Eurydice_slice signing_key,
                                                    Eurydice_slice message,
                                                    Eurydice_slice context,
                                                    uint8_t randomness[32U]) {
  libcrux_iot_ml_dsa_types_MLDSASignature_9b signature =
      libcrux_iot_ml_dsa_types_zero_ad_c2();
  Eurydice_slice uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  core_result_Result_87 uu____4 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
          uu____0, uu____1, uu____2, copy_of_randomness, signature.value);
  core_result_Result_f2 uu____5;
  if (uu____4.tag == core_result_Ok) {
    uu____5 = (KRML_CLITERAL(core_result_Result_f2){
        .tag = core_result_Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____4.f0;
    uu____5 = (KRML_CLITERAL(core_result_Result_f2){.tag = core_result_Err,
                                                    .val = {.case_Err = e}});
  }
  return uu____5;
}

/**
 Sign.
*/
core_result_Result_f2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)4896U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_c4(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_f2 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t *uu____0 = libcrux_iot_ml_dsa_types_as_ref_f8_32(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 Sign.
*/
core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)4896U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
      uu____0, uu____1, uu____2, copy_of_randomness, signature);
}

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_87 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_mut(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U],
    uint8_t *signature) {
  uint8_t *uu____0 = libcrux_iot_ml_dsa_types_as_ref_f8_32(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_mut(
      uu____0, uu____1, uu____2, copy_of_randomness, signature);
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
KRML_MUSTINLINE core_result_Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_mut_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U],
    uint8_t *signature) {
  if (!(Eurydice_slice_len(context, uint8_t) >
        LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
    Eurydice_slice uu____0 = context;
    core_option_Option_30 lit;
    lit.tag = core_option_Some;
    uint8_t ret[11U];
    libcrux_iot_ml_dsa_pre_hash_oid_0b(ret);
    memcpy(lit.f0, ret, (size_t)11U * sizeof(uint8_t));
    core_result_Result_80 uu____1 =
        libcrux_iot_ml_dsa_pre_hash_new_c9(uu____0, lit);
    if (!(uu____1.tag == core_result_Ok)) {
      return (KRML_CLITERAL(core_result_Result_87){
          .tag = core_result_Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc =
        uu____1.val.case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        domain_separation_context = dsc;
    Eurydice_slice uu____2 = signing_key;
    Eurydice_slice uu____3 = pre_hash_buffer;
    core_option_Option_e3 uu____4 = {.tag = core_option_Some,
                                     .f0 = domain_separation_context};
    /* Passing arrays by value in Rust generates a copy in C */
    uint8_t copy_of_randomness[32U];
    memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
    return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
        uu____2, uu____3, uu____4, copy_of_randomness, signature);
  }
  return (KRML_CLITERAL(core_result_Result_87){
      .tag = core_result_Err,
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
KRML_MUSTINLINE core_result_Result_f2
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_36(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]) {
  libcrux_iot_ml_dsa_types_MLDSASignature_9b signature =
      libcrux_iot_ml_dsa_types_zero_ad_c2();
  Eurydice_slice uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 = pre_hash_buffer;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  core_result_Result_87 uu____5 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_mut_36(
          uu____0, uu____1, uu____2, uu____3, copy_of_randomness,
          signature.value);
  core_result_Result_f2 uu____6;
  if (uu____5.tag == core_result_Ok) {
    uu____6 = (KRML_CLITERAL(core_result_Result_f2){
        .tag = core_result_Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____5.f0;
    uu____6 = (KRML_CLITERAL(core_result_Result_f2){.tag = core_result_Err,
                                                    .val = {.case_Err = e}});
  }
  return uu____6;
}

/**
 Sign (pre-hashed).
*/
core_result_Result_f2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_pre_hashed_shake128(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)4896U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 = pre_hash_buffer;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_36(
      uu____0, uu____1, uu____2, uu____3, copy_of_randomness);
}

/**
 Generate a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_f2
libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_pre_hashed_shake128(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t pre_hash_buffer[32U] = {0U};
  uint8_t *uu____0 = libcrux_iot_ml_dsa_types_as_ref_f8_32(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 =
      Eurydice_array_to_slice((size_t)32U, pre_hash_buffer, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3, copy_of_randomness);
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
    uint8_t *verification_key, Eurydice_slice message,
    core_option_Option_e3 domain_separation_context,
    uint8_t *signature_serialized) {
  uint8_t rand_stack[840U] = {0U};
  uint8_t rand_block[168U] = {0U};
  int32_t tmp_stack[263U] = {0U};
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d poly_slot =
      libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)2592U, verification_key, uint8_t),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice t1_serialized = uu____0.snd;
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d t1[8U];
  KRML_MAYBE_FOR8(i, (size_t)0U, (size_t)8U, (size_t)1U,
                  t1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_VERIFICATION_KEY_SIZE,
      t1_serialized,
      Eurydice_array_to_slice(
          (size_t)8U, t1,
          libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
  uint8_t deserialized_commitment_hash[64U] = {0U};
  libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
      deserialized_signer_response[7U];
  KRML_MAYBE_FOR7(i, (size_t)0U, (size_t)7U, (size_t)1U,
                  deserialized_signer_response[i] =
                      libcrux_iot_ml_dsa_polynomial_zero_c2_08(););
  int32_t deserialized_hint[8U][256U] = {{0U}};
  core_result_Result_5c uu____1 =
      libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT,
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_GAMMA1_RING_ELEMENT_SIZE,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT,
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_SIGNATURE_SIZE,
          Eurydice_array_to_slice((size_t)4627U, signature_serialized, uint8_t),
          Eurydice_array_to_slice((size_t)64U, deserialized_commitment_hash,
                                  uint8_t),
          Eurydice_array_to_slice(
              (size_t)7U, deserialized_signer_response,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
          Eurydice_array_to_slice((size_t)8U, deserialized_hint,
                                  int32_t[256U]));
  core_result_Result_5c uu____2;
  if (uu____1.tag == core_result_Ok) {
    if (libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            Eurydice_array_to_slice(
                (size_t)7U, deserialized_signer_response,
                libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
            ((int32_t)2 << (uint32_t)
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA)) {
      uu____2 = (KRML_CLITERAL(core_result_Result_5c){
          .tag = core_result_Err,
          .f0 =
              libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      uint8_t verification_key_hash[64U] = {0U};
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_24(
          Eurydice_array_to_slice((size_t)2592U, verification_key, uint8_t),
          verification_key_hash);
      uint8_t message_representative[64U] = {0U};
      libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
          Eurydice_array_to_slice((size_t)64U, verification_key_hash, uint8_t),
          &domain_separation_context, message, message_representative);
      libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
          verifier_challenge = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
      libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
          Eurydice_array_to_slice((size_t)64U, deserialized_commitment_hash,
                                  uint8_t),
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)7U, deserialized_signer_response,
                       libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
                   libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d);
           i++) {
        size_t i0 = i;
        libcrux_iot_ml_dsa_ntt_ntt_08(&deserialized_signer_response[i0]);
      }
      libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A, seed_for_a,
          rand_stack, rand_block, tmp_stack, &poly_slot,
          Eurydice_array_to_slice(
              (size_t)7U, deserialized_signer_response,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
          &verifier_challenge,
          Eurydice_array_to_slice(
              (size_t)8U, t1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      uint8_t recomputed_commitment_hash[64U] = {0U};
      libcrux_iot_ml_dsa_arithmetic_use_hint_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2,
          Eurydice_array_to_slice((size_t)8U, deserialized_hint, int32_t[256U]),
          Eurydice_array_to_slice(
              (size_t)8U, t1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d));
      uint8_t commitment_serialized[1024U] = {0U};
      libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_RING_ELEMENT_SIZE,
          Eurydice_array_to_slice(
              (size_t)8U, t1,
              libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d),
          Eurydice_array_to_slice((size_t)1024U, commitment_serialized,
                                  uint8_t));
      libcrux_iot_sha3_keccak_KeccakXofState_c7 shake =
          libcrux_iot_ml_dsa_hash_functions_portable_init_88();
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice((size_t)64U, message_representative,
                                          uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
          &shake, Eurydice_array_to_slice((size_t)1024U, commitment_serialized,
                                          uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
          &shake, Eurydice_array_to_slice((size_t)64U,
                                          recomputed_commitment_hash, uint8_t));
      if (Eurydice_array_eq((size_t)64U, deserialized_commitment_hash,
                            recomputed_commitment_hash, uint8_t)) {
        uu____2 = (KRML_CLITERAL(core_result_Result_5c){.tag = core_result_Ok});
      } else {
        uu____2 = (KRML_CLITERAL(core_result_Result_5c){
            .tag = core_result_Err,
            .f0 =
                libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_iot_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 =
        (KRML_CLITERAL(core_result_Result_5c){.tag = core_result_Err, .f0 = e});
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
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_c4(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, uint8_t *signature_serialized) {
  core_result_Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(core_option_Option_30){.tag = core_option_None}));
  if (!(uu____0.tag == core_result_Ok)) {
    return (KRML_CLITERAL(core_result_Result_5c){
        .tag = core_result_Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
      verification_key_serialized, message,
      (KRML_CLITERAL(core_option_Option_e3){.tag = core_option_Some,
                                            .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify.
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_c4(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
core_result_Result_5c libcrux_iot_ml_dsa_ml_dsa_87_portable_verify(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_iot_ml_dsa_types_MLDSASignature_9b *signature) {
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
KRML_MUSTINLINE core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_pre_hashed_36(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, Eurydice_slice pre_hash_buffer,
    uint8_t *signature_serialized) {
  libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(message, pre_hash_buffer);
  Eurydice_slice uu____0 = context;
  core_option_Option_30 lit;
  lit.tag = core_option_Some;
  uint8_t ret[11U];
  libcrux_iot_ml_dsa_pre_hash_oid_0b(ret);
  memcpy(lit.f0, ret, (size_t)11U * sizeof(uint8_t));
  core_result_Result_80 uu____1 =
      libcrux_iot_ml_dsa_pre_hash_new_c9(uu____0, lit);
  if (!(uu____1.tag == core_result_Ok)) {
    return (KRML_CLITERAL(core_result_Result_5c){
        .tag = core_result_Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____1.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
      verification_key_serialized, pre_hash_buffer,
      (KRML_CLITERAL(core_option_Option_e3){.tag = core_option_Some,
                                            .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
core_result_Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify_pre_hashed_shake128(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_pre_hashed_36(
      verification_key, message, context, pre_hash_buffer, signature);
}

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
    libcrux_iot_ml_dsa_types_MLDSASignature_9b *signature) {
  uint8_t pre_hash_buffer[32U] = {0U};
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify_pre_hashed_shake128(
      libcrux_iot_ml_dsa_types_as_ref_e9_d8(verification_key), message, context,
      Eurydice_array_to_slice((size_t)32U, pre_hash_buffer, uint8_t),
      libcrux_iot_ml_dsa_types_as_ref_ad_c2(signature));
}

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::SigningError}
*/
libcrux_iot_ml_dsa_types_SigningError libcrux_iot_ml_dsa_pre_hash_from_49(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e) {
  return libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError;
}

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::VerificationError}
*/
libcrux_iot_ml_dsa_types_VerificationError libcrux_iot_ml_dsa_pre_hash_from_97(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e) {
  return libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError;
}
