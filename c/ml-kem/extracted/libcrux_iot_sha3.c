/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: e656e17bff6ca5efac8ab6919b9b74cb9a8dd8ad
 * Eurydice: aaa9fa657fb6f09802edb890252040d94cd93982
 * Karamel: 8c19d41458ce5cbfea029ebc03334ba96d149039
 * F*: unset
 * Libcrux: 0b1da9aa241abc8ae799a477417da10614fe9c53
 */

#include "internal/libcrux_iot_sha3.h"

#include "internal/libcrux_iot_core.h"
#include "libcrux_iot_core.h"

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0
libcrux_iot_sha3_lane_from_ints_8d(Eurydice_arr_a0 value) {
  return value;
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0 libcrux_iot_sha3_lane_zero_8d(void) {
  return libcrux_iot_sha3_lane_from_ints_8d(
      libcrux_secrets_int_public_integers_classify_27_aa(
          (KRML_CLITERAL(Eurydice_arr_a0){.data = {0U}})));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_state_new_18(void) {
  Eurydice_arr_c0 uu____0;
  Eurydice_arr_a0 repeat_expression0[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression0[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(uu____0.data, repeat_expression0,
         (size_t)25U * sizeof(Eurydice_arr_a0));
  Eurydice_arr_44 uu____1;
  Eurydice_arr_a0 repeat_expression1[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression1[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(uu____1.data, repeat_expression1,
         (size_t)5U * sizeof(Eurydice_arr_a0));
  libcrux_iot_sha3_state_KeccakState lit;
  lit.st = uu____0;
  lit.c = uu____1;
  Eurydice_arr_a0 repeat_expression[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(lit.d.data, repeat_expression, (size_t)5U * sizeof(Eurydice_arr_a0));
  lit.i = (size_t)0U;
  return lit;
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE Eurydice_arr_a0 libcrux_iot_sha3_state_get_lane_18(
    const libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j) {
  return self->st.data[(size_t)5U * j + i];
}

/**
This function found in impl {core::ops::index::Index<usize, u32> for
libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE const uint32_t *libcrux_iot_sha3_lane_index_cc(
    const Eurydice_arr_a0 *self, size_t index) {
  return &self->data[index];
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_set_lane_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    Eurydice_arr_a0 lane) {
  self->st.data[(size_t)5U * j + i] = lane;
}

/**
This function found in impl {core::convert::From<[u32; 2usize]> for
libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0
libcrux_iot_sha3_lane_from_29(Eurydice_arr_a0 value) {
  return value;
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0
libcrux_iot_sha3_lane_interleave_8d(Eurydice_arr_a0 self) {
  uint64_t lane_u64 =
      libcrux_secrets_int_as_u64_b8(
          libcrux_iot_sha3_lane_index_cc(&self, (size_t)0U)[0U]) |
      libcrux_secrets_int_as_u64_b8(
          libcrux_iot_sha3_lane_index_cc(&self, (size_t)1U)[0U])
          << 32U;
  uint64_t even_bits = lane_u64 & 6148914691236517205ULL;
  even_bits = (even_bits ^ even_bits >> 1U) & 3689348814741910323ULL;
  even_bits = (even_bits ^ even_bits >> 2U) & 1085102592571150095ULL;
  even_bits = (even_bits ^ even_bits >> 4U) & 71777214294589695ULL;
  even_bits = (even_bits ^ even_bits >> 8U) & 281470681808895ULL;
  even_bits = (even_bits ^ even_bits >> 16U) & 4294967295ULL;
  uint64_t odd_bits = lane_u64 >> 1U & 6148914691236517205ULL;
  odd_bits = (odd_bits ^ odd_bits >> 1U) & 3689348814741910323ULL;
  odd_bits = (odd_bits ^ odd_bits >> 2U) & 1085102592571150095ULL;
  odd_bits = (odd_bits ^ odd_bits >> 4U) & 71777214294589695ULL;
  odd_bits = (odd_bits ^ odd_bits >> 8U) & 281470681808895ULL;
  odd_bits = (odd_bits ^ odd_bits >> 16U) & 4294967295ULL;
  return libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
      .data = {libcrux_secrets_int_as_u32_a3(even_bits),
               libcrux_secrets_int_as_u32_a3(odd_bits)}}));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE uint32_t libcrux_iot_sha3_state_get_with_zeta_18(
    const libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    size_t zeta) {
  return libcrux_iot_sha3_lane_index_cc(&self->st.data[(size_t)5U * j + i],
                                        zeta)[0U];
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_set_lane_value_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    uint32_t value) {
  self->c.data[i].data[j] = value;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_d(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t c_x4_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)0U)[0U];
  uint32_t c_x1_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)1U)[0U];
  uint32_t c_x3_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)0U)[0U];
  uint32_t c_x0_zeta1 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)1U)[0U];
  uint32_t c_x2_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)0U)[0U];
  uint32_t c_x4_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)1U)[0U];
  uint32_t d_x0_zeta0 = c_x4_zeta0 ^ core_num__u32__rotate_left(c_x1_zeta1, 1U);
  s->d.data->data[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  s->d.data[2U].data[1U] = d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  s->d.data[4U].data[0U] = d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  s->d.data[1U].data[1U] = d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  s->d.data[3U].data[0U] = d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  s->d.data->data[1U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  s->d.data[2U].data[0U] = d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  s->d.data[4U].data[1U] = d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  s->d.data[1U].data[0U] = d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  s->d.data[3U].data[1U] = d_x3_zeta1;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_d(s);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_set_with_zeta_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j, size_t zeta,
    uint32_t v) {
  self->st.data[(size_t)5U * j + i].data[zeta] = v;
}

typedef struct uint32_t_x2_s {
  uint32_t fst;
  uint32_t snd;
} uint32_t_x2;

typedef struct uint32_t_x3_s {
  uint32_t fst;
  uint32_t snd;
  uint32_t thd;
} uint32_t_x3;

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 9U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 1U)};
  uint32_t bx40 = uu____0.fst;
  uint32_t bx00 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 3U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 13U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 4U)};
  uint32_t bx10 = uu____1.fst;
  uint32_t bx20 = uu____1.snd;
  uint32_t bx30 = uu____1.thd;
  uint32_t ax00 = bx00 ^ (~bx10 & bx20);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 9U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 0U)};
  uint32_t bx41 = uu____2.fst;
  uint32_t bx01 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 3U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 12U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 4U)};
  uint32_t bx11 = uu____3.fst;
  uint32_t bx21 = uu____3.snd;
  uint32_t bx31 = uu____3.thd;
  uint32_t ax01 = bx01 ^ (~bx11 & bx21);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 18U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 5U)};
  uint32_t bx12 = uu____4.fst;
  uint32_t bx22 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 8U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 28U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 14U)};
  uint32_t bx32 = uu____5.fst;
  uint32_t bx42 = uu____5.snd;
  uint32_t bx02 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d03 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d13 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d03, 18U),
                         .snd = core_num__u32__rotate_left(a13 ^ d13, 5U)};
  uint32_t bx13 = uu____6.fst;
  uint32_t bx23 = uu____6.snd;
  uint32_t a23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t d23 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d33 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d43 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a23 ^ d23, 7U),
                         .snd = core_num__u32__rotate_left(a33 ^ d33, 28U),
                         .thd = core_num__u32__rotate_left(a43 ^ d43, 13U)};
  uint32_t bx33 = uu____7.fst;
  uint32_t bx43 = uu____7.snd;
  uint32_t bx03 = uu____7.thd;
  uint32_t ax03 = bx03 ^ (~bx13 & bx23);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax03);
  uint32_t ax12 = bx13 ^ (~bx23 & bx33);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx23 ^ (~bx33 & bx43);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx33 ^ (~bx43 & bx03);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx43 ^ (~bx03 & bx13);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax42);
  uint32_t a03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d04 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  uint32_t d14 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____8 = {.fst = core_num__u32__rotate_left(a03 ^ d04, 21U),
                         .snd = core_num__u32__rotate_left(a14 ^ d14, 1U)};
  uint32_t bx34 = uu____8.fst;
  uint32_t bx44 = uu____8.snd;
  uint32_t a24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d24 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d34 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d44 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____9 = {.fst = core_num__u32__rotate_left(a24 ^ d24, 31U),
                         .snd = core_num__u32__rotate_left(a34 ^ d34, 28U),
                         .thd = core_num__u32__rotate_left(a44 ^ d44, 20U)};
  uint32_t bx04 = uu____9.fst;
  uint32_t bx14 = uu____9.snd;
  uint32_t bx24 = uu____9.thd;
  uint32_t ax04 = bx04 ^ (~bx14 & bx24);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax04);
  uint32_t ax13 = bx14 ^ (~bx24 & bx34);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax13);
  uint32_t ax23 = bx24 ^ (~bx34 & bx44);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax23);
  uint32_t ax33 = bx34 ^ (~bx44 & bx04);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax33);
  uint32_t ax43 = bx44 ^ (~bx04 & bx14);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax43);
  uint32_t a04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____10 = {.fst = core_num__u32__rotate_left(a04 ^ d0, 20U),
                          .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____10.fst;
  uint32_t bx4 = uu____10.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____11 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                          .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                          .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____11.fst;
  uint32_t bx1 = uu____11.snd;
  uint32_t bx2 = uu____11.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax14 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax14);
  uint32_t ax24 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax24);
  uint32_t ax34 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax34);
  uint32_t ax44 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax44);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_d(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t c_x4_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)0U)[0U];
  uint32_t c_x1_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)1U)[0U];
  uint32_t c_x3_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)0U)[0U];
  uint32_t c_x0_zeta1 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)1U)[0U];
  uint32_t c_x2_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)0U)[0U];
  uint32_t c_x4_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)1U)[0U];
  uint32_t d_x0_zeta0 = c_x4_zeta0 ^ core_num__u32__rotate_left(c_x1_zeta1, 1U);
  s->d.data->data[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  s->d.data[2U].data[1U] = d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  s->d.data[4U].data[0U] = d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  s->d.data[1U].data[1U] = d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  s->d.data[3U].data[0U] = d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  s->d.data->data[1U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  s->d.data[2U].data[0U] = d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  s->d.data[4U].data[1U] = d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  s->d.data[1U].data[0U] = d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  s->d.data[3U].data[1U] = d_x3_zeta1;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_d(s);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 9U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 1U)};
  uint32_t bx40 = uu____0.fst;
  uint32_t bx00 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 3U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 13U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 4U)};
  uint32_t bx10 = uu____1.fst;
  uint32_t bx20 = uu____1.snd;
  uint32_t bx30 = uu____1.thd;
  uint32_t ax00 = bx00 ^ (~bx10 & bx20);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 9U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 0U)};
  uint32_t bx41 = uu____2.fst;
  uint32_t bx01 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 3U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 12U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 4U)};
  uint32_t bx11 = uu____3.fst;
  uint32_t bx21 = uu____3.snd;
  uint32_t bx31 = uu____3.thd;
  uint32_t ax01 = bx01 ^ (~bx11 & bx21);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 18U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 5U)};
  uint32_t bx12 = uu____4.fst;
  uint32_t bx22 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 8U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 28U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 14U)};
  uint32_t bx32 = uu____5.fst;
  uint32_t bx42 = uu____5.snd;
  uint32_t bx02 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d03 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d13 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d03, 18U),
                         .snd = core_num__u32__rotate_left(a13 ^ d13, 5U)};
  uint32_t bx13 = uu____6.fst;
  uint32_t bx23 = uu____6.snd;
  uint32_t a23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t d23 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d33 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d43 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a23 ^ d23, 7U),
                         .snd = core_num__u32__rotate_left(a33 ^ d33, 28U),
                         .thd = core_num__u32__rotate_left(a43 ^ d43, 13U)};
  uint32_t bx33 = uu____7.fst;
  uint32_t bx43 = uu____7.snd;
  uint32_t bx03 = uu____7.thd;
  uint32_t ax03 = bx03 ^ (~bx13 & bx23);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax03);
  uint32_t ax12 = bx13 ^ (~bx23 & bx33);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx23 ^ (~bx33 & bx43);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx33 ^ (~bx43 & bx03);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx43 ^ (~bx03 & bx13);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax42);
  uint32_t a03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d04 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  uint32_t d14 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____8 = {.fst = core_num__u32__rotate_left(a03 ^ d04, 21U),
                         .snd = core_num__u32__rotate_left(a14 ^ d14, 1U)};
  uint32_t bx34 = uu____8.fst;
  uint32_t bx44 = uu____8.snd;
  uint32_t a24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d24 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d34 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d44 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____9 = {.fst = core_num__u32__rotate_left(a24 ^ d24, 31U),
                         .snd = core_num__u32__rotate_left(a34 ^ d34, 28U),
                         .thd = core_num__u32__rotate_left(a44 ^ d44, 20U)};
  uint32_t bx04 = uu____9.fst;
  uint32_t bx14 = uu____9.snd;
  uint32_t bx24 = uu____9.thd;
  uint32_t ax04 = bx04 ^ (~bx14 & bx24);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax04);
  uint32_t ax13 = bx14 ^ (~bx24 & bx34);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax13);
  uint32_t ax23 = bx24 ^ (~bx34 & bx44);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax23);
  uint32_t ax33 = bx34 ^ (~bx44 & bx04);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax33);
  uint32_t ax43 = bx44 ^ (~bx04 & bx14);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax43);
  uint32_t a04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____10 = {.fst = core_num__u32__rotate_left(a04 ^ d0, 20U),
                          .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____10.fst;
  uint32_t bx4 = uu____10.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____11 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                          .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                          .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____11.fst;
  uint32_t bx1 = uu____11.snd;
  uint32_t bx2 = uu____11.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax14 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax14);
  uint32_t ax24 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax24);
  uint32_t ax34 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax34);
  uint32_t ax44 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax44);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_d(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t c_x4_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)0U)[0U];
  uint32_t c_x1_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)1U)[0U];
  uint32_t c_x3_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)0U)[0U];
  uint32_t c_x0_zeta1 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)1U)[0U];
  uint32_t c_x2_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)0U)[0U];
  uint32_t c_x4_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)1U)[0U];
  uint32_t d_x0_zeta0 = c_x4_zeta0 ^ core_num__u32__rotate_left(c_x1_zeta1, 1U);
  s->d.data->data[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  s->d.data[2U].data[1U] = d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  s->d.data[4U].data[0U] = d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  s->d.data[1U].data[1U] = d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  s->d.data[3U].data[0U] = d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  s->d.data->data[1U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  s->d.data[2U].data[0U] = d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  s->d.data[4U].data[1U] = d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  s->d.data[1U].data[0U] = d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  s->d.data[3U].data[1U] = d_x3_zeta1;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_d(s);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 9U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 1U)};
  uint32_t bx40 = uu____0.fst;
  uint32_t bx00 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 3U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 13U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 4U)};
  uint32_t bx10 = uu____1.fst;
  uint32_t bx20 = uu____1.snd;
  uint32_t bx30 = uu____1.thd;
  uint32_t ax00 = bx00 ^ (~bx10 & bx20);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 9U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 0U)};
  uint32_t bx41 = uu____2.fst;
  uint32_t bx01 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 3U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 12U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 4U)};
  uint32_t bx11 = uu____3.fst;
  uint32_t bx21 = uu____3.snd;
  uint32_t bx31 = uu____3.thd;
  uint32_t ax01 = bx01 ^ (~bx11 & bx21);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 18U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 5U)};
  uint32_t bx12 = uu____4.fst;
  uint32_t bx22 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 8U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 28U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 14U)};
  uint32_t bx32 = uu____5.fst;
  uint32_t bx42 = uu____5.snd;
  uint32_t bx02 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d03 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d13 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d03, 18U),
                         .snd = core_num__u32__rotate_left(a13 ^ d13, 5U)};
  uint32_t bx13 = uu____6.fst;
  uint32_t bx23 = uu____6.snd;
  uint32_t a23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t d23 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d33 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d43 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a23 ^ d23, 7U),
                         .snd = core_num__u32__rotate_left(a33 ^ d33, 28U),
                         .thd = core_num__u32__rotate_left(a43 ^ d43, 13U)};
  uint32_t bx33 = uu____7.fst;
  uint32_t bx43 = uu____7.snd;
  uint32_t bx03 = uu____7.thd;
  uint32_t ax03 = bx03 ^ (~bx13 & bx23);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax03);
  uint32_t ax12 = bx13 ^ (~bx23 & bx33);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx23 ^ (~bx33 & bx43);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx33 ^ (~bx43 & bx03);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx43 ^ (~bx03 & bx13);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax42);
  uint32_t a03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d04 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  uint32_t d14 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____8 = {.fst = core_num__u32__rotate_left(a03 ^ d04, 21U),
                         .snd = core_num__u32__rotate_left(a14 ^ d14, 1U)};
  uint32_t bx34 = uu____8.fst;
  uint32_t bx44 = uu____8.snd;
  uint32_t a24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d24 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d34 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d44 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____9 = {.fst = core_num__u32__rotate_left(a24 ^ d24, 31U),
                         .snd = core_num__u32__rotate_left(a34 ^ d34, 28U),
                         .thd = core_num__u32__rotate_left(a44 ^ d44, 20U)};
  uint32_t bx04 = uu____9.fst;
  uint32_t bx14 = uu____9.snd;
  uint32_t bx24 = uu____9.thd;
  uint32_t ax04 = bx04 ^ (~bx14 & bx24);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax04);
  uint32_t ax13 = bx14 ^ (~bx24 & bx34);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax13);
  uint32_t ax23 = bx24 ^ (~bx34 & bx44);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax23);
  uint32_t ax33 = bx34 ^ (~bx44 & bx04);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax33);
  uint32_t ax43 = bx44 ^ (~bx04 & bx14);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax43);
  uint32_t a04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____10 = {.fst = core_num__u32__rotate_left(a04 ^ d0, 20U),
                          .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____10.fst;
  uint32_t bx4 = uu____10.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____11 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                          .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                          .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____11.fst;
  uint32_t bx1 = uu____11.snd;
  uint32_t bx2 = uu____11.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax14 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax14);
  uint32_t ax24 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax24);
  uint32_t ax34 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax34);
  uint32_t ax44 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax44);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_d(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t c_x4_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)0U)[0U];
  uint32_t c_x1_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)1U)[0U];
  uint32_t c_x3_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)0U)[0U];
  uint32_t c_x0_zeta1 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)1U)[0U];
  uint32_t c_x2_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)0U)[0U];
  uint32_t c_x4_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)1U)[0U];
  uint32_t d_x0_zeta0 = c_x4_zeta0 ^ core_num__u32__rotate_left(c_x1_zeta1, 1U);
  s->d.data->data[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  s->d.data[2U].data[1U] = d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  s->d.data[4U].data[0U] = d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  s->d.data[1U].data[1U] = d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  s->d.data[3U].data[0U] = d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  s->d.data->data[1U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  s->d.data[2U].data[0U] = d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  s->d.data[4U].data[1U] = d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  s->d.data[1U].data[0U] = d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  s->d.data[3U].data[1U] = d_x3_zeta1;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_d(s);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 9U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 1U)};
  uint32_t bx40 = uu____0.fst;
  uint32_t bx00 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 3U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 13U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 4U)};
  uint32_t bx10 = uu____1.fst;
  uint32_t bx20 = uu____1.snd;
  uint32_t bx30 = uu____1.thd;
  uint32_t ax00 = bx00 ^ (~bx10 & bx20);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 9U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 0U)};
  uint32_t bx41 = uu____2.fst;
  uint32_t bx01 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 3U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 12U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 4U)};
  uint32_t bx11 = uu____3.fst;
  uint32_t bx21 = uu____3.snd;
  uint32_t bx31 = uu____3.thd;
  uint32_t ax01 = bx01 ^ (~bx11 & bx21);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 18U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 5U)};
  uint32_t bx12 = uu____4.fst;
  uint32_t bx22 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 8U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 28U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 14U)};
  uint32_t bx32 = uu____5.fst;
  uint32_t bx42 = uu____5.snd;
  uint32_t bx02 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d03 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d13 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d03, 18U),
                         .snd = core_num__u32__rotate_left(a13 ^ d13, 5U)};
  uint32_t bx13 = uu____6.fst;
  uint32_t bx23 = uu____6.snd;
  uint32_t a23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t d23 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d33 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d43 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a23 ^ d23, 7U),
                         .snd = core_num__u32__rotate_left(a33 ^ d33, 28U),
                         .thd = core_num__u32__rotate_left(a43 ^ d43, 13U)};
  uint32_t bx33 = uu____7.fst;
  uint32_t bx43 = uu____7.snd;
  uint32_t bx03 = uu____7.thd;
  uint32_t ax03 = bx03 ^ (~bx13 & bx23);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax03);
  uint32_t ax12 = bx13 ^ (~bx23 & bx33);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx23 ^ (~bx33 & bx43);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx33 ^ (~bx43 & bx03);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx43 ^ (~bx03 & bx13);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax42);
  uint32_t a03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d04 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  uint32_t d14 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____8 = {.fst = core_num__u32__rotate_left(a03 ^ d04, 21U),
                         .snd = core_num__u32__rotate_left(a14 ^ d14, 1U)};
  uint32_t bx34 = uu____8.fst;
  uint32_t bx44 = uu____8.snd;
  uint32_t a24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d24 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d34 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d44 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____9 = {.fst = core_num__u32__rotate_left(a24 ^ d24, 31U),
                         .snd = core_num__u32__rotate_left(a34 ^ d34, 28U),
                         .thd = core_num__u32__rotate_left(a44 ^ d44, 20U)};
  uint32_t bx04 = uu____9.fst;
  uint32_t bx14 = uu____9.snd;
  uint32_t bx24 = uu____9.thd;
  uint32_t ax04 = bx04 ^ (~bx14 & bx24);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax04);
  uint32_t ax13 = bx14 ^ (~bx24 & bx34);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax13);
  uint32_t ax23 = bx24 ^ (~bx34 & bx44);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax23);
  uint32_t ax33 = bx34 ^ (~bx44 & bx04);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax33);
  uint32_t ax43 = bx44 ^ (~bx04 & bx14);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax43);
  uint32_t a04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____10 = {.fst = core_num__u32__rotate_left(a04 ^ d0, 20U),
                          .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____10.fst;
  uint32_t bx4 = uu____10.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____11 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                          .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                          .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____11.fst;
  uint32_t bx1 = uu____11.snd;
  uint32_t bx2 = uu____11.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax14 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax14);
  uint32_t ax24 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax24);
  uint32_t ax34 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax34);
  uint32_t ax44 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax44);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)0U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)0U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)0U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)0U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)0U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)0U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)0U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)0U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_4rounds_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(s);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 4
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_23(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)4U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)4U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 4
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_23(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)4U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)4U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 4
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_23(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)4U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)4U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 4
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_23(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)4U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)4U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 4
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_4rounds_23(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_23(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_23(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_23(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_23(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(s);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 8
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_70(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)8U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)8U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 8
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_70(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)8U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)8U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 8
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_70(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)8U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)8U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 8
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_70(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 = (bx00 ^ (~bx10 & bx20)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)8U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 = (bx01 ^ (~bx11 & bx21)) ^
         LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)8U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 8
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_4rounds_70(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_70(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_70(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_70(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_70(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(s);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 12
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_60(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)12U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)12U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 12
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_60(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)12U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)12U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 12
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_60(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)12U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)12U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 12
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_60(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)12U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)12U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 12
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_4rounds_60(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_60(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_60(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_60(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_60(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(s);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 16
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_18(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)16U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)16U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 16
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_18(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)16U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)16U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 16
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_18(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)16U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)16U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 16
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_18(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)16U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)16U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 16
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_4rounds_18(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_18(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_18(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_18(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_18(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(s);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 20
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_fc(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)20U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)20U + (size_t)0U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 20
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_fc(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)20U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)20U + (size_t)1U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 20
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_fc(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)20U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)20U + (size_t)2U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 20
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_fc(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d00 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d10 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d00, 0U),
                         .snd = core_num__u32__rotate_left(a10 ^ d10, 22U)};
  uint32_t bx00 = uu____0.fst;
  uint32_t bx10 = uu____0.snd;
  uint32_t a20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d20 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d30 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d40 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a20 ^ d20, 22U),
                         .snd = core_num__u32__rotate_left(a30 ^ d30, 11U),
                         .thd = core_num__u32__rotate_left(a40 ^ d40, 7U)};
  uint32_t bx20 = uu____1.fst;
  uint32_t bx30 = uu____1.snd;
  uint32_t bx40 = uu____1.thd;
  uint32_t ax00 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax00 =
      (bx00 ^ (~bx10 & bx20)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[(size_t)20U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax00);
  uint32_t ax1 = bx10 ^ (~bx20 & bx30);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx20 ^ (~bx30 & bx40);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx30 ^ (~bx40 & bx00);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx40 ^ (~bx00 & bx10);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
  uint32_t a00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t d01 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d11 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____2 = {.fst = core_num__u32__rotate_left(a00 ^ d01, 0U),
                         .snd = core_num__u32__rotate_left(a11 ^ d11, 22U)};
  uint32_t bx01 = uu____2.fst;
  uint32_t bx11 = uu____2.snd;
  uint32_t a21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d21 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d31 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d41 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____3 = {.fst = core_num__u32__rotate_left(a21 ^ d21, 21U),
                         .snd = core_num__u32__rotate_left(a31 ^ d31, 10U),
                         .thd = core_num__u32__rotate_left(a41 ^ d41, 7U)};
  uint32_t bx21 = uu____3.fst;
  uint32_t bx31 = uu____3.snd;
  uint32_t bx41 = uu____3.thd;
  uint32_t ax01 = libcrux_secrets_int_public_integers_classify_27_df(0U);
  ax01 =
      (bx01 ^ (~bx11 & bx21)) ^
      LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[(size_t)20U + (size_t)3U];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax01);
  uint32_t ax10 = bx11 ^ (~bx21 & bx31);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax10);
  uint32_t ax20 = bx21 ^ (~bx31 & bx41);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax20);
  uint32_t ax30 = bx31 ^ (~bx41 & bx01);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax30);
  uint32_t ax40 = bx41 ^ (~bx01 & bx11);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax40);
  uint32_t a01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d02 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d12 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____4 = {.fst = core_num__u32__rotate_left(a01 ^ d02, 2U),
                         .snd = core_num__u32__rotate_left(a12 ^ d12, 23U)};
  uint32_t bx22 = uu____4.fst;
  uint32_t bx32 = uu____4.snd;
  uint32_t a22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d22 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d32 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t d42 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____5 = {.fst = core_num__u32__rotate_left(a22 ^ d22, 31U),
                         .snd = core_num__u32__rotate_left(a32 ^ d32, 14U),
                         .thd = core_num__u32__rotate_left(a42 ^ d42, 10U)};
  uint32_t bx42 = uu____5.fst;
  uint32_t bx02 = uu____5.snd;
  uint32_t bx12 = uu____5.thd;
  uint32_t ax02 = bx02 ^ (~bx12 & bx22);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax02);
  uint32_t ax11 = bx12 ^ (~bx22 & bx32);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax11);
  uint32_t ax21 = bx22 ^ (~bx32 & bx42);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax21);
  uint32_t ax31 = bx32 ^ (~bx42 & bx02);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax31);
  uint32_t ax41 = bx42 ^ (~bx02 & bx12);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax41);
  uint32_t a02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____6.fst;
  uint32_t bx3 = uu____6.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____7.fst;
  uint32_t bx0 = uu____7.snd;
  uint32_t bx1 = uu____7.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax12 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 20
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_4rounds_fc(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_fc(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_fc(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_fc(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_fc(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(s);
}

KRML_NOINLINE void libcrux_iot_sha3_keccak_keccakf1600(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_4rounds_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_4rounds_23(s);
  libcrux_iot_sha3_keccak_keccakf1600_4rounds_70(s);
  libcrux_iot_sha3_keccak_keccakf1600_4rounds_60(s);
  libcrux_iot_sha3_keccak_keccakf1600_4rounds_18(s);
  libcrux_iot_sha3_keccak_keccakf1600_4rounds_fc(s);
  s->i = (size_t)0U;
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0
libcrux_iot_sha3_lane_deinterleave_8d(Eurydice_arr_a0 self) {
  uint32_t even_bits = self.data[0U];
  uint32_t odd_bits = self.data[1U];
  uint32_t even_spaced_lo = even_bits & 65535U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 16U) & 65535U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 8U) & 16711935U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 4U) & 252645135U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 2U) & 858993459U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 1U) & 1431655765U;
  uint32_t even_spaced_hi = even_bits >> 16U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 16U) & 65535U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 8U) & 16711935U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 4U) & 252645135U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 2U) & 858993459U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 1U) & 1431655765U;
  uint32_t odd_spaced_lo = odd_bits & 65535U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 16U) & 65535U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 8U) & 16711935U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 4U) & 252645135U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 2U) & 858993459U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 1U) & 1431655765U;
  uint32_t odd_spaced_hi = odd_bits >> 16U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 16U) & 65535U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 8U) & 16711935U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 4U) & 252645135U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 2U) & 858993459U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 1U) & 1431655765U;
  return (KRML_CLITERAL(Eurydice_arr_a0){
      .data = {even_spaced_lo | odd_spaced_lo << 1U,
               even_spaced_hi | odd_spaced_hi << 1U}});
}

typedef struct const_size_t__x2_s {
  const size_t *fst;
  const size_t *snd;
} const_size_t__x2;

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_c6(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_c0 state_flat;
  Eurydice_arr_a0 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_a0));
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U, .end = (size_t)72U / (size_t)8U}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
        size_t i0 = i;
        Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U);
        libcrux_iot_sha3_state_set_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U,
            libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
                .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)0U)[0U],
                         libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)1U)[0U]}})));
      }
      return;
    }
    size_t i = uu____0.f0;
    size_t offset = start + (size_t)8U * i;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 uu____1 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    state_flat.data[i] = uu____1;
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_c6(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_c6(
      state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_c6(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_c6(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 72
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_dc(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)72U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_c6(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_c6(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_c6(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_c6(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_c6(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_c6(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_c6(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_c6(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_c6(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_c6(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_c6(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_c6(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_c6(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_c6(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_c6(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_c6(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_c6(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_c6(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_c6(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_c6(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 72
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_dc(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)72U;
  size_t rem = data.meta % (size_t)72U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                  .end = n}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      libcrux_iot_sha3_keccak_absorb_final_dc(&s, data, data.meta - rem, rem);
      if (blocks == (size_t)0U) {
        libcrux_iot_sha3_keccak_squeeze_first_and_last_c6(&s, out);
      } else {
        libcrux_iot_sha3_keccak_squeeze_first_block_c6(&s, out);
        size_t offset = (size_t)72U;
        for (size_t i = (size_t)1U; i < blocks; i++) {
          libcrux_iot_sha3_keccak_squeeze_next_block_c6(
              &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
          offset += (size_t)72U;
        }
        if (last < outlen) {
          const_size_t__x2 uu____1 = {.fst = &last, .snd = &offset};
          EURYDICE_ASSERT(uu____1.fst[0U] == uu____1.snd[0U], "panic!");
          libcrux_iot_sha3_keccak_squeeze_last_c6(
              s, Eurydice_slice_subslice_from_mut_6d(out, offset));
        }
      }
      return;
    }
    size_t i = uu____0.f0;
    libcrux_iot_sha3_keccak_absorb_block_c6(&s, data, i * (size_t)72U);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 72
- DELIM= 6
*/
void keccakx1_dc(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_dc(data, out);
}

/**
 Writes SHA3-512 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_512_DIGEST_SIZE`] bytes long
*/
void sha512_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload) {
  keccakx1_dc(payload, digest);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_b2(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_c0 state_flat;
  Eurydice_arr_a0 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_a0));
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U, .end = (size_t)136U / (size_t)8U}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
        size_t i0 = i;
        Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U);
        libcrux_iot_sha3_state_set_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U,
            libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
                .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)0U)[0U],
                         libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)1U)[0U]}})));
      }
      return;
    }
    size_t i = uu____0.f0;
    size_t offset = start + (size_t)8U * i;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 uu____1 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    state_flat.data[i] = uu____1;
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_b2(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_b2(
      state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_b2(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_b2(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_22(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)136U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_b2(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_b2(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_b2(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_b2(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_b2(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_b2(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_b2(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_b2(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_b2(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_b2(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_b2(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_b2(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_b2(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_b2(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_b2(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_b2(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_b2(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_b2(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_b2(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_b2(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_22(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)136U;
  size_t rem = data.meta % (size_t)136U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                  .end = n}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      libcrux_iot_sha3_keccak_absorb_final_22(&s, data, data.meta - rem, rem);
      if (blocks == (size_t)0U) {
        libcrux_iot_sha3_keccak_squeeze_first_and_last_b2(&s, out);
      } else {
        libcrux_iot_sha3_keccak_squeeze_first_block_b2(&s, out);
        size_t offset = (size_t)136U;
        for (size_t i = (size_t)1U; i < blocks; i++) {
          libcrux_iot_sha3_keccak_squeeze_next_block_b2(
              &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
          offset += (size_t)136U;
        }
        if (last < outlen) {
          const_size_t__x2 uu____1 = {.fst = &last, .snd = &offset};
          EURYDICE_ASSERT(uu____1.fst[0U] == uu____1.snd[0U], "panic!");
          libcrux_iot_sha3_keccak_squeeze_last_b2(
              s, Eurydice_slice_subslice_from_mut_6d(out, offset));
        }
      }
      return;
    }
    size_t i = uu____0.f0;
    libcrux_iot_sha3_keccak_absorb_block_b2(&s, data, i * (size_t)136U);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 136
- DELIM= 6
*/
void keccakx1_22(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_22(data, out);
}

/**
 Writes SHA3-256 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_256_DIGEST_SIZE`] bytes long
*/
void sha256_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload) {
  keccakx1_22(payload, digest);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_220(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(31U);
  size_t uu____0 = (size_t)136U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_b2(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_220(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)136U;
  size_t rem = data.meta % (size_t)136U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                  .end = n}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      libcrux_iot_sha3_keccak_absorb_final_220(&s, data, data.meta - rem, rem);
      if (blocks == (size_t)0U) {
        libcrux_iot_sha3_keccak_squeeze_first_and_last_b2(&s, out);
      } else {
        libcrux_iot_sha3_keccak_squeeze_first_block_b2(&s, out);
        size_t offset = (size_t)136U;
        for (size_t i = (size_t)1U; i < blocks; i++) {
          libcrux_iot_sha3_keccak_squeeze_next_block_b2(
              &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
          offset += (size_t)136U;
        }
        if (last < outlen) {
          const_size_t__x2 uu____1 = {.fst = &last, .snd = &offset};
          EURYDICE_ASSERT(uu____1.fst[0U] == uu____1.snd[0U], "panic!");
          libcrux_iot_sha3_keccak_squeeze_last_b2(
              s, Eurydice_slice_subslice_from_mut_6d(out, offset));
        }
      }
      return;
    }
    size_t i = uu____0.f0;
    libcrux_iot_sha3_keccak_absorb_block_b2(&s, data, i * (size_t)136U);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 136
- DELIM= 31
*/
void keccakx1_220(Eurydice_borrow_slice_u8 data,
                  Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_220(data, out);
}

/**
 Writes SHAKE256 digest of input payload to externally allocated buffer.

 Writes `out.len()` bytes.

 Preconditions:
 - `out` is at most `u32::MAX` bytes long
*/
void shake256_ema(Eurydice_mut_borrow_slice_u8 out,
                  Eurydice_borrow_slice_u8 data) {
  keccakx1_220(data, out);
}

/**
 Create a new SHAKE-128 state object.
*/
libcrux_iot_sha3_state_KeccakState libcrux_iot_sha3_incremental_shake128_init(
    void) {
  return libcrux_iot_sha3_state_new_18();
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_60(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_c0 state_flat;
  Eurydice_arr_a0 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_a0));
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U, .end = (size_t)168U / (size_t)8U}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
        size_t i0 = i;
        Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U);
        libcrux_iot_sha3_state_set_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U,
            libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
                .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)0U)[0U],
                         libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)1U)[0U]}})));
      }
      return;
    }
    size_t i = uu____0.f0;
    size_t offset = start + (size_t)8U * i;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 uu____1 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    state_flat.data[i] = uu____1;
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_60(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_60(
      state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_60(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_60(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 168
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_37(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(31U);
  size_t uu____0 = (size_t)168U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_60(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
 Absorb
*/
void libcrux_iot_sha3_incremental_shake128_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 data0) {
  libcrux_iot_sha3_keccak_absorb_final_37(s, data0, (size_t)0U, data0.meta);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_60(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_60(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_60(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_60(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_60(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_60(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_three_blocks
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_three_blocks_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_squeeze_first_block_60(s, out);
  libcrux_iot_sha3_keccak_squeeze_next_block_60(
      s, Eurydice_slice_subslice_from_mut_6d(out, (size_t)168U));
  libcrux_iot_sha3_keccak_squeeze_next_block_60(
      s, Eurydice_slice_subslice_from_mut_6d(out, (size_t)2U * (size_t)168U));
}

/**
 Squeeze three blocks
*/
void libcrux_iot_sha3_incremental_shake128_squeeze_first_three_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0) {
  libcrux_iot_sha3_keccak_squeeze_first_three_blocks_60(s, out0);
}

/**
 Squeeze another block
*/
void libcrux_iot_sha3_incremental_shake128_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0) {
  libcrux_iot_sha3_keccak_squeeze_next_block_60(s, out0);
}

/**
 Returns the size of a digest in bytes for a given [`Algorithm`].
*/
size_t digest_size(Algorithm mode) {
  switch (mode) {
    case libcrux_iot_sha3_Algorithm_Sha224: {
      break;
    }
    case libcrux_iot_sha3_Algorithm_Sha256: {
      return SHA3_256_DIGEST_SIZE;
    }
    case libcrux_iot_sha3_Algorithm_Sha384: {
      return SHA3_384_DIGEST_SIZE;
    }
    case libcrux_iot_sha3_Algorithm_Sha512: {
      return SHA3_512_DIGEST_SIZE;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return SHA3_224_DIGEST_SIZE;
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_9e(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_c0 state_flat;
  Eurydice_arr_a0 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_a0));
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U, .end = (size_t)144U / (size_t)8U}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
        size_t i0 = i;
        Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U);
        libcrux_iot_sha3_state_set_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U,
            libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
                .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)0U)[0U],
                         libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)1U)[0U]}})));
      }
      return;
    }
    size_t i = uu____0.f0;
    size_t offset = start + (size_t)8U * i;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 uu____1 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    state_flat.data[i] = uu____1;
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_9e(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_9e(
      state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_9e(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_9e(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 144
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)144U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_9e(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_9e(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_9e(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_9e(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_9e(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_9e(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_9e(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_9e(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_9e(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_9e(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_9e(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_9e(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_9e(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_9e(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_9e(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_9e(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_9e(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_9e(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_9e(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_9e(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 144
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_3a(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)144U;
  size_t rem = data.meta % (size_t)144U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                  .end = n}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      libcrux_iot_sha3_keccak_absorb_final_3a(&s, data, data.meta - rem, rem);
      if (blocks == (size_t)0U) {
        libcrux_iot_sha3_keccak_squeeze_first_and_last_9e(&s, out);
      } else {
        libcrux_iot_sha3_keccak_squeeze_first_block_9e(&s, out);
        size_t offset = (size_t)144U;
        for (size_t i = (size_t)1U; i < blocks; i++) {
          libcrux_iot_sha3_keccak_squeeze_next_block_9e(
              &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
          offset += (size_t)144U;
        }
        if (last < outlen) {
          const_size_t__x2 uu____1 = {.fst = &last, .snd = &offset};
          EURYDICE_ASSERT(uu____1.fst[0U] == uu____1.snd[0U], "panic!");
          libcrux_iot_sha3_keccak_squeeze_last_9e(
              s, Eurydice_slice_subslice_from_mut_6d(out, offset));
        }
      }
      return;
    }
    size_t i = uu____0.f0;
    libcrux_iot_sha3_keccak_absorb_block_9e(&s, data, i * (size_t)144U);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 144
- DELIM= 6
*/
void keccakx1_3a(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_3a(data, out);
}

/**
 Writes SHA3-224 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_224_DIGEST_SIZE`] bytes long
*/
void sha224_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload) {
  keccakx1_3a(payload, digest);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_53(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_c0 state_flat;
  Eurydice_arr_a0 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_a0));
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U, .end = (size_t)104U / (size_t)8U}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
        size_t i0 = i;
        Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U);
        libcrux_iot_sha3_state_set_lane_18(
            state, i0 / (size_t)5U, i0 % (size_t)5U,
            libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
                .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)0U)[0U],
                         libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                             libcrux_iot_sha3_lane_index_cc(
                                 &state_flat.data[i0], (size_t)1U)[0U]}})));
      }
      return;
    }
    size_t i = uu____0.f0;
    size_t offset = start + (size_t)8U * i;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 uu____1 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    state_flat.data[i] = uu____1;
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_53(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_53(
      state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_53(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_53(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 104
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_dc0(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)104U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_53(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_53(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_53(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_53(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_53(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_53(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_53(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_53(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_53(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_53(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_53(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_53(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_53(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_53(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_53(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_53(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_53(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_53(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_53(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_53(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 104
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_dc0(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)104U;
  size_t rem = data.meta % (size_t)104U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                  .end = n}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      libcrux_iot_sha3_keccak_absorb_final_dc0(&s, data, data.meta - rem, rem);
      if (blocks == (size_t)0U) {
        libcrux_iot_sha3_keccak_squeeze_first_and_last_53(&s, out);
      } else {
        libcrux_iot_sha3_keccak_squeeze_first_block_53(&s, out);
        size_t offset = (size_t)104U;
        for (size_t i = (size_t)1U; i < blocks; i++) {
          libcrux_iot_sha3_keccak_squeeze_next_block_53(
              &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
          offset += (size_t)104U;
        }
        if (last < outlen) {
          const_size_t__x2 uu____1 = {.fst = &last, .snd = &offset};
          EURYDICE_ASSERT(uu____1.fst[0U] == uu____1.snd[0U], "panic!");
          libcrux_iot_sha3_keccak_squeeze_last_53(
              s, Eurydice_slice_subslice_from_mut_6d(out, offset));
        }
      }
      return;
    }
    size_t i = uu____0.f0;
    libcrux_iot_sha3_keccak_absorb_block_53(&s, data, i * (size_t)104U);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 104
- DELIM= 6
*/
void keccakx1_dc0(Eurydice_borrow_slice_u8 data,
                  Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_dc0(data, out);
}

/**
 Writes SHA3-384 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_384_DIGEST_SIZE`] bytes long
*/
void sha384_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload) {
  keccakx1_dc0(payload, digest);
}

/**
 Returns SHA3-224 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_a2 sha224(Eurydice_borrow_slice_u8 payload) {
  Eurydice_arr_a2 out = libcrux_secrets_int_public_integers_classify_27_96(
      (KRML_CLITERAL(Eurydice_arr_a2){.data = {0U}}));
  sha224_ema(Eurydice_array_to_slice_mut_5e(&out), payload);
  return out;
}

/**
 Returns SHA3-256 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_ec sha256(Eurydice_borrow_slice_u8 data) {
  Eurydice_arr_ec out = libcrux_secrets_int_public_integers_classify_27_4b(
      (KRML_CLITERAL(Eurydice_arr_ec){.data = {0U}}));
  sha256_ema(Eurydice_array_to_slice_mut_01(&out), data);
  return out;
}

/**
 Returns SHA3-384 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_65 sha384(Eurydice_borrow_slice_u8 data) {
  Eurydice_arr_65 out = libcrux_secrets_int_public_integers_classify_27_69(
      (KRML_CLITERAL(Eurydice_arr_65){.data = {0U}}));
  sha384_ema(Eurydice_array_to_slice_mut_9f(&out), data);
  return out;
}

/**
 Returns SHA3-512 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_c7 sha512(Eurydice_borrow_slice_u8 data) {
  Eurydice_arr_c7 out = libcrux_secrets_int_public_integers_classify_27_56(
      (KRML_CLITERAL(Eurydice_arr_c7){.data = {0U}}));
  sha512_ema(Eurydice_array_to_slice_mut_17(&out), data);
  return out;
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_60(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_60(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_60(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_60(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_60(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_60(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_60(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_60(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_60(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_60(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_60(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 168
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_37(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)168U;
  size_t rem = data.meta % (size_t)168U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  core_ops_range_Range_87 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                  .end = n}),
          core_ops_range_Range_87, size_t, core_ops_range_Range_87);
  while (true) {
    core_option_Option_87 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, core_option_Option_87);
    if (uu____0.tag == core_option_None) {
      libcrux_iot_sha3_keccak_absorb_final_37(&s, data, data.meta - rem, rem);
      if (blocks == (size_t)0U) {
        libcrux_iot_sha3_keccak_squeeze_first_and_last_60(&s, out);
      } else {
        libcrux_iot_sha3_keccak_squeeze_first_block_60(&s, out);
        size_t offset = (size_t)168U;
        for (size_t i = (size_t)1U; i < blocks; i++) {
          libcrux_iot_sha3_keccak_squeeze_next_block_60(
              &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
          offset += (size_t)168U;
        }
        if (last < outlen) {
          const_size_t__x2 uu____1 = {.fst = &last, .snd = &offset};
          EURYDICE_ASSERT(uu____1.fst[0U] == uu____1.snd[0U], "panic!");
          libcrux_iot_sha3_keccak_squeeze_last_60(
              s, Eurydice_slice_subslice_from_mut_6d(out, offset));
        }
      }
      return;
    }
    size_t i = uu____0.f0;
    libcrux_iot_sha3_keccak_absorb_block_60(&s, data, i * (size_t)168U);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 168
- DELIM= 31
*/
void keccakx1_37(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_37(data, out);
}

/**
 Writes SHAKE-128 digest of input payload to externally allocated buffer.

 Writes `out.len()` bytes

 Preconditions:
 - `out` is at most `u32::MAX` bytes long
*/
void shake128_ema(Eurydice_mut_borrow_slice_u8 out,
                  Eurydice_borrow_slice_u8 data) {
  keccakx1_37(data, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_five_blocks
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_five_blocks_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_squeeze_first_block_60(s, out);
  libcrux_iot_sha3_keccak_squeeze_next_block_60(
      s, Eurydice_slice_subslice_from_mut_6d(out, (size_t)168U));
  libcrux_iot_sha3_keccak_squeeze_next_block_60(
      s, Eurydice_slice_subslice_from_mut_6d(out, (size_t)2U * (size_t)168U));
  libcrux_iot_sha3_keccak_squeeze_next_block_60(
      s, Eurydice_slice_subslice_from_mut_6d(out, (size_t)3U * (size_t)168U));
  libcrux_iot_sha3_keccak_squeeze_next_block_60(
      s, Eurydice_slice_subslice_from_mut_6d(out, (size_t)4U * (size_t)168U));
}

/**
 Squeeze five blocks
*/
void libcrux_iot_sha3_incremental_shake128_squeeze_first_five_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0) {
  libcrux_iot_sha3_keccak_squeeze_first_five_blocks_60(s, out0);
}

/**
 Absorb some data for SHAKE-256 for the last time
*/
void libcrux_iot_sha3_incremental_shake256_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_keccak_absorb_final_220(s, data, (size_t)0U, data.meta);
}

/**
 Create a new SHAKE-256 state object.
*/
KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_incremental_shake256_init(void) {
  return libcrux_iot_sha3_state_new_18();
}

/**
 Squeeze the first SHAKE-256 block
*/
void libcrux_iot_sha3_incremental_shake256_squeeze_first_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_squeeze_first_block_b2(&s[0U], out);
}

/**
 Squeeze the next SHAKE-256 block
*/
void libcrux_iot_sha3_incremental_shake256_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_squeeze_next_block_b2(s, out);
}
