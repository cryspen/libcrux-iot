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
 * Libcrux: 1ad7c25705450131b575043e252c944035898962
 */

#include "internal/libcrux_iot_sha3.h"

#include "internal/libcrux_iot_mldsa_core.h"
#include "libcrux_iot_mldsa_core.h"

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_b2
libcrux_iot_sha3_lane_from_ints_8d(Eurydice_arr_b2 value) {
  return value;
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_b2 libcrux_iot_sha3_lane_zero_8d(void) {
  return libcrux_iot_sha3_lane_from_ints_8d(
      libcrux_secrets_int_public_integers_classify_27_54(
          (KRML_CLITERAL(Eurydice_arr_b2){.data = {0U}})));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_state_new_18(void) {
  Eurydice_arr_f8 uu____0;
  Eurydice_arr_b2 repeat_expression0[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression0[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(uu____0.data, repeat_expression0,
         (size_t)25U * sizeof(Eurydice_arr_b2));
  Eurydice_arr_6c uu____1;
  Eurydice_arr_b2 repeat_expression1[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression1[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(uu____1.data, repeat_expression1,
         (size_t)5U * sizeof(Eurydice_arr_b2));
  libcrux_iot_sha3_state_KeccakState lit;
  lit.st = uu____0;
  lit.c = uu____1;
  Eurydice_arr_b2 repeat_expression[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(lit.d.data, repeat_expression, (size_t)5U * sizeof(Eurydice_arr_b2));
  lit.i = (size_t)0U;
  return lit;
}

/**
 Create a new SHAKE-256 state object.
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_portable_incremental_shake256_init(void) {
  return libcrux_iot_sha3_state_new_18();
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE Eurydice_arr_b2 libcrux_iot_sha3_state_get_lane_18(
    const libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j) {
  return self->st.data[(size_t)5U * j + i];
}

/**
This function found in impl {core::ops::index::Index<usize, u32> for
libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE const uint32_t *libcrux_iot_sha3_lane_index_cc(
    const Eurydice_arr_b2 *self, size_t index) {
  return &self->data[index];
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_set_lane_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    Eurydice_arr_b2 lane) {
  self->st.data[(size_t)5U * j + i] = lane;
}

/**
This function found in impl {core::convert::From<@Array<u32, 2usize>> for
libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_b2
libcrux_iot_sha3_lane_from_47(Eurydice_arr_b2 value) {
  return value;
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_b2
libcrux_iot_sha3_lane_interleave_8d(Eurydice_arr_b2 self) {
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
  return libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_b2){
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
This function found in impl {core::ops::index::IndexMut<usize, u32> for
libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE uint32_t *libcrux_iot_sha3_lane_index_mut_c5(
    Eurydice_arr_b2 *self, size_t index) {
  return &self->data[index];
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_set_with_zeta_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j, size_t zeta,
    uint32_t v) {
  libcrux_iot_sha3_lane_index_mut_c5(&self->st.data[(size_t)5U * j + i],
                                     zeta)[0U] = v;
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

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round0
with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_bc(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t ax_20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t ax_30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t ax_40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(s->c.data, (size_t)0U)[0U] =
      (((ax_0 ^ ax_10) ^ ax_20) ^ ax_30) ^ ax_40;
  uint32_t ax_00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t ax_21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t ax_31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t ax_41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(s->c.data, (size_t)1U)[0U] =
      (((ax_00 ^ ax_11) ^ ax_21) ^ ax_31) ^ ax_41;
  uint32_t ax_01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[1U], (size_t)0U)[0U] =
      (((ax_01 ^ ax_12) ^ ax_22) ^ ax_32) ^ ax_42;
  uint32_t ax_02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[1U], (size_t)1U)[0U] =
      (((ax_02 ^ ax_13) ^ ax_23) ^ ax_33) ^ ax_43;
  uint32_t ax_03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t ax_14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t ax_24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t ax_34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[2U], (size_t)0U)[0U] =
      (((ax_03 ^ ax_14) ^ ax_24) ^ ax_34) ^ ax_44;
  uint32_t ax_04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t ax_15 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t ax_25 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t ax_35 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_45 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[2U], (size_t)1U)[0U] =
      (((ax_04 ^ ax_15) ^ ax_25) ^ ax_35) ^ ax_45;
  uint32_t ax_05 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t ax_16 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t ax_26 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_36 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t ax_46 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[3U], (size_t)0U)[0U] =
      (((ax_05 ^ ax_16) ^ ax_26) ^ ax_36) ^ ax_46;
  uint32_t ax_06 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t ax_17 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t ax_27 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_37 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t ax_47 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[3U], (size_t)1U)[0U] =
      (((ax_06 ^ ax_17) ^ ax_27) ^ ax_37) ^ ax_47;
  uint32_t ax_07 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t ax_18 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_28 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t ax_38 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t ax_48 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[4U], (size_t)0U)[0U] =
      (((ax_07 ^ ax_18) ^ ax_28) ^ ax_38) ^ ax_48;
  uint32_t ax_08 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[4U], (size_t)1U)[0U] =
      (((ax_08 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4;
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
  libcrux_iot_sha3_lane_index_mut_c5(s->d.data, (size_t)0U)[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[2U], (size_t)1U)[0U] =
      d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[4U], (size_t)0U)[0U] =
      d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[1U], (size_t)1U)[0U] =
      d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[3U], (size_t)0U)[0U] =
      d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(s->d.data, (size_t)1U)[0U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[2U], (size_t)0U)[0U] =
      d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[4U], (size_t)1U)[0U] =
      d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[1U], (size_t)0U)[0U] =
      d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[3U], (size_t)1U)[0U] =
      d_x3_zeta1;
  size_t i = s->i;
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
  uint32_t ax00 = (bx00 ^ (~bx10 & bx20)) ^
                  LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[i];
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
  uint32_t ax01 = (bx01 ^ (~bx11 & bx21)) ^
                  LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[i];
  s->i = i + (size_t)1U;
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
  uint32_t d03 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d13 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d03, 1U),
                         .snd = core_num__u32__rotate_left(a13 ^ d13, 22U)};
  uint32_t bx23 = uu____6.fst;
  uint32_t bx33 = uu____6.snd;
  uint32_t a23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d23 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d33 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t d43 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a23 ^ d23, 30U),
                         .snd = core_num__u32__rotate_left(a33 ^ d33, 14U),
                         .thd = core_num__u32__rotate_left(a43 ^ d43, 10U)};
  uint32_t bx43 = uu____7.fst;
  uint32_t bx03 = uu____7.snd;
  uint32_t bx13 = uu____7.thd;
  uint32_t ax03 = bx03 ^ (~bx13 & bx23);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax03);
  uint32_t ax12 = bx13 ^ (~bx23 & bx33);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx23 ^ (~bx33 & bx43);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx33 ^ (~bx43 & bx03);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx43 ^ (~bx03 & bx13);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
  uint32_t a03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d04 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d14 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____8 = {.fst = core_num__u32__rotate_left(a03 ^ d04, 9U),
                         .snd = core_num__u32__rotate_left(a14 ^ d14, 1U)};
  uint32_t bx44 = uu____8.fst;
  uint32_t bx04 = uu____8.snd;
  uint32_t a24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t d24 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t d34 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d44 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____9 = {.fst = core_num__u32__rotate_left(a24 ^ d24, 3U),
                         .snd = core_num__u32__rotate_left(a34 ^ d34, 13U),
                         .thd = core_num__u32__rotate_left(a44 ^ d44, 4U)};
  uint32_t bx14 = uu____9.fst;
  uint32_t bx24 = uu____9.snd;
  uint32_t bx34 = uu____9.thd;
  uint32_t ax04 = bx04 ^ (~bx14 & bx24);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax04);
  uint32_t ax13 = bx14 ^ (~bx24 & bx34);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax13);
  uint32_t ax23 = bx24 ^ (~bx34 & bx44);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax23);
  uint32_t ax33 = bx34 ^ (~bx44 & bx04);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax33);
  uint32_t ax43 = bx44 ^ (~bx04 & bx14);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax43);
  uint32_t a04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d05 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a15 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d15 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____10 = {.fst = core_num__u32__rotate_left(a04 ^ d05, 9U),
                          .snd = core_num__u32__rotate_left(a15 ^ d15, 0U)};
  uint32_t bx45 = uu____10.fst;
  uint32_t bx05 = uu____10.snd;
  uint32_t a25 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d25 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a35 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t d35 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a45 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d45 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____11 = {.fst = core_num__u32__rotate_left(a25 ^ d25, 3U),
                          .snd = core_num__u32__rotate_left(a35 ^ d35, 12U),
                          .thd = core_num__u32__rotate_left(a45 ^ d45, 4U)};
  uint32_t bx15 = uu____11.fst;
  uint32_t bx25 = uu____11.snd;
  uint32_t bx35 = uu____11.thd;
  uint32_t ax05 = bx05 ^ (~bx15 & bx25);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax05);
  uint32_t ax14 = bx15 ^ (~bx25 & bx35);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax14);
  uint32_t ax24 = bx25 ^ (~bx35 & bx45);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax24);
  uint32_t ax34 = bx35 ^ (~bx45 & bx05);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax34);
  uint32_t ax44 = bx45 ^ (~bx05 & bx15);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax44);
  uint32_t a05 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d06 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a16 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d16 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____12 = {.fst = core_num__u32__rotate_left(a05 ^ d06, 18U),
                          .snd = core_num__u32__rotate_left(a16 ^ d16, 5U)};
  uint32_t bx16 = uu____12.fst;
  uint32_t bx26 = uu____12.snd;
  uint32_t a26 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t d26 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a36 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d36 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a46 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d46 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____13 = {.fst = core_num__u32__rotate_left(a26 ^ d26, 8U),
                          .snd = core_num__u32__rotate_left(a36 ^ d36, 28U),
                          .thd = core_num__u32__rotate_left(a46 ^ d46, 14U)};
  uint32_t bx36 = uu____13.fst;
  uint32_t bx46 = uu____13.snd;
  uint32_t bx06 = uu____13.thd;
  uint32_t ax06 = bx06 ^ (~bx16 & bx26);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax06);
  uint32_t ax15 = bx16 ^ (~bx26 & bx36);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax15);
  uint32_t ax25 = bx26 ^ (~bx36 & bx46);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax25);
  uint32_t ax35 = bx36 ^ (~bx46 & bx06);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax35);
  uint32_t ax45 = bx46 ^ (~bx06 & bx16);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax45);
  uint32_t a06 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d07 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a17 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d17 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____14 = {.fst = core_num__u32__rotate_left(a06 ^ d07, 18U),
                          .snd = core_num__u32__rotate_left(a17 ^ d17, 5U)};
  uint32_t bx17 = uu____14.fst;
  uint32_t bx27 = uu____14.snd;
  uint32_t a27 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t d27 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a37 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t d37 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a47 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d47 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____15 = {.fst = core_num__u32__rotate_left(a27 ^ d27, 7U),
                          .snd = core_num__u32__rotate_left(a37 ^ d37, 28U),
                          .thd = core_num__u32__rotate_left(a47 ^ d47, 13U)};
  uint32_t bx37 = uu____15.fst;
  uint32_t bx47 = uu____15.snd;
  uint32_t bx07 = uu____15.thd;
  uint32_t ax07 = bx07 ^ (~bx17 & bx27);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax07);
  uint32_t ax16 = bx17 ^ (~bx27 & bx37);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax16);
  uint32_t ax26 = bx27 ^ (~bx37 & bx47);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax26);
  uint32_t ax36 = bx37 ^ (~bx47 & bx07);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax36);
  uint32_t ax46 = bx47 ^ (~bx07 & bx17);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax46);
  uint32_t a07 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d08 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a18 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  uint32_t d18 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____16 = {.fst = core_num__u32__rotate_left(a07 ^ d08, 21U),
                          .snd = core_num__u32__rotate_left(a18 ^ d18, 1U)};
  uint32_t bx38 = uu____16.fst;
  uint32_t bx48 = uu____16.snd;
  uint32_t a28 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d28 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a38 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d38 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a48 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d48 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____17 = {.fst = core_num__u32__rotate_left(a28 ^ d28, 31U),
                          .snd = core_num__u32__rotate_left(a38 ^ d38, 28U),
                          .thd = core_num__u32__rotate_left(a48 ^ d48, 20U)};
  uint32_t bx08 = uu____17.fst;
  uint32_t bx18 = uu____17.snd;
  uint32_t bx28 = uu____17.thd;
  uint32_t ax08 = bx08 ^ (~bx18 & bx28);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax08);
  uint32_t ax17 = bx18 ^ (~bx28 & bx38);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax17);
  uint32_t ax27 = bx28 ^ (~bx38 & bx48);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax27);
  uint32_t ax37 = bx38 ^ (~bx48 & bx08);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax37);
  uint32_t ax47 = bx48 ^ (~bx08 & bx18);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax47);
  uint32_t a08 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____18 = {.fst = core_num__u32__rotate_left(a08 ^ d0, 20U),
                          .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____18.fst;
  uint32_t bx4 = uu____18.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____19 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                          .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                          .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____19.fst;
  uint32_t bx1 = uu____19.snd;
  uint32_t bx2 = uu____19.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax18 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax18);
  uint32_t ax28 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax28);
  uint32_t ax38 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax38);
  uint32_t ax48 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax48);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round1
with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_bc(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t ax_40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t ax_10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t ax_30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(s->c.data, (size_t)0U)[0U] =
      (((ax_00 ^ ax_10) ^ ax_20) ^ ax_30) ^ ax_40;
  uint32_t ax_01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t ax_41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t ax_11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t ax_31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(s->c.data, (size_t)1U)[0U] =
      (((ax_01 ^ ax_11) ^ ax_21) ^ ax_31) ^ ax_41;
  uint32_t ax_12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[1U], (size_t)0U)[0U] =
      (((ax_02 ^ ax_12) ^ ax_22) ^ ax_32) ^ ax_42;
  uint32_t ax_13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[1U], (size_t)1U)[0U] =
      (((ax_03 ^ ax_13) ^ ax_23) ^ ax_33) ^ ax_43;
  uint32_t ax_24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t ax_44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t ax_14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t ax_34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[2U], (size_t)0U)[0U] =
      (((ax_04 ^ ax_14) ^ ax_24) ^ ax_34) ^ ax_44;
  uint32_t ax_25 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t ax_45 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t ax_15 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t ax_35 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_05 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[2U], (size_t)1U)[0U] =
      (((ax_05 ^ ax_15) ^ ax_25) ^ ax_35) ^ ax_45;
  uint32_t ax_36 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t ax_06 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t ax_26 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_46 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t ax_16 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[3U], (size_t)0U)[0U] =
      (((ax_06 ^ ax_16) ^ ax_26) ^ ax_36) ^ ax_46;
  uint32_t ax_37 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t ax_07 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t ax_27 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t ax_17 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[3U], (size_t)1U)[0U] =
      (((ax_07 ^ ax_17) ^ ax_27) ^ ax_37) ^ ax_4;
  uint32_t ax_47 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t ax_18 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_38 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t ax_08 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t ax_28 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[4U], (size_t)0U)[0U] =
      (((ax_08 ^ ax_18) ^ ax_28) ^ ax_38) ^ ax_47;
  uint32_t ax_48 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[4U], (size_t)1U)[0U] =
      (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_48;
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
  libcrux_iot_sha3_lane_index_mut_c5(s->d.data, (size_t)0U)[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[2U], (size_t)1U)[0U] =
      d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[4U], (size_t)0U)[0U] =
      d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[1U], (size_t)1U)[0U] =
      d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[3U], (size_t)0U)[0U] =
      d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(s->d.data, (size_t)1U)[0U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[2U], (size_t)0U)[0U] =
      d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[4U], (size_t)1U)[0U] =
      d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[1U], (size_t)0U)[0U] =
      d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[3U], (size_t)1U)[0U] =
      d_x3_zeta1;
  size_t i = s->i;
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
  uint32_t ax00 = (bx00 ^ (~bx10 & bx20)) ^
                  LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[i];
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
  uint32_t ax01 = (bx01 ^ (~bx11 & bx21)) ^
                  LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[i];
  s->i = i + (size_t)1U;
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
  uint32_t d03 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d13 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d03, 1U),
                         .snd = core_num__u32__rotate_left(a13 ^ d13, 22U)};
  uint32_t bx23 = uu____6.fst;
  uint32_t bx33 = uu____6.snd;
  uint32_t a23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d23 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d33 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t d43 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a23 ^ d23, 30U),
                         .snd = core_num__u32__rotate_left(a33 ^ d33, 14U),
                         .thd = core_num__u32__rotate_left(a43 ^ d43, 10U)};
  uint32_t bx43 = uu____7.fst;
  uint32_t bx03 = uu____7.snd;
  uint32_t bx13 = uu____7.thd;
  uint32_t ax03 = bx03 ^ (~bx13 & bx23);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax03);
  uint32_t ax12 = bx13 ^ (~bx23 & bx33);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax12);
  uint32_t ax22 = bx23 ^ (~bx33 & bx43);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax22);
  uint32_t ax32 = bx33 ^ (~bx43 & bx03);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx43 ^ (~bx03 & bx13);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
  uint32_t a03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d04 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d14 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____8 = {.fst = core_num__u32__rotate_left(a03 ^ d04, 9U),
                         .snd = core_num__u32__rotate_left(a14 ^ d14, 1U)};
  uint32_t bx44 = uu____8.fst;
  uint32_t bx04 = uu____8.snd;
  uint32_t a24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t d24 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t d34 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t d44 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____9 = {.fst = core_num__u32__rotate_left(a24 ^ d24, 3U),
                         .snd = core_num__u32__rotate_left(a34 ^ d34, 13U),
                         .thd = core_num__u32__rotate_left(a44 ^ d44, 4U)};
  uint32_t bx14 = uu____9.fst;
  uint32_t bx24 = uu____9.snd;
  uint32_t bx34 = uu____9.thd;
  uint32_t ax04 = bx04 ^ (~bx14 & bx24);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax04);
  uint32_t ax13 = bx14 ^ (~bx24 & bx34);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax13);
  uint32_t ax23 = bx24 ^ (~bx34 & bx44);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax23);
  uint32_t ax33 = bx34 ^ (~bx44 & bx04);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax33);
  uint32_t ax43 = bx44 ^ (~bx04 & bx14);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax43);
  uint32_t a04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d05 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a15 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d15 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____10 = {.fst = core_num__u32__rotate_left(a04 ^ d05, 9U),
                          .snd = core_num__u32__rotate_left(a15 ^ d15, 0U)};
  uint32_t bx45 = uu____10.fst;
  uint32_t bx05 = uu____10.snd;
  uint32_t a25 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d25 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a35 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t d35 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a45 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d45 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____11 = {.fst = core_num__u32__rotate_left(a25 ^ d25, 3U),
                          .snd = core_num__u32__rotate_left(a35 ^ d35, 12U),
                          .thd = core_num__u32__rotate_left(a45 ^ d45, 4U)};
  uint32_t bx15 = uu____11.fst;
  uint32_t bx25 = uu____11.snd;
  uint32_t bx35 = uu____11.thd;
  uint32_t ax05 = bx05 ^ (~bx15 & bx25);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax05);
  uint32_t ax14 = bx15 ^ (~bx25 & bx35);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax14);
  uint32_t ax24 = bx25 ^ (~bx35 & bx45);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax24);
  uint32_t ax34 = bx35 ^ (~bx45 & bx05);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax34);
  uint32_t ax44 = bx45 ^ (~bx05 & bx15);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax44);
  uint32_t a05 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d06 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a16 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d16 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____12 = {.fst = core_num__u32__rotate_left(a05 ^ d06, 18U),
                          .snd = core_num__u32__rotate_left(a16 ^ d16, 5U)};
  uint32_t bx16 = uu____12.fst;
  uint32_t bx26 = uu____12.snd;
  uint32_t a26 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t d26 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a36 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d36 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a46 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d46 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____13 = {.fst = core_num__u32__rotate_left(a26 ^ d26, 8U),
                          .snd = core_num__u32__rotate_left(a36 ^ d36, 28U),
                          .thd = core_num__u32__rotate_left(a46 ^ d46, 14U)};
  uint32_t bx36 = uu____13.fst;
  uint32_t bx46 = uu____13.snd;
  uint32_t bx06 = uu____13.thd;
  uint32_t ax06 = bx06 ^ (~bx16 & bx26);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax06);
  uint32_t ax15 = bx16 ^ (~bx26 & bx36);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax15);
  uint32_t ax25 = bx26 ^ (~bx36 & bx46);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax25);
  uint32_t ax35 = bx36 ^ (~bx46 & bx06);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax35);
  uint32_t ax45 = bx46 ^ (~bx06 & bx16);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax45);
  uint32_t a06 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d07 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a17 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t d17 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____14 = {.fst = core_num__u32__rotate_left(a06 ^ d07, 18U),
                          .snd = core_num__u32__rotate_left(a17 ^ d17, 5U)};
  uint32_t bx17 = uu____14.fst;
  uint32_t bx27 = uu____14.snd;
  uint32_t a27 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t d27 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a37 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t d37 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a47 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d47 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____15 = {.fst = core_num__u32__rotate_left(a27 ^ d27, 7U),
                          .snd = core_num__u32__rotate_left(a37 ^ d37, 28U),
                          .thd = core_num__u32__rotate_left(a47 ^ d47, 13U)};
  uint32_t bx37 = uu____15.fst;
  uint32_t bx47 = uu____15.snd;
  uint32_t bx07 = uu____15.thd;
  uint32_t ax07 = bx07 ^ (~bx17 & bx27);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax07);
  uint32_t ax16 = bx17 ^ (~bx27 & bx37);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax16);
  uint32_t ax26 = bx27 ^ (~bx37 & bx47);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax26);
  uint32_t ax36 = bx37 ^ (~bx47 & bx07);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax36);
  uint32_t ax46 = bx47 ^ (~bx07 & bx17);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax46);
  uint32_t a07 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d08 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a18 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  uint32_t d18 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____16 = {.fst = core_num__u32__rotate_left(a07 ^ d08, 21U),
                          .snd = core_num__u32__rotate_left(a18 ^ d18, 1U)};
  uint32_t bx38 = uu____16.fst;
  uint32_t bx48 = uu____16.snd;
  uint32_t a28 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d28 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a38 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d38 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a48 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d48 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____17 = {.fst = core_num__u32__rotate_left(a28 ^ d28, 31U),
                          .snd = core_num__u32__rotate_left(a38 ^ d38, 28U),
                          .thd = core_num__u32__rotate_left(a48 ^ d48, 20U)};
  uint32_t bx08 = uu____17.fst;
  uint32_t bx18 = uu____17.snd;
  uint32_t bx28 = uu____17.thd;
  uint32_t ax08 = bx08 ^ (~bx18 & bx28);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax08);
  uint32_t ax17 = bx18 ^ (~bx28 & bx38);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax17);
  uint32_t ax27 = bx28 ^ (~bx38 & bx48);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax27);
  uint32_t ax37 = bx38 ^ (~bx48 & bx08);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax37);
  uint32_t ax47 = bx48 ^ (~bx08 & bx18);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax47);
  uint32_t a08 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____18 = {.fst = core_num__u32__rotate_left(a08 ^ d0, 20U),
                          .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____18.fst;
  uint32_t bx4 = uu____18.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____19 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                          .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                          .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____19.fst;
  uint32_t bx1 = uu____19.snd;
  uint32_t bx2 = uu____19.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax18 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax18);
  uint32_t ax28 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax28);
  uint32_t ax38 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax38);
  uint32_t ax48 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax48);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round2
with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_bc(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t ax_30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t ax_20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t ax_10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(s->c.data, (size_t)0U)[0U] =
      (((ax_00 ^ ax_10) ^ ax_20) ^ ax_30) ^ ax_40;
  uint32_t ax_01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t ax_31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t ax_21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t ax_11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(s->c.data, (size_t)1U)[0U] =
      (((ax_01 ^ ax_11) ^ ax_21) ^ ax_31) ^ ax_41;
  uint32_t ax_32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[1U], (size_t)0U)[0U] =
      (((ax_02 ^ ax_12) ^ ax_22) ^ ax_32) ^ ax_42;
  uint32_t ax_33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[1U], (size_t)1U)[0U] =
      (((ax_03 ^ ax_13) ^ ax_23) ^ ax_33) ^ ax_43;
  uint32_t ax_14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t ax_04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t ax_44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t ax_34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[2U], (size_t)0U)[0U] =
      (((ax_04 ^ ax_14) ^ ax_24) ^ ax_34) ^ ax_44;
  uint32_t ax_15 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t ax_05 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t ax_45 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t ax_35 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_25 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[2U], (size_t)1U)[0U] =
      (((ax_05 ^ ax_15) ^ ax_25) ^ ax_35) ^ ax_45;
  uint32_t ax_46 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t ax_36 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t ax_26 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_16 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t ax_06 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[3U], (size_t)0U)[0U] =
      (((ax_06 ^ ax_16) ^ ax_26) ^ ax_36) ^ ax_46;
  uint32_t ax_47 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t ax_37 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_17 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t ax_07 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[3U], (size_t)1U)[0U] =
      (((ax_07 ^ ax_17) ^ ax_2) ^ ax_37) ^ ax_47;
  uint32_t ax_27 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t ax_18 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_08 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t ax_48 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t ax_38 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[4U], (size_t)0U)[0U] =
      (((ax_08 ^ ax_18) ^ ax_27) ^ ax_38) ^ ax_48;
  uint32_t ax_28 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[4U], (size_t)1U)[0U] =
      (((ax_0 ^ ax_1) ^ ax_28) ^ ax_3) ^ ax_4;
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
  libcrux_iot_sha3_lane_index_mut_c5(s->d.data, (size_t)0U)[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[2U], (size_t)1U)[0U] =
      d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[4U], (size_t)0U)[0U] =
      d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[1U], (size_t)1U)[0U] =
      d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[3U], (size_t)0U)[0U] =
      d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(s->d.data, (size_t)1U)[0U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[2U], (size_t)0U)[0U] =
      d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[4U], (size_t)1U)[0U] =
      d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[1U], (size_t)0U)[0U] =
      d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[3U], (size_t)1U)[0U] =
      d_x3_zeta1;
  size_t i = s->i;
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
  uint32_t ax00 = (bx00 ^ (~bx10 & bx20)) ^
                  LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[i];
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
  uint32_t ax01 = (bx01 ^ (~bx11 & bx21)) ^
                  LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[i];
  s->i = i + (size_t)1U;
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
  uint32_t d03 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t d13 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d03, 1U),
                         .snd = core_num__u32__rotate_left(a13 ^ d13, 22U)};
  uint32_t bx23 = uu____6.fst;
  uint32_t bx33 = uu____6.snd;
  uint32_t a23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d23 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d33 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t d43 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a23 ^ d23, 30U),
                         .snd = core_num__u32__rotate_left(a33 ^ d33, 14U),
                         .thd = core_num__u32__rotate_left(a43 ^ d43, 10U)};
  uint32_t bx43 = uu____7.fst;
  uint32_t bx03 = uu____7.snd;
  uint32_t bx13 = uu____7.thd;
  uint32_t ax03 = bx03 ^ (~bx13 & bx23);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax03);
  uint32_t ax12 = bx13 ^ (~bx23 & bx33);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx23 ^ (~bx33 & bx43);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx33 ^ (~bx43 & bx03);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax32);
  uint32_t ax42 = bx43 ^ (~bx03 & bx13);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
  uint32_t a03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t d04 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d14 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____8 = {.fst = core_num__u32__rotate_left(a03 ^ d04, 9U),
                         .snd = core_num__u32__rotate_left(a14 ^ d14, 1U)};
  uint32_t bx44 = uu____8.fst;
  uint32_t bx04 = uu____8.snd;
  uint32_t a24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t d24 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t d34 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t d44 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____9 = {.fst = core_num__u32__rotate_left(a24 ^ d24, 3U),
                         .snd = core_num__u32__rotate_left(a34 ^ d34, 13U),
                         .thd = core_num__u32__rotate_left(a44 ^ d44, 4U)};
  uint32_t bx14 = uu____9.fst;
  uint32_t bx24 = uu____9.snd;
  uint32_t bx34 = uu____9.thd;
  uint32_t ax04 = bx04 ^ (~bx14 & bx24);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax04);
  uint32_t ax13 = bx14 ^ (~bx24 & bx34);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax13);
  uint32_t ax23 = bx24 ^ (~bx34 & bx44);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax23);
  uint32_t ax33 = bx34 ^ (~bx44 & bx04);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax33);
  uint32_t ax43 = bx44 ^ (~bx04 & bx14);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax43);
  uint32_t a04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t d05 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a15 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d15 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____10 = {.fst = core_num__u32__rotate_left(a04 ^ d05, 9U),
                          .snd = core_num__u32__rotate_left(a15 ^ d15, 0U)};
  uint32_t bx45 = uu____10.fst;
  uint32_t bx05 = uu____10.snd;
  uint32_t a25 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t d25 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a35 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t d35 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a45 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d45 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____11 = {.fst = core_num__u32__rotate_left(a25 ^ d25, 3U),
                          .snd = core_num__u32__rotate_left(a35 ^ d35, 12U),
                          .thd = core_num__u32__rotate_left(a45 ^ d45, 4U)};
  uint32_t bx15 = uu____11.fst;
  uint32_t bx25 = uu____11.snd;
  uint32_t bx35 = uu____11.thd;
  uint32_t ax05 = bx05 ^ (~bx15 & bx25);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax05);
  uint32_t ax14 = bx15 ^ (~bx25 & bx35);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax14);
  uint32_t ax24 = bx25 ^ (~bx35 & bx45);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax24);
  uint32_t ax34 = bx35 ^ (~bx45 & bx05);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax34);
  uint32_t ax44 = bx45 ^ (~bx05 & bx15);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax44);
  uint32_t a05 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d06 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a16 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d16 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____12 = {.fst = core_num__u32__rotate_left(a05 ^ d06, 18U),
                          .snd = core_num__u32__rotate_left(a16 ^ d16, 5U)};
  uint32_t bx16 = uu____12.fst;
  uint32_t bx26 = uu____12.snd;
  uint32_t a26 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t d26 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a36 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t d36 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a46 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d46 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____13 = {.fst = core_num__u32__rotate_left(a26 ^ d26, 8U),
                          .snd = core_num__u32__rotate_left(a36 ^ d36, 28U),
                          .thd = core_num__u32__rotate_left(a46 ^ d46, 14U)};
  uint32_t bx36 = uu____13.fst;
  uint32_t bx46 = uu____13.snd;
  uint32_t bx06 = uu____13.thd;
  uint32_t ax06 = bx06 ^ (~bx16 & bx26);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax06);
  uint32_t ax15 = bx16 ^ (~bx26 & bx36);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax15);
  uint32_t ax25 = bx26 ^ (~bx36 & bx46);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax25);
  uint32_t ax35 = bx36 ^ (~bx46 & bx06);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax35);
  uint32_t ax45 = bx46 ^ (~bx06 & bx16);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax45);
  uint32_t a06 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d07 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a17 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t d17 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____14 = {.fst = core_num__u32__rotate_left(a06 ^ d07, 18U),
                          .snd = core_num__u32__rotate_left(a17 ^ d17, 5U)};
  uint32_t bx17 = uu____14.fst;
  uint32_t bx27 = uu____14.snd;
  uint32_t a27 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t d27 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a37 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t d37 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a47 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d47 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____15 = {.fst = core_num__u32__rotate_left(a27 ^ d27, 7U),
                          .snd = core_num__u32__rotate_left(a37 ^ d37, 28U),
                          .thd = core_num__u32__rotate_left(a47 ^ d47, 13U)};
  uint32_t bx37 = uu____15.fst;
  uint32_t bx47 = uu____15.snd;
  uint32_t bx07 = uu____15.thd;
  uint32_t ax07 = bx07 ^ (~bx17 & bx27);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax07);
  uint32_t ax16 = bx17 ^ (~bx27 & bx37);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax16);
  uint32_t ax26 = bx27 ^ (~bx37 & bx47);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax26);
  uint32_t ax36 = bx37 ^ (~bx47 & bx07);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax36);
  uint32_t ax46 = bx47 ^ (~bx07 & bx17);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax46);
  uint32_t a07 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d08 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a18 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  uint32_t d18 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____16 = {.fst = core_num__u32__rotate_left(a07 ^ d08, 21U),
                          .snd = core_num__u32__rotate_left(a18 ^ d18, 1U)};
  uint32_t bx38 = uu____16.fst;
  uint32_t bx48 = uu____16.snd;
  uint32_t a28 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d28 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a38 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d38 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a48 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t d48 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____17 = {.fst = core_num__u32__rotate_left(a28 ^ d28, 31U),
                          .snd = core_num__u32__rotate_left(a38 ^ d38, 28U),
                          .thd = core_num__u32__rotate_left(a48 ^ d48, 20U)};
  uint32_t bx08 = uu____17.fst;
  uint32_t bx18 = uu____17.snd;
  uint32_t bx28 = uu____17.thd;
  uint32_t ax08 = bx08 ^ (~bx18 & bx28);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax08);
  uint32_t ax17 = bx18 ^ (~bx28 & bx38);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax17);
  uint32_t ax27 = bx28 ^ (~bx38 & bx48);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax27);
  uint32_t ax37 = bx38 ^ (~bx48 & bx08);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax37);
  uint32_t ax47 = bx48 ^ (~bx08 & bx18);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax47);
  uint32_t a08 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____18 = {.fst = core_num__u32__rotate_left(a08 ^ d0, 20U),
                          .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____18.fst;
  uint32_t bx4 = uu____18.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____19 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                          .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                          .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____19.fst;
  uint32_t bx1 = uu____19.snd;
  uint32_t bx2 = uu____19.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax18 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax18);
  uint32_t ax28 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax28);
  uint32_t ax38 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax38);
  uint32_t ax48 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax48);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round3
with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_bc(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_00 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_30 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t ax_10 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t ax_40 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t ax_20 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(s->c.data, (size_t)0U)[0U] =
      (((ax_00 ^ ax_10) ^ ax_20) ^ ax_30) ^ ax_40;
  uint32_t ax_01 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_31 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t ax_11 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t ax_41 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t ax_21 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(s->c.data, (size_t)1U)[0U] =
      (((ax_01 ^ ax_11) ^ ax_21) ^ ax_31) ^ ax_41;
  uint32_t ax_22 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_02 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_32 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_12 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_42 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[1U], (size_t)0U)[0U] =
      (((ax_02 ^ ax_12) ^ ax_22) ^ ax_32) ^ ax_42;
  uint32_t ax_23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[1U], (size_t)1U)[0U] =
      (((ax_03 ^ ax_13) ^ ax_23) ^ ax_33) ^ ax_43;
  uint32_t ax_44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t ax_24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t ax_04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t ax_34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[2U], (size_t)0U)[0U] =
      (((ax_04 ^ ax_14) ^ ax_24) ^ ax_34) ^ ax_44;
  uint32_t ax_45 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t ax_25 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t ax_05 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t ax_35 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_15 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[2U], (size_t)1U)[0U] =
      (((ax_05 ^ ax_15) ^ ax_25) ^ ax_35) ^ ax_45;
  uint32_t ax_16 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t ax_46 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t ax_26 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_06 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t ax_36 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[3U], (size_t)0U)[0U] =
      (((ax_06 ^ ax_16) ^ ax_26) ^ ax_36) ^ ax_46;
  uint32_t ax_17 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t ax_47 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t ax_27 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_07 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[3U], (size_t)1U)[0U] =
      (((ax_07 ^ ax_17) ^ ax_27) ^ ax_3) ^ ax_47;
  uint32_t ax_37 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t ax_18 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_48 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t ax_28 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t ax_08 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[4U], (size_t)0U)[0U] =
      (((ax_08 ^ ax_18) ^ ax_28) ^ ax_37) ^ ax_48;
  uint32_t ax_38 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->c.data[4U], (size_t)1U)[0U] =
      (((ax_0 ^ ax_1) ^ ax_2) ^ ax_38) ^ ax_4;
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
  libcrux_iot_sha3_lane_index_mut_c5(s->d.data, (size_t)0U)[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[2U], (size_t)1U)[0U] =
      d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[4U], (size_t)0U)[0U] =
      d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[1U], (size_t)1U)[0U] =
      d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[3U], (size_t)0U)[0U] =
      d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(s->d.data, (size_t)1U)[0U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[2U], (size_t)0U)[0U] =
      d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[4U], (size_t)1U)[0U] =
      d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[1U], (size_t)0U)[0U] =
      d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  libcrux_iot_sha3_lane_index_mut_c5(&s->d.data[3U], (size_t)1U)[0U] =
      d_x3_zeta1;
  size_t i = s->i;
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
  uint32_t ax00 = (bx00 ^ (~bx10 & bx20)) ^
                  LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[i];
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
  uint32_t ax01 = (bx01 ^ (~bx11 & bx21)) ^
                  LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[i];
  s->i = i + (size_t)1U;
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
  uint32_t d03 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a13 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t d13 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____6 = {.fst = core_num__u32__rotate_left(a02 ^ d03, 1U),
                         .snd = core_num__u32__rotate_left(a13 ^ d13, 22U)};
  uint32_t bx23 = uu____6.fst;
  uint32_t bx33 = uu____6.snd;
  uint32_t a23 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t d23 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a33 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t d33 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a43 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t d43 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____7 = {.fst = core_num__u32__rotate_left(a23 ^ d23, 30U),
                         .snd = core_num__u32__rotate_left(a33 ^ d33, 14U),
                         .thd = core_num__u32__rotate_left(a43 ^ d43, 10U)};
  uint32_t bx43 = uu____7.fst;
  uint32_t bx03 = uu____7.snd;
  uint32_t bx13 = uu____7.thd;
  uint32_t ax03 = bx03 ^ (~bx13 & bx23);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax03);
  uint32_t ax12 = bx13 ^ (~bx23 & bx33);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax12);
  uint32_t ax22 = bx23 ^ (~bx33 & bx43);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax22);
  uint32_t ax32 = bx33 ^ (~bx43 & bx03);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax32);
  uint32_t ax42 = bx43 ^ (~bx03 & bx13);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax42);
  uint32_t a03 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t d04 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a14 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t d14 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____8 = {.fst = core_num__u32__rotate_left(a03 ^ d04, 9U),
                         .snd = core_num__u32__rotate_left(a14 ^ d14, 1U)};
  uint32_t bx44 = uu____8.fst;
  uint32_t bx04 = uu____8.snd;
  uint32_t a24 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t d24 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a34 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t d34 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a44 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t d44 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____9 = {.fst = core_num__u32__rotate_left(a24 ^ d24, 3U),
                         .snd = core_num__u32__rotate_left(a34 ^ d34, 13U),
                         .thd = core_num__u32__rotate_left(a44 ^ d44, 4U)};
  uint32_t bx14 = uu____9.fst;
  uint32_t bx24 = uu____9.snd;
  uint32_t bx34 = uu____9.thd;
  uint32_t ax04 = bx04 ^ (~bx14 & bx24);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax04);
  uint32_t ax13 = bx14 ^ (~bx24 & bx34);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax13);
  uint32_t ax23 = bx24 ^ (~bx34 & bx44);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax23);
  uint32_t ax33 = bx34 ^ (~bx44 & bx04);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax33);
  uint32_t ax43 = bx44 ^ (~bx04 & bx14);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax43);
  uint32_t a04 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t d05 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a15 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t d15 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____10 = {.fst = core_num__u32__rotate_left(a04 ^ d05, 9U),
                          .snd = core_num__u32__rotate_left(a15 ^ d15, 0U)};
  uint32_t bx45 = uu____10.fst;
  uint32_t bx05 = uu____10.snd;
  uint32_t a25 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t d25 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a35 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t d35 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a45 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t d45 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____11 = {.fst = core_num__u32__rotate_left(a25 ^ d25, 3U),
                          .snd = core_num__u32__rotate_left(a35 ^ d35, 12U),
                          .thd = core_num__u32__rotate_left(a45 ^ d45, 4U)};
  uint32_t bx15 = uu____11.fst;
  uint32_t bx25 = uu____11.snd;
  uint32_t bx35 = uu____11.thd;
  uint32_t ax05 = bx05 ^ (~bx15 & bx25);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax05);
  uint32_t ax14 = bx15 ^ (~bx25 & bx35);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax14);
  uint32_t ax24 = bx25 ^ (~bx35 & bx45);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax24);
  uint32_t ax34 = bx35 ^ (~bx45 & bx05);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax34);
  uint32_t ax44 = bx45 ^ (~bx05 & bx15);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax44);
  uint32_t a05 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t d06 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a16 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t d16 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____12 = {.fst = core_num__u32__rotate_left(a05 ^ d06, 18U),
                          .snd = core_num__u32__rotate_left(a16 ^ d16, 5U)};
  uint32_t bx16 = uu____12.fst;
  uint32_t bx26 = uu____12.snd;
  uint32_t a26 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t d26 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a36 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t d36 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a46 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t d46 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____13 = {.fst = core_num__u32__rotate_left(a26 ^ d26, 8U),
                          .snd = core_num__u32__rotate_left(a36 ^ d36, 28U),
                          .thd = core_num__u32__rotate_left(a46 ^ d46, 14U)};
  uint32_t bx36 = uu____13.fst;
  uint32_t bx46 = uu____13.snd;
  uint32_t bx06 = uu____13.thd;
  uint32_t ax06 = bx06 ^ (~bx16 & bx26);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax06);
  uint32_t ax15 = bx16 ^ (~bx26 & bx36);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax15);
  uint32_t ax25 = bx26 ^ (~bx36 & bx46);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax25);
  uint32_t ax35 = bx36 ^ (~bx46 & bx06);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax35);
  uint32_t ax45 = bx46 ^ (~bx06 & bx16);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax45);
  uint32_t a06 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t d07 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a17 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t d17 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____14 = {.fst = core_num__u32__rotate_left(a06 ^ d07, 18U),
                          .snd = core_num__u32__rotate_left(a17 ^ d17, 5U)};
  uint32_t bx17 = uu____14.fst;
  uint32_t bx27 = uu____14.snd;
  uint32_t a27 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t d27 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a37 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t d37 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a47 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t d47 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____15 = {.fst = core_num__u32__rotate_left(a27 ^ d27, 7U),
                          .snd = core_num__u32__rotate_left(a37 ^ d37, 28U),
                          .thd = core_num__u32__rotate_left(a47 ^ d47, 13U)};
  uint32_t bx37 = uu____15.fst;
  uint32_t bx47 = uu____15.snd;
  uint32_t bx07 = uu____15.thd;
  uint32_t ax07 = bx07 ^ (~bx17 & bx27);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax07);
  uint32_t ax16 = bx17 ^ (~bx27 & bx37);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax16);
  uint32_t ax26 = bx27 ^ (~bx37 & bx47);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax26);
  uint32_t ax36 = bx37 ^ (~bx47 & bx07);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax36);
  uint32_t ax46 = bx47 ^ (~bx07 & bx17);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax46);
  uint32_t a07 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t d08 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a18 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  uint32_t d18 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____16 = {.fst = core_num__u32__rotate_left(a07 ^ d08, 21U),
                          .snd = core_num__u32__rotate_left(a18 ^ d18, 1U)};
  uint32_t bx38 = uu____16.fst;
  uint32_t bx48 = uu____16.snd;
  uint32_t a28 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t d28 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a38 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t d38 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a48 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t d48 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____17 = {.fst = core_num__u32__rotate_left(a28 ^ d28, 31U),
                          .snd = core_num__u32__rotate_left(a38 ^ d38, 28U),
                          .thd = core_num__u32__rotate_left(a48 ^ d48, 20U)};
  uint32_t bx08 = uu____17.fst;
  uint32_t bx18 = uu____17.snd;
  uint32_t bx28 = uu____17.thd;
  uint32_t ax08 = bx08 ^ (~bx18 & bx28);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax08);
  uint32_t ax17 = bx18 ^ (~bx28 & bx38);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax17);
  uint32_t ax27 = bx28 ^ (~bx38 & bx48);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax27);
  uint32_t ax37 = bx38 ^ (~bx48 & bx08);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax37);
  uint32_t ax47 = bx48 ^ (~bx08 & bx18);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax47);
  uint32_t a08 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____18 = {.fst = core_num__u32__rotate_left(a08 ^ d0, 20U),
                          .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____18.fst;
  uint32_t bx4 = uu____18.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____19 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                          .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                          .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____19.fst;
  uint32_t bx1 = uu____19.snd;
  uint32_t bx2 = uu____19.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax18 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax18);
  uint32_t ax28 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax28);
  uint32_t ax38 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax38);
  uint32_t ax48 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax48);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_4rounds_bc(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_bc(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_bc(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_bc(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_bc(s);
}

KRML_NOINLINE void libcrux_iot_sha3_keccak_keccakf1600(
    libcrux_iot_sha3_state_KeccakState *s) {
  for (int32_t i = (int32_t)0; i < (int32_t)6; i++) {
    libcrux_iot_sha3_keccak_keccakf1600_4rounds_bc(s);
  }
  s->i = (size_t)0U;
}

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$4size_t]], core_array_TryFromSliceError

*/
typedef struct Result_44_s {
  Result_a4_tags tag;
  union {
    Eurydice_array_u8x4 case_Ok;
    TryFromSliceError case_Err;
  } val;
} Result_44;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$4size_t]], core_array_TryFromSliceError

*/
static Eurydice_array_u8x4 unwrap_26_84(Result_44 self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_5b(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_f8 state_flat;
  Eurydice_arr_b2 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_b2));
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_7e(
               blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_7e(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_08){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_b2 uu____0 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_47(
            (KRML_CLITERAL(Eurydice_arr_b2){.data = {a, b}})));
    state_flat.data[i0] = uu____0;
  }
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 got = libcrux_iot_sha3_state_get_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_b2){
            .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)0U)[0U],
                     libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)1U)[0U]}})));
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_5b(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_5b(
      state, Eurydice_array_to_slice_shared_f7(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_5b(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_5b(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_ad(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_88 blocks = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_36(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_7e(
                            last, (KRML_CLITERAL(core_ops_range_Range_08){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(31U);
  size_t uu____0 = (size_t)136U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_5b(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
 Absorb some data for SHAKE-256 for the last time
*/
void libcrux_iot_sha3_portable_incremental_shake256_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_state_KeccakState *uu____0 = s;
  Eurydice_borrow_slice_u8 uu____1 = data;
  libcrux_iot_sha3_keccak_absorb_final_ad(uu____0, uu____1, (size_t)0U,
                                          Eurydice_slice_len(data, uint8_t));
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_b2
libcrux_iot_sha3_lane_deinterleave_8d(Eurydice_arr_b2 self) {
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
  return (KRML_CLITERAL(Eurydice_arr_b2){
      .data = {even_spaced_lo | odd_spaced_lo << 1U,
               even_spaced_hi | odd_spaced_hi << 1U}});
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_3a(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_f8 state_flat;
  Eurydice_arr_b2 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_b2));
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_7e(
               blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_7e(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_08){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_b2 uu____0 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_47(
            (KRML_CLITERAL(Eurydice_arr_b2){.data = {a, b}})));
    state_flat.data[i0] = uu____0;
  }
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 got = libcrux_iot_sha3_state_get_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_b2){
            .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)0U)[0U],
                     libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)1U)[0U]}})));
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_3a(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_3a(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_3a(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_3a(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_3a(
      state, Eurydice_array_to_slice_shared_f7(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_3a(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_3a(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 168
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_c6(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_88 blocks = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_36(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_7e(
                            last, (KRML_CLITERAL(core_ops_range_Range_08){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(31U);
  size_t uu____0 = (size_t)168U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_3a(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_3a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_7e(
        out,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_60(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_7e(
        out, (KRML_CLITERAL(core_ops_range_Range_08){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_60(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_3a(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_2u32_3a(
      s, Eurydice_array_to_slice_mut_f7(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_3a(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_3a(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_3a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_3a(s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.lane.split_at_mut_1
with types uint8_t

*/
KRML_MUSTINLINE Eurydice_dst_ref_mut_uint8_t_size_t_x2
libcrux_iot_sha3_lane_split_at_mut_1_90(Eurydice_mut_borrow_slice_u8 out,
                                        size_t mid) {
  return Eurydice_slice_split_at_mut(out, mid, uint8_t,
                                     Eurydice_dst_ref_mut_uint8_t_size_t_x2);
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
/**
A monomorphic instance of libcrux_iot_sha3.lane.split_at_mut_n_8d
with types uint8_t

*/
KRML_MUSTINLINE Eurydice_dst_ref_mut_uint8_t_size_t_x2
libcrux_iot_sha3_lane_split_at_mut_n_8d_90(Eurydice_mut_borrow_slice_u8 a,
                                           size_t mid) {
  return libcrux_iot_sha3_lane_split_at_mut_1_90(a, mid);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_3a(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_3a(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_3a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_3a(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_3a(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_3a(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_3a(&s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 168
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_c6(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = Eurydice_slice_len(data, uint8_t) / (size_t)168U;
  size_t rem = Eurydice_slice_len(data, uint8_t) % (size_t)168U;
  size_t outlen = Eurydice_slice_len((KRML_CLITERAL(Eurydice_borrow_slice_u8){
                                         .ptr = out.ptr, .meta = out.meta}),
                                     uint8_t);
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  for (size_t i = (size_t)0U; i < n; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_keccak_absorb_block_3a(&s, data, i0 * (size_t)168U);
  }
  libcrux_iot_sha3_state_KeccakState *uu____0 = &s;
  Eurydice_borrow_slice_u8 uu____1 = data;
  libcrux_iot_sha3_keccak_absorb_final_c6(
      uu____0, uu____1, Eurydice_slice_len(data, uint8_t) - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_3a(&s, out);
  } else {
    Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____2 =
        libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, (size_t)168U);
    Eurydice_mut_borrow_slice_u8 o0 = uu____2.fst;
    Eurydice_mut_borrow_slice_u8 o1 = uu____2.snd;
    libcrux_iot_sha3_keccak_squeeze_first_block_3a(&s, o0);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____3 =
          libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o1, (size_t)168U);
      Eurydice_mut_borrow_slice_u8 o = uu____3.fst;
      Eurydice_mut_borrow_slice_u8 orest = uu____3.snd;
      libcrux_iot_sha3_keccak_squeeze_next_block_3a(&s, o);
      o1 = orest;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_3a(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_iot_sha3_portable_keccakx1_c6(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_c6(data, out);
}

/**
 A portable SHAKE128 implementation.
*/
void libcrux_iot_sha3_portable_shake128(Eurydice_mut_borrow_slice_u8 digest,
                                        Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_c6(data, digest);
}

/**
 Create a new SHAKE-128 state object.
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_portable_incremental_shake128_init(void) {
  return libcrux_iot_sha3_state_new_18();
}

/**
 Absorb
*/
void libcrux_iot_sha3_portable_incremental_shake128_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 data0) {
  libcrux_iot_sha3_state_KeccakState *uu____0 = s;
  Eurydice_borrow_slice_u8 uu____1 = data0;
  libcrux_iot_sha3_keccak_absorb_final_c6(uu____0, uu____1, (size_t)0U,
                                          Eurydice_slice_len(data0, uint8_t));
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_five_blocks
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_five_blocks_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____0 =
      libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, (size_t)168U);
  Eurydice_mut_borrow_slice_u8 o0 = uu____0.fst;
  Eurydice_mut_borrow_slice_u8 o10 = uu____0.snd;
  libcrux_iot_sha3_keccak_squeeze_first_block_3a(s, o0);
  Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____1 =
      libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o10, (size_t)168U);
  Eurydice_mut_borrow_slice_u8 o1 = uu____1.fst;
  Eurydice_mut_borrow_slice_u8 o20 = uu____1.snd;
  libcrux_iot_sha3_keccak_squeeze_next_block_3a(s, o1);
  Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____2 =
      libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o20, (size_t)168U);
  Eurydice_mut_borrow_slice_u8 o2 = uu____2.fst;
  Eurydice_mut_borrow_slice_u8 o30 = uu____2.snd;
  libcrux_iot_sha3_keccak_squeeze_next_block_3a(s, o2);
  Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____3 =
      libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o30, (size_t)168U);
  Eurydice_mut_borrow_slice_u8 o3 = uu____3.fst;
  Eurydice_mut_borrow_slice_u8 o4 = uu____3.snd;
  libcrux_iot_sha3_keccak_squeeze_next_block_3a(s, o3);
  libcrux_iot_sha3_keccak_squeeze_next_block_3a(s, o4);
}

/**
 Squeeze five blocks
*/
void libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0) {
  libcrux_iot_sha3_keccak_squeeze_first_five_blocks_3a(s, out0);
}

/**
 Squeeze another block
*/
void libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0) {
  libcrux_iot_sha3_keccak_squeeze_next_block_3a(s, out0);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_5b(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_5b(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_5b(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_5b(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_5b(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_7e(
        out,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_60(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_7e(
        out, (KRML_CLITERAL(core_ops_range_Range_08){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_60(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_5b(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_2u32_5b(
      s, Eurydice_array_to_slice_mut_f7(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_5b(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_5b(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_5b(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_5b(s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
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
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_5b(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_5b(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_5b(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_5b(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_5b(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_5b(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_5b(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_5b(&s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_ad(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = Eurydice_slice_len(data, uint8_t) / (size_t)136U;
  size_t rem = Eurydice_slice_len(data, uint8_t) % (size_t)136U;
  size_t outlen = Eurydice_slice_len((KRML_CLITERAL(Eurydice_borrow_slice_u8){
                                         .ptr = out.ptr, .meta = out.meta}),
                                     uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  for (size_t i = (size_t)0U; i < n; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_keccak_absorb_block_5b(&s, data, i0 * (size_t)136U);
  }
  libcrux_iot_sha3_state_KeccakState *uu____0 = &s;
  Eurydice_borrow_slice_u8 uu____1 = data;
  libcrux_iot_sha3_keccak_absorb_final_ad(
      uu____0, uu____1, Eurydice_slice_len(data, uint8_t) - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_5b(&s, out);
  } else {
    Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____2 =
        libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, (size_t)136U);
    Eurydice_mut_borrow_slice_u8 o0 = uu____2.fst;
    Eurydice_mut_borrow_slice_u8 o1 = uu____2.snd;
    libcrux_iot_sha3_keccak_squeeze_first_block_5b(&s, o0);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____3 =
          libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o1, (size_t)136U);
      Eurydice_mut_borrow_slice_u8 o = uu____3.fst;
      Eurydice_mut_borrow_slice_u8 orest = uu____3.snd;
      libcrux_iot_sha3_keccak_squeeze_next_block_5b(&s, o);
      o1 = orest;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_5b(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_iot_sha3_portable_keccakx1_ad(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_ad(data, out);
}

/**
 A portable SHAKE256 implementation.
*/
void libcrux_iot_sha3_portable_shake256(Eurydice_mut_borrow_slice_u8 digest,
                                        Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_ad(data, digest);
}

/**
 Squeeze the first SHAKE-256 block
*/
void libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_squeeze_first_block_5b(s, out);
}

/**
 Squeeze the next SHAKE-256 block
*/
void libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_squeeze_next_block_5b(s, out);
}

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.fill_buffer_f0
with const generics
- RATE= 136
*/
size_t libcrux_iot_sha3_keccak_fill_buffer_f0_5b(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_len = Eurydice_slice_len(inputs, uint8_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (self->buf_len + input_len >= (size_t)136U) {
      consumed = (size_t)136U - self->buf_len;
      Eurydice_slice_copy(
          Eurydice_array_to_subslice_from_mut_8c(&self->buf, self->buf_len),
          Eurydice_slice_subslice_to_shared_c6(inputs, consumed), uint8_t);
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_full_f0
with const generics
- RATE= 136
*/
size_t libcrux_iot_sha3_keccak_absorb_full_f0_5b(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_consumed =
      libcrux_iot_sha3_keccak_fill_buffer_f0_5b(self, inputs);
  if (input_consumed > (size_t)0U) {
    libcrux_iot_sha3_state_load_block_18_5b(
        &self->inner, Eurydice_array_to_slice_shared_d4(&self->buf),
        (size_t)0U);
    libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      Eurydice_slice_len(inputs, uint8_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)136U;
  size_t remainder = input_to_consume % (size_t)136U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_state_load_block_18_5b(&self->inner, inputs,
                                            input_consumed + i0 * (size_t)136U);
    libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
  }
  return remainder;
}

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_f0
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_f0_5b(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_remainder_len =
      libcrux_iot_sha3_keccak_absorb_full_f0_5b(self, inputs);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = Eurydice_slice_len(inputs, uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice_mut_360(
            &self->buf, (KRML_CLITERAL(core_ops_range_Range_08){
                            .start = self->buf_len,
                            .end = self->buf_len + input_remainder_len})),
        Eurydice_slice_subslice_from_shared_6b(inputs,
                                               input_len - input_remainder_len),
        uint8_t);
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

/**
 Shake256 absorb
*/
/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<136usize> for
libcrux_iot_sha3::portable::incremental::Shake256Xof}
*/
void libcrux_iot_sha3_portable_incremental_absorb_a5(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_keccak_absorb_f0_5b(self, input);
}

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final_f0
with const generics
- RATE= 136
- DELIMITER= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_f0_ad(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_remainder_len =
      libcrux_iot_sha3_keccak_absorb_full_f0_5b(self, inputs);
  size_t input_len = Eurydice_slice_len(inputs, uint8_t);
  Eurydice_arr_88 blocks = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  if (self->buf_len > (size_t)0U) {
    Eurydice_slice_copy(
        Eurydice_array_to_subslice_mut_36(
            &blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)0U, .end = self->buf_len})),
        Eurydice_array_to_subslice_shared_360(
            &self->buf, (KRML_CLITERAL(core_ops_range_Range_08){
                            .start = (size_t)0U, .end = self->buf_len})),
        uint8_t);
  }
  if (input_remainder_len > (size_t)0U) {
    Eurydice_slice_copy(
        Eurydice_array_to_subslice_mut_36(
            &blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = self->buf_len,
                         .end = self->buf_len + input_remainder_len})),
        Eurydice_slice_subslice_from_shared_6b(inputs,
                                               input_len - input_remainder_len),
        uint8_t);
  }
  blocks.data[self->buf_len + input_remainder_len] =
      libcrux_secrets_int_public_integers_classify_27_90(31U);
  size_t uu____0 = (size_t)136U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_5b(&self->inner, &blocks,
                                               (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
}

/**
 Shake256 absorb final
*/
/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<136usize> for
libcrux_iot_sha3::portable::incremental::Shake256Xof}
*/
void libcrux_iot_sha3_portable_incremental_absorb_final_a5(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_keccak_absorb_final_f0_ad(self, input);
}

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.zero_block_f0
with const generics
- RATE= 136
*/
Eurydice_arr_3d libcrux_iot_sha3_keccak_zero_block_f0_5b(void) {
  return libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_3d){.data = {0U}}));
}

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.new_f0
with const generics
- RATE= 136
*/
libcrux_iot_sha3_keccak_KeccakXofState_c7 libcrux_iot_sha3_keccak_new_f0_5b(
    void) {
  libcrux_iot_sha3_state_KeccakState uu____0 = libcrux_iot_sha3_state_new_18();
  return (KRML_CLITERAL(libcrux_iot_sha3_keccak_KeccakXofState_c7){
      .inner = uu____0,
      .buf = libcrux_iot_sha3_keccak_zero_block_f0_5b(),
      .buf_len = (size_t)0U,
      .sponge = false});
}

/**
 Shake256 new state
*/
/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<136usize> for
libcrux_iot_sha3::portable::incremental::Shake256Xof}
*/
libcrux_iot_sha3_keccak_KeccakXofState_c7
libcrux_iot_sha3_portable_incremental_new_a5(void) {
  return libcrux_iot_sha3_keccak_new_f0_5b();
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_18_5b(
    libcrux_iot_sha3_state_KeccakState self, Eurydice_mut_borrow_slice_u8 out) {
  size_t num_full_blocks =
      Eurydice_slice_len((KRML_CLITERAL(Eurydice_borrow_slice_u8){
                             .ptr = out.ptr, .meta = out.meta}),
                         uint8_t) /
      (size_t)8U;
  size_t last_block_len =
      Eurydice_slice_len((KRML_CLITERAL(Eurydice_borrow_slice_u8){
                             .ptr = out.ptr, .meta = out.meta}),
                         uint8_t) %
      (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(&self, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_7e(
        out,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_60(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_7e(
        out, (KRML_CLITERAL(core_ops_range_Range_08){
                 .start = i0 * (size_t)8U + (size_t)4U,
                 .end = i0 * (size_t)8U + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_60(&lvalue),
                        uint8_t);
  }
  if (last_block_len > (size_t)4U) {
    Eurydice_arr_b2 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(&self, num_full_blocks / (size_t)5U,
                                           num_full_blocks % (size_t)5U));
    size_t last_half_block_len = last_block_len - (size_t)4U;
    Eurydice_mut_borrow_slice_u8 uu____2 = Eurydice_slice_subslice_mut_7e(
        out, (KRML_CLITERAL(core_ops_range_Range_08){
                 .start = num_full_blocks * (size_t)8U,
                 .end = num_full_blocks * (size_t)8U + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____2, Eurydice_array_to_slice_shared_60(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____3 = Eurydice_slice_subslice_mut_7e(
        out, (KRML_CLITERAL(core_ops_range_Range_08){
                 .start = num_full_blocks * (size_t)8U + (size_t)4U,
                 .end = num_full_blocks * (size_t)8U + last_block_len}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(
        uu____3,
        Eurydice_array_to_subslice_shared_361(
            &lvalue, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)0U, .end = last_half_block_len})),
        uint8_t);
  } else if (last_block_len > (size_t)0U) {
    Eurydice_arr_b2 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(&self, num_full_blocks / (size_t)5U,
                                           num_full_blocks % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____4 = Eurydice_slice_subslice_mut_7e(
        out, (KRML_CLITERAL(core_ops_range_Range_08){
                 .start = num_full_blocks * (size_t)8U,
                 .end = num_full_blocks * (size_t)8U + last_block_len}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(
        uu____4,
        Eurydice_array_to_subslice_shared_361(
            &lvalue, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)0U, .end = last_block_len})),
        uint8_t);
  }
}

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_f0
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_f0_5b(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_mut_borrow_slice_u8 out) {
  if (self->sponge) {
    libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
  }
  size_t out_len = Eurydice_slice_len((KRML_CLITERAL(Eurydice_borrow_slice_u8){
                                          .ptr = out.ptr, .meta = out.meta}),
                                      uint8_t);
  size_t blocks = out_len / (size_t)136U;
  size_t last = out_len - out_len % (size_t)136U;
  size_t mid;
  if ((size_t)136U >= out_len) {
    mid = out_len;
  } else {
    mid = (size_t)136U;
  }
  Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____0 =
      libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, mid);
  Eurydice_mut_borrow_slice_u8 out00 = uu____0.fst;
  Eurydice_mut_borrow_slice_u8 out_rest = uu____0.snd;
  libcrux_iot_sha3_state_store_18_5b(self->inner, out00);
  for (size_t i = (size_t)1U; i < blocks; i++) {
    Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____1 =
        libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out_rest, (size_t)136U);
    Eurydice_mut_borrow_slice_u8 out0 = uu____1.fst;
    Eurydice_mut_borrow_slice_u8 tmp = uu____1.snd;
    libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
    libcrux_iot_sha3_state_store_18_5b(self->inner, out0);
    out_rest = tmp;
  }
  if (last < out_len) {
    libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
    libcrux_iot_sha3_state_store_18_5b(self->inner, out_rest);
  }
  self->sponge = true;
}

/**
 Shake256 squeeze
*/
/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<136usize> for
libcrux_iot_sha3::portable::incremental::Shake256Xof}
*/
void libcrux_iot_sha3_portable_incremental_squeeze_a5(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_squeeze_f0_5b(self, out);
}

/**
 Returns the output size of a digest.
*/
size_t libcrux_iot_sha3_digest_size(libcrux_iot_sha3_Algorithm mode) {
  switch (mode) {
    case libcrux_iot_sha3_Algorithm_Sha224: {
      break;
    }
    case libcrux_iot_sha3_Algorithm_Sha256: {
      return LIBCRUX_IOT_SHA3_SHA3_256_DIGEST_SIZE;
    }
    case libcrux_iot_sha3_Algorithm_Sha384: {
      return LIBCRUX_IOT_SHA3_SHA3_384_DIGEST_SIZE;
    }
    case libcrux_iot_sha3_Algorithm_Sha512: {
      return LIBCRUX_IOT_SHA3_SHA3_512_DIGEST_SIZE;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return LIBCRUX_IOT_SHA3_SHA3_224_DIGEST_SIZE;
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_2c(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_f8 state_flat;
  Eurydice_arr_b2 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_b2));
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_7e(
               blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_7e(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_08){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_b2 uu____0 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_47(
            (KRML_CLITERAL(Eurydice_arr_b2){.data = {a, b}})));
    state_flat.data[i0] = uu____0;
  }
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 got = libcrux_iot_sha3_state_get_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_b2){
            .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)0U)[0U],
                     libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)1U)[0U]}})));
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_2c(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_2c(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_2c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_2c(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_2c(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_2c(
      state, Eurydice_array_to_slice_shared_f7(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_2c(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_2c(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 144
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_1e(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_88 blocks = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_36(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_7e(
                            last, (KRML_CLITERAL(core_ops_range_Range_08){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)144U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_2c(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_2c(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_7e(
        out,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_60(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_7e(
        out, (KRML_CLITERAL(core_ops_range_Range_08){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_60(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_2c(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_2u32_2c(
      s, Eurydice_array_to_slice_mut_f7(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_2c(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_2c(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_2c(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_2c(s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
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
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_2c(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_2c(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_2c(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_2c(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_2c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_2c(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_2c(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_2c(&s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 144
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_1e(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = Eurydice_slice_len(data, uint8_t) / (size_t)144U;
  size_t rem = Eurydice_slice_len(data, uint8_t) % (size_t)144U;
  size_t outlen = Eurydice_slice_len((KRML_CLITERAL(Eurydice_borrow_slice_u8){
                                         .ptr = out.ptr, .meta = out.meta}),
                                     uint8_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  for (size_t i = (size_t)0U; i < n; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_keccak_absorb_block_2c(&s, data, i0 * (size_t)144U);
  }
  libcrux_iot_sha3_state_KeccakState *uu____0 = &s;
  Eurydice_borrow_slice_u8 uu____1 = data;
  libcrux_iot_sha3_keccak_absorb_final_1e(
      uu____0, uu____1, Eurydice_slice_len(data, uint8_t) - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_2c(&s, out);
  } else {
    Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____2 =
        libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, (size_t)144U);
    Eurydice_mut_borrow_slice_u8 o0 = uu____2.fst;
    Eurydice_mut_borrow_slice_u8 o1 = uu____2.snd;
    libcrux_iot_sha3_keccak_squeeze_first_block_2c(&s, o0);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____3 =
          libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o1, (size_t)144U);
      Eurydice_mut_borrow_slice_u8 o = uu____3.fst;
      Eurydice_mut_borrow_slice_u8 orest = uu____3.snd;
      libcrux_iot_sha3_keccak_squeeze_next_block_2c(&s, o);
      o1 = orest;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_2c(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_1e(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_1e(data, out);
}

/**
 A portable SHA3 224 implementation.
*/
void libcrux_iot_sha3_portable_sha224(Eurydice_mut_borrow_slice_u8 digest,
                                      Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_1e(data, digest);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_ad0(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_88 blocks = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_36(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_7e(
                            last, (KRML_CLITERAL(core_ops_range_Range_08){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)136U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_5b(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_ad0(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = Eurydice_slice_len(data, uint8_t) / (size_t)136U;
  size_t rem = Eurydice_slice_len(data, uint8_t) % (size_t)136U;
  size_t outlen = Eurydice_slice_len((KRML_CLITERAL(Eurydice_borrow_slice_u8){
                                         .ptr = out.ptr, .meta = out.meta}),
                                     uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  for (size_t i = (size_t)0U; i < n; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_keccak_absorb_block_5b(&s, data, i0 * (size_t)136U);
  }
  libcrux_iot_sha3_state_KeccakState *uu____0 = &s;
  Eurydice_borrow_slice_u8 uu____1 = data;
  libcrux_iot_sha3_keccak_absorb_final_ad0(
      uu____0, uu____1, Eurydice_slice_len(data, uint8_t) - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_5b(&s, out);
  } else {
    Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____2 =
        libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, (size_t)136U);
    Eurydice_mut_borrow_slice_u8 o0 = uu____2.fst;
    Eurydice_mut_borrow_slice_u8 o1 = uu____2.snd;
    libcrux_iot_sha3_keccak_squeeze_first_block_5b(&s, o0);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____3 =
          libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o1, (size_t)136U);
      Eurydice_mut_borrow_slice_u8 o = uu____3.fst;
      Eurydice_mut_borrow_slice_u8 orest = uu____3.snd;
      libcrux_iot_sha3_keccak_squeeze_next_block_5b(&s, o);
      o1 = orest;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_5b(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_ad0(Eurydice_borrow_slice_u8 data,
                                            Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_ad0(data, out);
}

/**
 A portable SHA3 256 implementation.
*/
void libcrux_iot_sha3_portable_sha256(Eurydice_mut_borrow_slice_u8 digest,
                                      Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_ad0(data, digest);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_7a(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_f8 state_flat;
  Eurydice_arr_b2 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_b2));
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_7e(
               blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_7e(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_08){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_b2 uu____0 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_47(
            (KRML_CLITERAL(Eurydice_arr_b2){.data = {a, b}})));
    state_flat.data[i0] = uu____0;
  }
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 got = libcrux_iot_sha3_state_get_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_b2){
            .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)0U)[0U],
                     libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)1U)[0U]}})));
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_7a(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_7a(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_7a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_7a(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_7a(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_7a(
      state, Eurydice_array_to_slice_shared_f7(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_7a(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_7a(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 104
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_7c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_88 blocks = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_36(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_7e(
                            last, (KRML_CLITERAL(core_ops_range_Range_08){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)104U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_7a(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_7a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_7e(
        out,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_60(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_7e(
        out, (KRML_CLITERAL(core_ops_range_Range_08){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_60(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_7a(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_2u32_7a(
      s, Eurydice_array_to_slice_mut_f7(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_7a(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_7a(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_7a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_7a(s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
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
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_7a(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_7a(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_7a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_7a(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_7a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_7a(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_7a(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_7a(&s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 104
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_7c(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = Eurydice_slice_len(data, uint8_t) / (size_t)104U;
  size_t rem = Eurydice_slice_len(data, uint8_t) % (size_t)104U;
  size_t outlen = Eurydice_slice_len((KRML_CLITERAL(Eurydice_borrow_slice_u8){
                                         .ptr = out.ptr, .meta = out.meta}),
                                     uint8_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  for (size_t i = (size_t)0U; i < n; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_keccak_absorb_block_7a(&s, data, i0 * (size_t)104U);
  }
  libcrux_iot_sha3_state_KeccakState *uu____0 = &s;
  Eurydice_borrow_slice_u8 uu____1 = data;
  libcrux_iot_sha3_keccak_absorb_final_7c(
      uu____0, uu____1, Eurydice_slice_len(data, uint8_t) - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_7a(&s, out);
  } else {
    Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____2 =
        libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, (size_t)104U);
    Eurydice_mut_borrow_slice_u8 o0 = uu____2.fst;
    Eurydice_mut_borrow_slice_u8 o1 = uu____2.snd;
    libcrux_iot_sha3_keccak_squeeze_first_block_7a(&s, o0);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____3 =
          libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o1, (size_t)104U);
      Eurydice_mut_borrow_slice_u8 o = uu____3.fst;
      Eurydice_mut_borrow_slice_u8 orest = uu____3.snd;
      libcrux_iot_sha3_keccak_squeeze_next_block_7a(&s, o);
      o1 = orest;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_7a(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_7c(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_7c(data, out);
}

/**
 A portable SHA3 384 implementation.
*/
void libcrux_iot_sha3_portable_sha384(Eurydice_mut_borrow_slice_u8 digest,
                                      Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_7c(data, digest);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_f8(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  Eurydice_arr_f8 state_flat;
  Eurydice_arr_b2 repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(state_flat.data, repeat_expression,
         (size_t)25U * sizeof(Eurydice_arr_b2));
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_7e(
               blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_7e(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_08){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(unwrap_26_84(
        (KRML_CLITERAL(Result_44){.tag = Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_b2 uu____0 =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_47(
            (KRML_CLITERAL(Eurydice_arr_b2){.data = {a, b}})));
    state_flat.data[i0] = uu____0;
  }
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 got = libcrux_iot_sha3_state_get_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_b2){
            .data = {libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)0U)[0U],
                     libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                         libcrux_iot_sha3_lane_index_cc(&state_flat.data[i0],
                                                        (size_t)1U)[0U]}})));
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_f8(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_f8(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_f8(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_f8(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_f8(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_f8(
      state, Eurydice_array_to_slice_shared_f7(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_f8(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_f8(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 72
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_96(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_88 blocks = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_36(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_08){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_7e(
                            last, (KRML_CLITERAL(core_ops_range_Range_08){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)72U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_f8(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_f8(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_b2 lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_7e(
        out,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_60(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_7e(
        out, (KRML_CLITERAL(core_ops_range_Range_08){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_60(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_f8(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_2u32_f8(
      s, Eurydice_array_to_slice_mut_f7(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_f8(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_f8(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_f8(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_f8(s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
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
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_f8(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_f8(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_f8(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_f8(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_f8(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_f8(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_f8(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_88 b = libcrux_secrets_int_public_integers_classify_27_c1(
      (KRML_CLITERAL(Eurydice_arr_88){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_f8(&s, &b);
  Eurydice_mut_borrow_slice_u8 uu____0 = out;
  const Eurydice_arr_88 *uu____1 = &b;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice_shared_36(
          uu____1, (KRML_CLITERAL(core_ops_range_Range_08){
                       .start = (size_t)0U,
                       .end = Eurydice_slice_len(
                           (KRML_CLITERAL(Eurydice_borrow_slice_u8){
                               .ptr = out.ptr, .meta = out.meta}),
                           uint8_t)})),
      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 72
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_96(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = Eurydice_slice_len(data, uint8_t) / (size_t)72U;
  size_t rem = Eurydice_slice_len(data, uint8_t) % (size_t)72U;
  size_t outlen = Eurydice_slice_len((KRML_CLITERAL(Eurydice_borrow_slice_u8){
                                         .ptr = out.ptr, .meta = out.meta}),
                                     uint8_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  for (size_t i = (size_t)0U; i < n; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_keccak_absorb_block_f8(&s, data, i0 * (size_t)72U);
  }
  libcrux_iot_sha3_state_KeccakState *uu____0 = &s;
  Eurydice_borrow_slice_u8 uu____1 = data;
  libcrux_iot_sha3_keccak_absorb_final_96(
      uu____0, uu____1, Eurydice_slice_len(data, uint8_t) - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_f8(&s, out);
  } else {
    Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____2 =
        libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, (size_t)72U);
    Eurydice_mut_borrow_slice_u8 o0 = uu____2.fst;
    Eurydice_mut_borrow_slice_u8 o1 = uu____2.snd;
    libcrux_iot_sha3_keccak_squeeze_first_block_f8(&s, o0);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____3 =
          libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o1, (size_t)72U);
      Eurydice_mut_borrow_slice_u8 o = uu____3.fst;
      Eurydice_mut_borrow_slice_u8 orest = uu____3.snd;
      libcrux_iot_sha3_keccak_squeeze_next_block_f8(&s, o);
      o1 = orest;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_f8(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_96(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_96(data, out);
}

/**
 A portable SHA3 512 implementation.
*/
void libcrux_iot_sha3_portable_sha512(Eurydice_mut_borrow_slice_u8 digest,
                                      Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_96(data, digest);
}

/**
 SHA3 224

 Preconditions:
 - `digest.len() == 28`
*/
void libcrux_iot_sha3_sha224_ema(Eurydice_mut_borrow_slice_u8 digest,
                                 Eurydice_borrow_slice_u8 payload) {
  libcrux_iot_sha3_portable_keccakx1_1e(payload, digest);
}

/**
 SHA3 224
*/
Eurydice_arr_f1 libcrux_iot_sha3_sha224(Eurydice_borrow_slice_u8 data) {
  Eurydice_arr_f1 out = libcrux_secrets_int_public_integers_classify_27_4b(
      (KRML_CLITERAL(Eurydice_arr_f1){.data = {0U}}));
  libcrux_iot_sha3_sha224_ema(Eurydice_array_to_slice_mut_c0(&out), data);
  return out;
}

/**
 SHA3 256
*/
void libcrux_iot_sha3_sha256_ema(Eurydice_mut_borrow_slice_u8 digest,
                                 Eurydice_borrow_slice_u8 payload) {
  libcrux_iot_sha3_portable_keccakx1_ad0(payload, digest);
}

/**
 SHA3 256
*/
Eurydice_arr_60 libcrux_iot_sha3_sha256(Eurydice_borrow_slice_u8 data) {
  Eurydice_arr_60 out = libcrux_secrets_int_public_integers_classify_27_62(
      (KRML_CLITERAL(Eurydice_arr_60){.data = {0U}}));
  libcrux_iot_sha3_sha256_ema(Eurydice_array_to_slice_mut_6e(&out), data);
  return out;
}

/**
 SHA3 384
*/
void libcrux_iot_sha3_sha384_ema(Eurydice_mut_borrow_slice_u8 digest,
                                 Eurydice_borrow_slice_u8 payload) {
  libcrux_iot_sha3_portable_keccakx1_7c(payload, digest);
}

/**
 SHA3 384
*/
Eurydice_arr_5f libcrux_iot_sha3_sha384(Eurydice_borrow_slice_u8 data) {
  Eurydice_arr_5f out = libcrux_secrets_int_public_integers_classify_27_7d(
      (KRML_CLITERAL(Eurydice_arr_5f){.data = {0U}}));
  libcrux_iot_sha3_sha384_ema(Eurydice_array_to_slice_mut_95(&out), data);
  return out;
}

/**
 SHA3 512
*/
void libcrux_iot_sha3_sha512_ema(Eurydice_mut_borrow_slice_u8 digest,
                                 Eurydice_borrow_slice_u8 payload) {
  libcrux_iot_sha3_portable_keccakx1_96(payload, digest);
}

/**
 SHA3 512
*/
Eurydice_arr_06 libcrux_iot_sha3_sha512(Eurydice_borrow_slice_u8 data) {
  Eurydice_arr_06 out = libcrux_secrets_int_public_integers_classify_27_490(
      (KRML_CLITERAL(Eurydice_arr_06){.data = {0U}}));
  libcrux_iot_sha3_sha512_ema(Eurydice_array_to_slice_mut_d8(&out), data);
  return out;
}

/**
 SHAKE 128

 Writes `out.len()` bytes.
*/
void libcrux_iot_sha3_shake128_ema(Eurydice_mut_borrow_slice_u8 out,
                                   Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_c6(data, out);
}

/**
 SHAKE 256

 Writes `out.len()` bytes.
*/
void libcrux_iot_sha3_shake256_ema(Eurydice_mut_borrow_slice_u8 out,
                                   Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_ad(data, out);
}

/**
 Perform four rounds of the keccak permutation functions
*/
void libcrux_iot_sha3_portable_incremental_keccakf1660_4rounds(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_4rounds_bc(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_three_blocks
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_three_blocks_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____0 =
      libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, (size_t)168U);
  Eurydice_mut_borrow_slice_u8 o0 = uu____0.fst;
  Eurydice_mut_borrow_slice_u8 o10 = uu____0.snd;
  libcrux_iot_sha3_keccak_squeeze_first_block_3a(s, o0);
  Eurydice_dst_ref_mut_uint8_t_size_t_x2 uu____1 =
      libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o10, (size_t)168U);
  Eurydice_mut_borrow_slice_u8 o1 = uu____1.fst;
  Eurydice_mut_borrow_slice_u8 o2 = uu____1.snd;
  libcrux_iot_sha3_keccak_squeeze_next_block_3a(s, o1);
  libcrux_iot_sha3_keccak_squeeze_next_block_3a(s, o2);
}

/**
 Squeeze three blocks
*/
void libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0) {
  libcrux_iot_sha3_keccak_squeeze_first_three_blocks_3a(s, out0);
}
