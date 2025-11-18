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
 * Libcrux: ef9b31aaac0a2120341b8ac2739f1e1613fe5b7a
 */

#ifndef internal_libcrux_iot_sha3_H
#define internal_libcrux_iot_sha3_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_iot_sha3.h"
#include "internal/libcrux_iot_core.h"
#include "libcrux_iot_core.h"

typedef Eurydice_arr_b2 libcrux_iot_sha3_lane_Lane2U32;

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_b2 libcrux_iot_sha3_lane_from_ints_8d(Eurydice_arr_b2 value);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_b2 libcrux_iot_sha3_lane_zero_8d(void);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
libcrux_iot_sha3_state_KeccakState libcrux_iot_sha3_state_new_18(void);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
Eurydice_arr_b2 libcrux_iot_sha3_state_get_lane_18(
    const libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j);

/**
This function found in impl {core::ops::index::Index<usize, u32> for
libcrux_iot_sha3::lane::Lane2U32}
*/
const uint32_t *libcrux_iot_sha3_lane_index_cc(const Eurydice_arr_b2 *self,
                                               size_t index);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
void libcrux_iot_sha3_state_set_lane_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    Eurydice_arr_b2 lane);

/**
This function found in impl {core::convert::From<@Array<u32, 2usize>> for
libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_b2 libcrux_iot_sha3_lane_from_47(Eurydice_arr_b2 value);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_b2 libcrux_iot_sha3_lane_interleave_8d(Eurydice_arr_b2 self);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
uint32_t libcrux_iot_sha3_state_get_with_zeta_18(
    const libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    size_t zeta);

/**
This function found in impl {core::ops::index::IndexMut<usize, u32> for
libcrux_iot_sha3::lane::Lane2U32}
*/
uint32_t *libcrux_iot_sha3_lane_index_mut_c5(Eurydice_arr_b2 *self,
                                             size_t index);

#define LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0                               \
  ((KRML_CLITERAL(Eurydice_arr_000){                                           \
      .data = {1U, 0U, 0U, 0U, 1U, 1U, 1U, 1U, 0U, 0U, 1U, 0U, 1U, 1U, 1U, 1U, \
               0U, 0U, 0U, 0U, 1U, 0U, 1U, 0U, 0U, 0U, 1U, 1U, 0U, 1U, 0U, 1U, \
               1U, 1U, 1U, 1U, 0U, 0U, 1U, 1U, 1U, 1U, 0U, 1U, 1U, 0U, 0U, 1U, \
               0U, 1U, 0U, 1U, 1U, 1U, 0U, 1U, 0U, 1U, 1U, 0U, 1U, 1U, 1U, 0U, \
               0U, 1U, 1U, 0U, 1U, 0U, 0U, 1U, 1U, 0U, 1U, 1U, 0U, 1U, 0U, 0U, \
               0U, 1U, 0U, 0U, 1U, 1U, 1U, 0U, 1U, 1U, 0U, 1U, 1U, 0U, 0U, 0U, \
               0U, 1U, 1U, 1U, 0U, 1U, 0U, 0U, 1U, 0U, 0U, 1U, 0U, 0U, 0U, 0U, \
               0U, 1U, 0U, 1U, 1U, 0U, 0U, 0U, 1U, 1U, 1U, 0U, 0U, 0U, 0U, 0U, \
               0U, 1U, 1U, 0U, 1U, 1U, 1U, 1U, 0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, \
               0U, 1U, 0U, 0U, 1U, 0U, 1U, 0U, 0U, 1U, 1U, 1U, 1U, 1U, 1U, 1U, \
               1U, 0U, 0U, 0U, 1U, 1U, 0U, 0U, 0U, 1U, 0U, 1U, 0U, 1U, 0U, 1U, \
               0U, 0U, 0U, 0U, 1U, 0U, 0U, 0U, 0U, 1U, 1U, 0U, 0U, 1U, 1U, 0U, \
               0U, 0U, 0U, 0U, 1U, 1U, 1U, 1U, 1U, 0U, 1U, 1U, 1U, 0U, 1U, 1U, \
               1U, 1U, 1U, 1U, 0U, 1U, 0U, 1U, 0U, 0U, 1U, 0U, 1U, 1U, 0U, 1U, \
               0U, 1U, 0U, 1U, 1U, 0U, 0U, 1U, 1U, 1U, 0U, 0U, 1U, 0U, 0U, 1U, \
               1U, 0U, 0U, 1U, 0U, 0U, 0U, 1U, 0U, 1U, 1U, 1U}}))

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
void libcrux_iot_sha3_state_set_with_zeta_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j, size_t zeta,
    uint32_t v);

#define LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1                           \
  ((KRML_CLITERAL(Eurydice_arr_000){                                       \
      .data = {                                                            \
          0U,          137U,        2147483787U, 2147516544U, 139U,        \
          32768U,      2147516552U, 2147483778U, 11U,         10U,         \
          32898U,      32771U,      32907U,      2147483659U, 2147483786U, \
          2147483777U, 2147483777U, 2147483656U, 131U,        2147516419U, \
          2147516552U, 2147483784U, 32768U,      2147516546U, 2147516553U, \
          2147516547U, 2147483649U, 2147516418U, 2147483785U, 130U,        \
          2147483656U, 137U,        2147483656U, 0U,          131U,        \
          2147516544U, 8U,          2147483776U, 2147516544U, 2U,          \
          2147516555U, 8U,          2147483657U, 32779U,      2147516546U, \
          2147516416U, 32776U,      32897U,      2147516553U, 2147516553U, \
          2147516426U, 138U,        130U,        2147483650U, 32898U,      \
          32896U,      2147483659U, 2147483651U, 10U,         32769U,      \
          2147483779U, 32899U,      139U,        32778U,      2147483779U, \
          32778U,      2147483648U, 2147483786U, 2147483656U, 10U,         \
          32904U,      8U,          2147483651U, 0U,          10U,         \
          32779U,      2147516552U, 2147483659U, 2147483776U, 2147516554U, \
          32777U,      3U,          2147483651U, 137U,        2147483777U, \
          2147483787U, 2147516419U, 2147516427U, 32776U,      32776U,      \
          32770U,      9U,          2147516545U, 32906U,      2147516426U, \
          128U,        32905U,      32906U,      2147516553U, 2147516416U, \
          32897U,      2147516426U, 9U,          2147516418U, 2147483658U, \
          2147516418U, 2147483648U, 2147483657U, 32904U,      2U,          \
          2147516424U, 2147516552U, 2147483649U, 2147516555U, 2U,          \
          2147516418U, 2147483779U, 32905U,      32896U,      2147483778U, \
          136U,        2147516554U, 32906U,      2147516547U, 2147483659U, \
          2147483657U, 32769U,      2147483785U, 136U,        2147516419U, \
          2147516417U, 3U,          2147483776U, 2147516425U, 2147483785U, \
          11U,         131U,        2147516425U, 2147483779U, 32768U,      \
          2147516427U, 32770U,      3U,          2147483786U, 2147483650U, \
          32769U,      2147483648U, 2147483651U, 131U,        2147516554U, \
          32771U,      32776U,      32907U,      2147483778U, 1U,          \
          32769U,      2147483658U, 2147516424U, 2147516427U, 32897U,      \
          2147516547U, 2147483778U, 130U,        2147483777U, 2147483650U, \
          32904U,      139U,        32899U,      8U,          2147483786U, \
          2147483787U, 2147516554U, 32896U,      2147483784U, 32899U,      \
          2U,          2147516545U, 32771U,      32897U,      2147516416U, \
          32770U,      138U,        1U,          32898U,      32906U,      \
          2147516416U, 32907U,      2147483649U, 2147516545U, 32777U,      \
          138U,        136U,        2147516425U, 2147483658U, 2147516555U, \
          139U,        32905U,      32771U,      32770U,      128U,        \
          32778U,      2147483658U, 2147516545U, 32896U,      2147483649U, \
          2147516424U, 2147516546U, 2147516426U, 3U,          2147483657U, \
          32898U,      32777U,      128U,        32899U,      129U,        \
          1U,          32779U,      2147516417U, 128U,        32768U,      \
          2147516417U, 9U,          2147516555U, 129U,        130U,        \
          2147483787U, 2147516425U, 2147483648U, 2147483776U, 2147516419U, \
          2147516546U, 2147516547U, 2147483784U, 32905U,      32777U,      \
          9U,          2147516424U, 2147516417U, 138U,        11U,         \
          137U,        2147483650U, 32779U,      2147516427U, 32907U,      \
          2147483784U, 32778U,      2147483785U, 1U,          32904U,      \
          129U,        136U,        2147516544U, 129U,        11U}}))

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round0
with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_bc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round1
with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_bc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round2
with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_bc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round3
with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_bc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_bc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round0
with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_ac(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round1
with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_ac(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round2
with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_ac(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round3
with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_ac(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_ac(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round0
with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_3b(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round1
with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_3b(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round2
with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_3b(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round3
with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_3b(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_3b(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round0
with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_78(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round1
with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_78(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round2
with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_78(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round3
with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_78(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_78(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round0
with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_f1(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round1
with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_f1(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round2
with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_f1(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round3
with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_f1(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_f1(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round0
with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round1
with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round2
with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_round3
with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_70(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600(libcrux_iot_sha3_state_KeccakState *s);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_b2 libcrux_iot_sha3_lane_deinterleave_8d(Eurydice_arr_b2 self);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_2u32_f8(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_18_f8(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_absorb_block_f8(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_full_2u32_f8(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_full_18_f8(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_96(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_2u32_f8(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_full_2u32_f8(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_full_18_f8(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_f8(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.lane.split_at_mut_1
with types uint8_t

*/
Eurydice_dst_ref_mut_uint8_t_size_t_x2 libcrux_iot_sha3_lane_split_at_mut_1_90(
    Eurydice_mut_borrow_slice_u8 out, size_t mid);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
/**
A monomorphic instance of libcrux_iot_sha3.lane.split_at_mut_n_8d
with types uint8_t

*/
Eurydice_dst_ref_mut_uint8_t_size_t_x2
libcrux_iot_sha3_lane_split_at_mut_n_8d_90(Eurydice_mut_borrow_slice_u8 a,
                                           size_t mid);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_18_f8(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_f8(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_f8(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_last_f8(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_96(Eurydice_borrow_slice_u8 data,
                                       Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_96(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out);

/**
 A portable SHA3 512 implementation.
*/
void libcrux_iot_sha3_portable_sha512(Eurydice_mut_borrow_slice_u8 digest,
                                      Eurydice_borrow_slice_u8 data);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_2u32_5b(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_18_5b(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_absorb_block_5b(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_full_2u32_5b(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_full_18_5b(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_ad(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_2u32_5b(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_full_2u32_5b(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_full_18_5b(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_5b(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_18_5b(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_5b(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_5b(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_last_5b(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_ad(Eurydice_borrow_slice_u8 data,
                                       Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_ad(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out);

/**
 A portable SHA3 256 implementation.
*/
void libcrux_iot_sha3_portable_sha256(Eurydice_mut_borrow_slice_u8 digest,
                                      Eurydice_borrow_slice_u8 data);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_absorb_final_ad0(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_keccak_ad0(Eurydice_borrow_slice_u8 data,
                                        Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_iot_sha3_portable_keccakx1_ad0(Eurydice_borrow_slice_u8 data,
                                            Eurydice_mut_borrow_slice_u8 out);

/**
 A portable SHAKE256 implementation.
*/
void libcrux_iot_sha3_portable_shake256(Eurydice_mut_borrow_slice_u8 digest,
                                        Eurydice_borrow_slice_u8 data);

typedef libcrux_iot_sha3_state_KeccakState
    libcrux_iot_sha3_portable_KeccakState;

/**
 Create a new SHAKE-128 state object.
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_portable_incremental_shake128_init(void);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_2u32_3a(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_full_2u32_3a(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_full_18_3a(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_absorb_final_c6(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
 Absorb
*/
void libcrux_iot_sha3_portable_incremental_shake128_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 data0);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_2u32_3a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_18_3a(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_3a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_three_blocks
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_three_blocks_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
 Squeeze three blocks
*/
void libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0);

/**
 Squeeze another block
*/
void libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0);

#define SHA3_224_DIGEST_SIZE ((size_t)28U)

#define SHA3_256_DIGEST_SIZE ((size_t)32U)

#define SHA3_384_DIGEST_SIZE ((size_t)48U)

#define SHA3_512_DIGEST_SIZE ((size_t)64U)

#define libcrux_iot_sha3_Algorithm_Sha224 1
#define libcrux_iot_sha3_Algorithm_Sha256 2
#define libcrux_iot_sha3_Algorithm_Sha384 3
#define libcrux_iot_sha3_Algorithm_Sha512 4

typedef uint8_t Algorithm;

/**
 Returns the output size of a digest.
*/
size_t digest_size(Algorithm mode);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_2u32_2c(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_18_2c(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_absorb_block_2c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_full_2u32_2c(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_full_18_2c(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_1e(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_2u32_2c(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_full_2u32_2c(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_full_18_2c(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_2c(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_18_2c(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_2c(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_2c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_last_2c(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_1e(Eurydice_borrow_slice_u8 data,
                                       Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_1e(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out);

/**
 A portable SHA3 224 implementation.
*/
void libcrux_iot_sha3_portable_sha224(Eurydice_mut_borrow_slice_u8 digest,
                                      Eurydice_borrow_slice_u8 data);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_2u32_7a(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_18_7a(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_absorb_block_7a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_full_2u32_7a(
    libcrux_iot_sha3_state_KeccakState *state, const Eurydice_arr_88 *blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_full_18_7a(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_88 *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_7c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_2u32_7a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_full_2u32_7a(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_full_18_7a(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_7a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_18_7a(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_7a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_7a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_last_7a(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_7c(Eurydice_borrow_slice_u8 data,
                                       Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_7c(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out);

/**
 A portable SHA3 384 implementation.
*/
void libcrux_iot_sha3_portable_sha384(Eurydice_mut_borrow_slice_u8 digest,
                                      Eurydice_borrow_slice_u8 data);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_18_3a(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_absorb_block_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_full_2u32_3a(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_88 *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_full_18_3a(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_88 *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_3a(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_last_3a(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_keccak_c6(Eurydice_borrow_slice_u8 data,
                                       Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_iot_sha3_portable_keccakx1_c6(Eurydice_borrow_slice_u8 data,
                                           Eurydice_mut_borrow_slice_u8 out);

#define LIBCRUX_IOT_SHA3_KECCAK_WIDTH ((size_t)200U)

/**
 A portable SHAKE128 implementation.
*/
void libcrux_iot_sha3_portable_shake128(Eurydice_mut_borrow_slice_u8 digest,
                                        Eurydice_borrow_slice_u8 data);

/**
 Perform four rounds of the keccak permutation functions
*/
void libcrux_iot_sha3_portable_incremental_keccakf1660_4rounds(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_five_blocks
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_five_blocks_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
 Squeeze five blocks
*/
void libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0);

/**
 Absorb some data for SHAKE-256 for the last time
*/
void libcrux_iot_sha3_portable_incremental_shake256_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 data);

/**
 Create a new SHAKE-256 state object.
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_portable_incremental_shake256_init(void);

/**
 Squeeze the first SHAKE-256 block
*/
void libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
 Squeeze the next SHAKE-256 block
*/
void libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.KeccakXofState
with const generics
- $136size_t
*/
typedef struct libcrux_iot_sha3_keccak_KeccakXofState_c7_s {
  libcrux_iot_sha3_state_KeccakState inner;
  Eurydice_arr_3d buf;
  size_t buf_len;
  bool sponge;
} libcrux_iot_sha3_keccak_KeccakXofState_c7;

typedef libcrux_iot_sha3_keccak_KeccakXofState_c7
    libcrux_iot_sha3_portable_incremental_Shake256Xof;

/**
A monomorphic instance of libcrux_iot_sha3.keccak.KeccakXofState
with const generics
- $168size_t
*/
typedef struct libcrux_iot_sha3_keccak_KeccakXofState_49_s {
  libcrux_iot_sha3_state_KeccakState inner;
  Eurydice_arr_27 buf;
  size_t buf_len;
  bool sponge;
} libcrux_iot_sha3_keccak_KeccakXofState_49;

typedef libcrux_iot_sha3_keccak_KeccakXofState_49
    libcrux_iot_sha3_portable_incremental_Shake128Xof;

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_sha3_H_DEFINED
#endif /* internal_libcrux_iot_sha3_H */
