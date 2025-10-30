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
 * Libcrux: 77a80e3eb2196754d31058d237c0052000775d2c
 */

#ifndef internal_libcrux_iot_sha3_H
#define internal_libcrux_iot_sha3_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_iot_sha3.h"
#include "internal/libcrux_iot_core.h"

#define libcrux_iot_sha3_Algorithm_Sha224 1
#define libcrux_iot_sha3_Algorithm_Sha256 2
#define libcrux_iot_sha3_Algorithm_Sha384 3
#define libcrux_iot_sha3_Algorithm_Sha512 4

typedef uint8_t Algorithm;

/**
 Returns the output size of a digest.
*/
size_t digest_size(Algorithm mode);

typedef struct libcrux_iot_sha3_lane_Lane2U32_s {
  uint32_t fst[2U];
} libcrux_iot_sha3_lane_Lane2U32;

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
libcrux_iot_sha3_lane_Lane2U32 libcrux_iot_sha3_lane_from_ints_8d(
    uint32_t value[2U]);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
libcrux_iot_sha3_lane_Lane2U32 libcrux_iot_sha3_lane_zero_8d(void);

typedef struct libcrux_iot_sha3_state_KeccakState_s {
  libcrux_iot_sha3_lane_Lane2U32 st[25U];
  libcrux_iot_sha3_lane_Lane2U32 c[5U];
  libcrux_iot_sha3_lane_Lane2U32 d[5U];
  size_t i;
} libcrux_iot_sha3_state_KeccakState;

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
libcrux_iot_sha3_state_KeccakState libcrux_iot_sha3_state_new_18(void);

/**
This function found in impl {core::convert::From<@Array<u32, 2usize>> for
libcrux_iot_sha3::lane::Lane2U32}
*/
libcrux_iot_sha3_lane_Lane2U32 libcrux_iot_sha3_lane_from_47(
    uint32_t value[2U]);

/**
This function found in impl {core::ops::index::Index<usize, u32> for
libcrux_iot_sha3::lane::Lane2U32}
*/
uint32_t *libcrux_iot_sha3_lane_index_cc(libcrux_iot_sha3_lane_Lane2U32 *self,
                                         size_t index);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
libcrux_iot_sha3_lane_Lane2U32 libcrux_iot_sha3_lane_interleave_8d(
    libcrux_iot_sha3_lane_Lane2U32 self);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
libcrux_iot_sha3_lane_Lane2U32 libcrux_iot_sha3_state_get_lane_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
void libcrux_iot_sha3_state_set_lane_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    libcrux_iot_sha3_lane_Lane2U32 lane);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
uint32_t libcrux_iot_sha3_state_get_with_zeta_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j, size_t zeta);

/**
This function found in impl {core::ops::index::IndexMut<usize, u32> for
libcrux_iot_sha3::lane::Lane2U32}
*/
uint32_t *libcrux_iot_sha3_lane_index_mut_c5(
    libcrux_iot_sha3_lane_Lane2U32 *self, size_t index);

extern const uint32_t libcrux_iot_sha3_keccak_RC_INTERLEAVED_0[255U];

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
void libcrux_iot_sha3_state_set_with_zeta_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j, size_t zeta,
    uint32_t v);

extern const uint32_t libcrux_iot_sha3_keccak_RC_INTERLEAVED_1[255U];

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

void libcrux_iot_sha3_keccak_keccakf1600(libcrux_iot_sha3_state_KeccakState *s);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
libcrux_iot_sha3_lane_Lane2U32 libcrux_iot_sha3_lane_deinterleave_8d(
    libcrux_iot_sha3_lane_Lane2U32 self);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_2u32_2c(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_slice blocks,
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
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_absorb_block_2c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_full_2u32_2c(
    libcrux_iot_sha3_state_KeccakState *state, uint8_t *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_full_18_2c(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_1e(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice last, size_t start,
    size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_2u32_2c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_full_2u32_2c(
    libcrux_iot_sha3_state_KeccakState *s, uint8_t *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_full_18_2c(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_2c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.lane.split_at_mut_1
with types uint8_t

*/
Eurydice_slice_uint8_t_x2 libcrux_iot_sha3_lane_split_at_mut_1_90(
    Eurydice_slice out, size_t mid);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
/**
A monomorphic instance of libcrux_iot_sha3.lane.split_at_mut_n_8d
with types uint8_t

*/
Eurydice_slice_uint8_t_x2 libcrux_iot_sha3_lane_split_at_mut_n_8d_90(
    Eurydice_slice a, size_t mid);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_18_2c(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_2c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_2c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_last_2c(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_1e(Eurydice_slice data, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_1e(Eurydice_slice data,
                                           Eurydice_slice out);

/**
 A portable SHA3 224 implementation.
*/
void libcrux_iot_sha3_portable_sha224(Eurydice_slice digest,
                                      Eurydice_slice data);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_2u32_5b(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_slice blocks,
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
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_absorb_block_5b(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_full_2u32_5b(
    libcrux_iot_sha3_state_KeccakState *state, uint8_t *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_full_18_5b(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_ad(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice last, size_t start,
    size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_2u32_5b(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_full_2u32_5b(
    libcrux_iot_sha3_state_KeccakState *s, uint8_t *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_full_18_5b(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_5b(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_18_5b(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_5b(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_5b(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_last_5b(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_ad(Eurydice_slice data, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_ad(Eurydice_slice data,
                                           Eurydice_slice out);

/**
 A portable SHA3 256 implementation.
*/
void libcrux_iot_sha3_portable_sha256(Eurydice_slice digest,
                                      Eurydice_slice data);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_2u32_7a(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_slice blocks,
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
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_absorb_block_7a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_full_2u32_7a(
    libcrux_iot_sha3_state_KeccakState *state, uint8_t *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_full_18_7a(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_7c(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice last, size_t start,
    size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_2u32_7a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_full_2u32_7a(
    libcrux_iot_sha3_state_KeccakState *s, uint8_t *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_full_18_7a(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_7a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_18_7a(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_7a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_7a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_last_7a(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_7c(Eurydice_slice data, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_7c(Eurydice_slice data,
                                           Eurydice_slice out);

/**
 A portable SHA3 384 implementation.
*/
void libcrux_iot_sha3_portable_sha384(Eurydice_slice digest,
                                      Eurydice_slice data);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_2u32_f8(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_slice blocks,
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
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_absorb_block_f8(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_full_2u32_f8(
    libcrux_iot_sha3_state_KeccakState *state, uint8_t *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_full_18_f8(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_96(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice last, size_t start,
    size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_2u32_f8(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_full_2u32_f8(
    libcrux_iot_sha3_state_KeccakState *s, uint8_t *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_full_18_f8(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_f8(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_18_f8(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_f8(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_f8(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_last_f8(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_96(Eurydice_slice data, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_iot_sha3_portable_keccakx1_96(Eurydice_slice data,
                                           Eurydice_slice out);

/**
 A portable SHA3 512 implementation.
*/
void libcrux_iot_sha3_portable_sha512(Eurydice_slice digest,
                                      Eurydice_slice data);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_2u32_3a(
    libcrux_iot_sha3_state_KeccakState *state, Eurydice_slice blocks,
    size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_18_3a(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_absorb_block_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_full_2u32_3a(
    libcrux_iot_sha3_state_KeccakState *state, uint8_t *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_full_18_3a(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_absorb_final_c6(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice last, size_t start,
    size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_2u32_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_full_2u32_3a(
    libcrux_iot_sha3_state_KeccakState *s, uint8_t *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_full_18_3a(
    libcrux_iot_sha3_state_KeccakState *self, uint8_t *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_18_3a(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_last_3a(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_keccak_c6(Eurydice_slice data, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_iot_sha3_portable_keccakx1_c6(Eurydice_slice data,
                                           Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_absorb_final_ad0(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice last, size_t start,
    size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_keccak_ad0(Eurydice_slice data,
                                        Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_iot_sha3_portable_keccakx1_ad0(Eurydice_slice data,
                                            Eurydice_slice out);

#define LIBCRUX_IOT_SHA3_KECCAK_WIDTH ((size_t)200U)

/**
This function found in impl {core::clone::Clone for
libcrux_iot_sha3::lane::Lane2U32}
*/
libcrux_iot_sha3_lane_Lane2U32 libcrux_iot_sha3_lane_clone_f6(
    libcrux_iot_sha3_lane_Lane2U32 *self);

/**
 A portable SHAKE128 implementation.
*/
void libcrux_iot_sha3_portable_shake128(Eurydice_slice digest,
                                        Eurydice_slice data);

/**
 A portable SHAKE256 implementation.
*/
void libcrux_iot_sha3_portable_shake256(Eurydice_slice digest,
                                        Eurydice_slice data);

typedef libcrux_iot_sha3_state_KeccakState
    libcrux_iot_sha3_portable_KeccakState;

/**
 Perform four rounds of the keccak permutation functions
*/
void libcrux_iot_sha3_portable_incremental_keccakf1660_4rounds(
    libcrux_iot_sha3_state_KeccakState *s);

/**
 Absorb
*/
void libcrux_iot_sha3_portable_incremental_shake128_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice data0);

/**
 Create a new SHAKE-128 state object.
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_portable_incremental_shake128_init(void);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_five_blocks
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_five_blocks_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
 Squeeze five blocks
*/
void libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out0);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_three_blocks
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_three_blocks_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
 Squeeze three blocks
*/
void libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out0);

/**
 Squeeze another block
*/
void libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out0);

/**
 Absorb some data for SHAKE-256 for the last time
*/
void libcrux_iot_sha3_portable_incremental_shake256_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice data);

/**
 Create a new SHAKE-256 state object.
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_portable_incremental_shake256_init(void);

/**
 Squeeze the first SHAKE-256 block
*/
void libcrux_iot_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
 Squeeze the next SHAKE-256 block
*/
void libcrux_iot_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.KeccakXofState
with const generics
- $136size_t
*/
typedef struct libcrux_iot_sha3_keccak_KeccakXofState_c7_s {
  libcrux_iot_sha3_state_KeccakState inner;
  uint8_t buf[136U];
  size_t buf_len;
  bool sponge;
} libcrux_iot_sha3_keccak_KeccakXofState_c7;

typedef libcrux_iot_sha3_keccak_KeccakXofState_c7
    libcrux_iot_sha3_portable_incremental_Shake256Xof;

/**
 Consume the internal buffer and the required amount of the input to pad to
 `RATE`.

 Returns the `consumed` bytes from `inputs` if there's enough buffered
 content to consume, and `0` otherwise.
 If `consumed > 0` is returned, `self.buf` contains a full block to be
 loaded.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.fill_buffer_f0
with const generics
- RATE= 136
*/
size_t libcrux_iot_sha3_keccak_fill_buffer_f0_5b(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice inputs);

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_full_f0
with const generics
- RATE= 136
*/
size_t libcrux_iot_sha3_keccak_absorb_full_f0_5b(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice inputs);

/**
 Absorb

 This function takes any number of bytes to absorb and buffers if it's not
 enough. The function assumes that all input slices in `blocks` have the same
 length.

 Only a multiple of `RATE` blocks are absorbed.
 For the remaining bytes [`absorb_final`] needs to be called.

 This works best with relatively small `inputs`.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_f0
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_absorb_f0_5b(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice inputs);

/**
 Shake256 absorb
*/
/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<136usize> for
libcrux_iot_sha3::portable::incremental::Shake256Xof}
*/
void libcrux_iot_sha3_portable_incremental_absorb_a5(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice input);

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final_f0
with const generics
- RATE= 136
- DELIMITER= 31
*/
void libcrux_iot_sha3_keccak_absorb_final_f0_ad(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice inputs);

/**
 Shake256 absorb final
*/
/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<136usize> for
libcrux_iot_sha3::portable::incremental::Shake256Xof}
*/
void libcrux_iot_sha3_portable_incremental_absorb_final_a5(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice input);

/**
 An all zero block
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.zero_block_f0
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_zero_block_f0_5b(uint8_t ret[136U]);

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.new_f0
with const generics
- RATE= 136
*/
libcrux_iot_sha3_keccak_KeccakXofState_c7 libcrux_iot_sha3_keccak_new_f0_5b(
    void);

/**
 Shake256 new state
*/
/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<136usize> for
libcrux_iot_sha3::portable::incremental::Shake256Xof}
*/
libcrux_iot_sha3_keccak_KeccakXofState_c7
libcrux_iot_sha3_portable_incremental_new_a5(void);

/**
 `out` has the exact size we want here. It must be less than or equal to `RATE`.
*/
/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_18_5b(libcrux_iot_sha3_state_KeccakState self,
                                        Eurydice_slice out);

/**
 Squeeze `N` x `LEN` bytes.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_f0
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_f0_5b(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice out);

/**
 Shake256 squeeze
*/
/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<136usize> for
libcrux_iot_sha3::portable::incremental::Shake256Xof}
*/
void libcrux_iot_sha3_portable_incremental_squeeze_a5(
    libcrux_iot_sha3_keccak_KeccakXofState_c7 *self, Eurydice_slice out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.KeccakXofState
with const generics
- $168size_t
*/
typedef struct libcrux_iot_sha3_keccak_KeccakXofState_49_s {
  libcrux_iot_sha3_state_KeccakState inner;
  uint8_t buf[168U];
  size_t buf_len;
  bool sponge;
} libcrux_iot_sha3_keccak_KeccakXofState_49;

typedef libcrux_iot_sha3_keccak_KeccakXofState_49
    libcrux_iot_sha3_portable_incremental_Shake128Xof;

/**
 Consume the internal buffer and the required amount of the input to pad to
 `RATE`.

 Returns the `consumed` bytes from `inputs` if there's enough buffered
 content to consume, and `0` otherwise.
 If `consumed > 0` is returned, `self.buf` contains a full block to be
 loaded.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.fill_buffer_f0
with const generics
- RATE= 168
*/
size_t libcrux_iot_sha3_keccak_fill_buffer_f0_3a(
    libcrux_iot_sha3_keccak_KeccakXofState_49 *self, Eurydice_slice inputs);

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_full_f0
with const generics
- RATE= 168
*/
size_t libcrux_iot_sha3_keccak_absorb_full_f0_3a(
    libcrux_iot_sha3_keccak_KeccakXofState_49 *self, Eurydice_slice inputs);

/**
 Absorb

 This function takes any number of bytes to absorb and buffers if it's not
 enough. The function assumes that all input slices in `blocks` have the same
 length.

 Only a multiple of `RATE` blocks are absorbed.
 For the remaining bytes [`absorb_final`] needs to be called.

 This works best with relatively small `inputs`.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_f0
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_absorb_f0_3a(
    libcrux_iot_sha3_keccak_KeccakXofState_49 *self, Eurydice_slice inputs);

/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<168usize> for
libcrux_iot_sha3::portable::incremental::Shake128Xof}
*/
void libcrux_iot_sha3_portable_incremental_absorb_7b(
    libcrux_iot_sha3_keccak_KeccakXofState_49 *self, Eurydice_slice input);

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final_f0
with const generics
- RATE= 168
- DELIMITER= 31
*/
void libcrux_iot_sha3_keccak_absorb_final_f0_c6(
    libcrux_iot_sha3_keccak_KeccakXofState_49 *self, Eurydice_slice inputs);

/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<168usize> for
libcrux_iot_sha3::portable::incremental::Shake128Xof}
*/
void libcrux_iot_sha3_portable_incremental_absorb_final_7b(
    libcrux_iot_sha3_keccak_KeccakXofState_49 *self, Eurydice_slice input);

/**
 An all zero block
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.zero_block_f0
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_zero_block_f0_3a(uint8_t ret[168U]);

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.new_f0
with const generics
- RATE= 168
*/
libcrux_iot_sha3_keccak_KeccakXofState_49 libcrux_iot_sha3_keccak_new_f0_3a(
    void);

/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<168usize> for
libcrux_iot_sha3::portable::incremental::Shake128Xof}
*/
libcrux_iot_sha3_keccak_KeccakXofState_49
libcrux_iot_sha3_portable_incremental_new_7b(void);

/**
 `out` has the exact size we want here. It must be less than or equal to `RATE`.
*/
/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_18_3a(libcrux_iot_sha3_state_KeccakState self,
                                        Eurydice_slice out);

/**
 Squeeze `N` x `LEN` bytes.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakXofState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_f0
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_f0_3a(
    libcrux_iot_sha3_keccak_KeccakXofState_49 *self, Eurydice_slice out);

/**
 Shake128 squeeze
*/
/**
This function found in impl
{libcrux_iot_sha3::portable::incremental::Xof<168usize> for
libcrux_iot_sha3::portable::incremental::Shake128Xof}
*/
void libcrux_iot_sha3_portable_incremental_squeeze_7b(
    libcrux_iot_sha3_keccak_KeccakXofState_49 *self, Eurydice_slice out);

/**
This function found in impl {core::clone::Clone for
libcrux_iot_sha3::portable::KeccakState}
*/
libcrux_iot_sha3_state_KeccakState libcrux_iot_sha3_portable_clone_4f(
    libcrux_iot_sha3_state_KeccakState *self);

/**
This function found in impl {core::clone::Clone for
libcrux_iot_sha3::state::KeccakState}
*/
libcrux_iot_sha3_state_KeccakState libcrux_iot_sha3_state_clone_0f(
    libcrux_iot_sha3_state_KeccakState *self);

/**
This function found in impl {core::convert::From<libcrux_iot_sha3::Algorithm>
for u32}
*/
uint32_t from_c3(Algorithm v);

/**
This function found in impl {core::convert::From<u32> for
libcrux_iot_sha3::Algorithm}
*/
Algorithm from_c2(uint32_t v);

typedef uint8_t Sha3_512Digest[64U];

typedef uint8_t Sha3_384Digest[48U];

typedef uint8_t Sha3_256Digest[32U];

typedef uint8_t Sha3_224Digest[28U];

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_sha3_H_DEFINED
#endif /* internal_libcrux_iot_sha3_H */
