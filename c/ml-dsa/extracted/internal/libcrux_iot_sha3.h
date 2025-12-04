/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 637a6bc8a4c2a79875af5aa4e413c7ef3aa7f391
 * Eurydice: 788f967cfd9eaff503d3785f64072f851945c726
 * Karamel: 4e64d915da3c172d1dfad805b8e1a46beff938bc
 * F*: unset
 * Libcrux: 34a7778be03e250fff932df62147cec2b85ec54b
 */

#ifndef internal_libcrux_iot_sha3_H
#define internal_libcrux_iot_sha3_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_iot_sha3.h"
#include "libcrux_iot_mldsa_core.h"

typedef Eurydice_arr_b2 libcrux_iot_sha3_lane_Lane2U32;

#define libcrux_iot_sha3_Algorithm_Sha224 1
#define libcrux_iot_sha3_Algorithm_Sha256 2
#define libcrux_iot_sha3_Algorithm_Sha384 3
#define libcrux_iot_sha3_Algorithm_Sha512 4

typedef uint8_t libcrux_iot_sha3_Algorithm;

#define LIBCRUX_IOT_SHA3_SHA3_224_DIGEST_SIZE ((size_t)28U)

#define LIBCRUX_IOT_SHA3_SHA3_256_DIGEST_SIZE ((size_t)32U)

#define LIBCRUX_IOT_SHA3_SHA3_384_DIGEST_SIZE ((size_t)48U)

#define LIBCRUX_IOT_SHA3_SHA3_512_DIGEST_SIZE ((size_t)64U)

/**
 Returns the output size of a digest.
*/
static inline size_t libcrux_iot_sha3_digest_size(
    libcrux_iot_sha3_Algorithm mode) {
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
 A portable SHA3 224 implementation.
*/
static inline void libcrux_iot_sha3_portable_sha224(
    Eurydice_mut_borrow_slice_u8 digest, Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_1e(data, digest);
}

/**
 A portable SHA3 256 implementation.
*/
static inline void libcrux_iot_sha3_portable_sha256(
    Eurydice_mut_borrow_slice_u8 digest, Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_ad0(data, digest);
}

/**
 A portable SHA3 384 implementation.
*/
static inline void libcrux_iot_sha3_portable_sha384(
    Eurydice_mut_borrow_slice_u8 digest, Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_7c(data, digest);
}

/**
 A portable SHA3 512 implementation.
*/
static inline void libcrux_iot_sha3_portable_sha512(
    Eurydice_mut_borrow_slice_u8 digest, Eurydice_borrow_slice_u8 data) {
  libcrux_iot_sha3_portable_keccakx1_96(data, digest);
}

#define LIBCRUX_IOT_SHA3_KECCAK_WIDTH ((size_t)200U)

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

/**
 Perform four rounds of the keccak permutation functions
*/
static inline void libcrux_iot_sha3_portable_incremental_keccakf1660_4rounds(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_4rounds_bc(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_three_blocks
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_squeeze_first_three_blocks_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_mut_borrow_slice_u8_x2 uu____0 =
      libcrux_iot_sha3_lane_split_at_mut_n_8d_90(out, (size_t)168U);
  Eurydice_mut_borrow_slice_u8 o0 = uu____0.fst;
  Eurydice_mut_borrow_slice_u8 o10 = uu____0.snd;
  libcrux_iot_sha3_keccak_squeeze_first_block_3a(s, o0);
  Eurydice_mut_borrow_slice_u8_x2 uu____1 =
      libcrux_iot_sha3_lane_split_at_mut_n_8d_90(o10, (size_t)168U);
  Eurydice_mut_borrow_slice_u8 o1 = uu____1.fst;
  Eurydice_mut_borrow_slice_u8 o2 = uu____1.snd;
  libcrux_iot_sha3_keccak_squeeze_next_block_3a(s, o1);
  libcrux_iot_sha3_keccak_squeeze_next_block_3a(s, o2);
}

/**
 Squeeze three blocks
*/
static inline void
libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0) {
  libcrux_iot_sha3_keccak_squeeze_first_three_blocks_3a(s, out0);
}

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_sha3_H_DEFINED
#endif /* internal_libcrux_iot_sha3_H */
