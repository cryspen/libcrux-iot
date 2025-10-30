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

#ifndef libcrux_iot_sha3_H
#define libcrux_iot_sha3_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

typedef struct libcrux_iot_sha3_lane_Lane2U32_s {
  uint32_t fst[2U];
} libcrux_iot_sha3_lane_Lane2U32;

typedef struct libcrux_iot_sha3_state_KeccakState_s {
  libcrux_iot_sha3_lane_Lane2U32 st[25U];
  libcrux_iot_sha3_lane_Lane2U32 c[5U];
  libcrux_iot_sha3_lane_Lane2U32 d[5U];
  size_t i;
} libcrux_iot_sha3_state_KeccakState;

typedef libcrux_iot_sha3_state_KeccakState
    libcrux_iot_sha3_portable_KeccakState;

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
 SHA3 224

 Preconditions:
 - `digest.len() == 28`
*/
void libcrux_iot_sha3_sha224_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 224
*/
void libcrux_iot_sha3_sha224(Eurydice_slice data, uint8_t ret[28U]);

/**
 SHA3 256
*/
void libcrux_iot_sha3_sha256_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 256
*/
void libcrux_iot_sha3_sha256(Eurydice_slice data, uint8_t ret[32U]);

/**
 SHA3 384
*/
void libcrux_iot_sha3_sha384_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 384
*/
void libcrux_iot_sha3_sha384(Eurydice_slice data, uint8_t ret[48U]);

/**
 SHA3 512
*/
void libcrux_iot_sha3_sha512_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 512
*/
void libcrux_iot_sha3_sha512(Eurydice_slice data, uint8_t ret[64U]);

/**
 SHAKE 128

 Writes `out.len()` bytes.
*/
void libcrux_iot_sha3_shake128_ema(Eurydice_slice out, Eurydice_slice data);

/**
 SHAKE 256

 Writes `out.len()` bytes.
*/
void libcrux_iot_sha3_shake256_ema(Eurydice_slice out, Eurydice_slice data);

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_sha3_H_DEFINED
#endif /* libcrux_iot_sha3_H */
