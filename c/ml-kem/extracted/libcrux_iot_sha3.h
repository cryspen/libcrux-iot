/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 2381cbc416ef2ad0b561c362c500bc84f36b6785
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: 3613334610aa951d9320aba05c143b366adfe599
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

/**
 SHA3 224

 Preconditions:
 - `digest.len() == 28`
*/
void sha224_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 224
*/
void sha224(Eurydice_slice data, uint8_t ret[28U]);

/**
 SHA3 256
*/
void sha256_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 256
*/
void sha256(Eurydice_slice data, uint8_t ret[32U]);

/**
 SHA3 384
*/
void sha384_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 384
*/
void sha384(Eurydice_slice data, uint8_t ret[48U]);

/**
 SHA3 512
*/
void sha512_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 512
*/
void sha512(Eurydice_slice data, uint8_t ret[64U]);

/**
 SHAKE 128

 Writes `out.len()` bytes.
*/
void shake128_ema(Eurydice_slice out, Eurydice_slice data);

/**
 SHAKE 256

 Writes `out.len()` bytes.
*/
void shake256_ema(Eurydice_slice out, Eurydice_slice data);

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_sha3_H_DEFINED
#endif /* libcrux_iot_sha3_H */
