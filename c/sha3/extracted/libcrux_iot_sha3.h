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

#ifndef libcrux_iot_sha3_H
#define libcrux_iot_sha3_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

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
