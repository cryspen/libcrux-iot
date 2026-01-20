/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 146b7dce58cb11ca8010b1c947c3437a959dcd88
 * Eurydice: cdf02f9d8ed0d73f88c0a495c5b79359a51398fc
 * Karamel: 8e7262955105599e91f3a99c9ab3d3387f7046f2
 * F*: 89901492c020c74b82d811d27f3149c222d9b8b5
 * Libcrux: 2259f47ca2a2a060c9fd147ccc78ed3588bfd288
 */

#ifndef libcrux_iot_sha3_H
#define libcrux_iot_sha3_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_iot_core.h"

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_sha3_lane_Lane2U32
with const generics
- $25size_t
*/
typedef struct Eurydice_arr_f8_s {
  Eurydice_arr_b2 data[25U];
} Eurydice_arr_f8;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_sha3_lane_Lane2U32
with const generics
- $5size_t
*/
typedef struct Eurydice_arr_6c_s {
  Eurydice_arr_b2 data[5U];
} Eurydice_arr_6c;

typedef struct libcrux_iot_sha3_state_KeccakState_s {
  Eurydice_arr_f8 st;
  Eurydice_arr_6c c;
  Eurydice_arr_6c d;
  size_t i;
} libcrux_iot_sha3_state_KeccakState;

/**
 SHA3 224

 Preconditions:
 - `digest.len() == 28`
*/
void sha224_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload);

/**
 SHA3 224
*/
Eurydice_arr_f1 sha224(Eurydice_borrow_slice_u8 data);

/**
 SHA3 256
*/
void sha256_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload);

/**
 SHA3 256
*/
Eurydice_arr_600 sha256(Eurydice_borrow_slice_u8 data);

/**
 SHA3 384
*/
void sha384_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload);

/**
 SHA3 384
*/
Eurydice_arr_5f sha384(Eurydice_borrow_slice_u8 data);

/**
 SHA3 512
*/
void sha512_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload);

/**
 SHA3 512
*/
Eurydice_arr_06 sha512(Eurydice_borrow_slice_u8 data);

/**
 SHAKE 128

 Writes `out.len()` bytes.
*/
void shake128_ema(Eurydice_mut_borrow_slice_u8 out,
                  Eurydice_borrow_slice_u8 data);

/**
 SHAKE 256

 Writes `out.len()` bytes.
*/
void shake256_ema(Eurydice_mut_borrow_slice_u8 out,
                  Eurydice_borrow_slice_u8 data);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_sha3_portable_KeccakState
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_5e_s {
  libcrux_iot_sha3_state_KeccakState data[4U];
} Eurydice_arr_5e;

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_sha3_H_DEFINED
#endif /* libcrux_iot_sha3_H */
