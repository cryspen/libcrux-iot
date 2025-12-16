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

#ifndef libcrux_iot_sha3_H
#define libcrux_iot_sha3_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_iot_mldsa_core.h"

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

typedef libcrux_iot_sha3_state_KeccakState
    libcrux_iot_sha3_portable_KeccakState;

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
 SHA3 224

 Preconditions:
 - `digest.len() == 28`
*/
void libcrux_iot_sha3_sha224_ema(Eurydice_mut_borrow_slice_u8 digest,
                                 Eurydice_borrow_slice_u8 payload);

/**
 SHA3 224
*/
Eurydice_arr_f1 libcrux_iot_sha3_sha224(Eurydice_borrow_slice_u8 data);

/**
 SHA3 256
*/
void libcrux_iot_sha3_sha256_ema(Eurydice_mut_borrow_slice_u8 digest,
                                 Eurydice_borrow_slice_u8 payload);

/**
 SHA3 256
*/
Eurydice_arr_60 libcrux_iot_sha3_sha256(Eurydice_borrow_slice_u8 data);

/**
 SHA3 384
*/
void libcrux_iot_sha3_sha384_ema(Eurydice_mut_borrow_slice_u8 digest,
                                 Eurydice_borrow_slice_u8 payload);

/**
 SHA3 384
*/
Eurydice_arr_5f libcrux_iot_sha3_sha384(Eurydice_borrow_slice_u8 data);

/**
 SHA3 512
*/
void libcrux_iot_sha3_sha512_ema(Eurydice_mut_borrow_slice_u8 digest,
                                 Eurydice_borrow_slice_u8 payload);

/**
 SHA3 512
*/
Eurydice_arr_06 libcrux_iot_sha3_sha512(Eurydice_borrow_slice_u8 data);

/**
 SHAKE 128

 Writes `out.len()` bytes.
*/
void libcrux_iot_sha3_shake128_ema(Eurydice_mut_borrow_slice_u8 out,
                                   Eurydice_borrow_slice_u8 data);

/**
 SHAKE 256

 Writes `out.len()` bytes.
*/
void libcrux_iot_sha3_shake256_ema(Eurydice_mut_borrow_slice_u8 out,
                                   Eurydice_borrow_slice_u8 data);

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_sha3_H_DEFINED
#endif /* libcrux_iot_sha3_H */
