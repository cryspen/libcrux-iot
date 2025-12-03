/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 637a6bc8a4c2a79875af5aa4e413c7ef3aa7f391
 * Eurydice: 5ca42bdb4309a18e332321ca9ae66607824428eb
 * Karamel: 4e64d915da3c172d1dfad805b8e1a46beff938bc
 * F*: unset
 * Libcrux: 936916cddc98fa7c87698a18d08336862d718614
 */

#ifndef libcrux_iot_sha3_H
#define libcrux_iot_sha3_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_iot_core.h"

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
Eurydice_arr_60 sha256(Eurydice_borrow_slice_u8 data);

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

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_sha3_H_DEFINED
#endif /* libcrux_iot_sha3_H */
