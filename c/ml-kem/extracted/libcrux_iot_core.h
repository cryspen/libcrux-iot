/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 146b7dce58cb11ca8010b1c947c3437a959dcd88
 * Eurydice: cdf02f9d8ed0d73f88c0a495c5b79359a51398fc
 * Karamel: 8e7262955105599e91f3a99c9ab3d3387f7046f2
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: f5a2e8205f49b35cb3e6b03aa25e16c26318ad09
 */

#ifndef libcrux_iot_core_H
#define libcrux_iot_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1568size_t
*/
typedef struct Eurydice_arr_00_s {
  uint8_t data[1568U];
} Eurydice_arr_00;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $3168size_t
*/
typedef struct Eurydice_arr_17_s {
  uint8_t data[3168U];
} Eurydice_arr_17;

/**
A monomorphic instance of libcrux_iot_ml_kem.types.MlKemKeyPair
with const generics
- $3168size_t
- $1568size_t
*/
typedef struct libcrux_iot_ml_kem_types_MlKemKeyPair_f7_s {
  Eurydice_arr_17 sk;
  Eurydice_arr_00 pk;
} libcrux_iot_ml_kem_types_MlKemKeyPair_f7;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $34size_t
*/
typedef struct Eurydice_arr_48_s {
  uint8_t data[34U];
} Eurydice_arr_48;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr uint8_t[[$34size_t]], size_t

*/
typedef struct Eurydice_dst_ref_shared_60_s {
  const Eurydice_arr_48 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_60;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $168size_t
*/
typedef struct Eurydice_arr_27_s {
  uint8_t data[168U];
} Eurydice_arr_27;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr uint8_t[[$168size_t]], size_t

*/
typedef struct Eurydice_dst_ref_mut_36_s {
  Eurydice_arr_27 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_36;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $504size_t
*/
typedef struct Eurydice_arr_b0_s {
  uint8_t data[504U];
} Eurydice_arr_b0;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr uint8_t[[$504size_t]], size_t

*/
typedef struct Eurydice_dst_ref_mut_ea_s {
  Eurydice_arr_b0 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_ea;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_600_s {
  uint8_t data[32U];
} Eurydice_arr_600;

/**
A monomorphic instance of K.
with types libcrux_iot_ml_kem_types_MlKemCiphertext[[$1568size_t]], Eurydice_arr
uint8_t[[$32size_t]]

*/
typedef struct tuple_32_s {
  Eurydice_arr_00 fst;
  Eurydice_arr_600 snd;
} tuple_32;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $33size_t
*/
typedef struct Eurydice_arr_3e_s {
  uint8_t data[33U];
} Eurydice_arr_3e;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr uint8_t[[$33size_t]], size_t

*/
typedef struct Eurydice_dst_ref_shared_d2_s {
  const Eurydice_arr_3e *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_d2;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1184size_t
*/
typedef struct Eurydice_arr_74_s {
  uint8_t data[1184U];
} Eurydice_arr_74;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2400size_t
*/
typedef struct Eurydice_arr_ea_s {
  uint8_t data[2400U];
} Eurydice_arr_ea;

/**
A monomorphic instance of libcrux_iot_ml_kem.types.MlKemKeyPair
with const generics
- $2400size_t
- $1184size_t
*/
typedef struct libcrux_iot_ml_kem_types_MlKemKeyPair_5f_s {
  Eurydice_arr_ea sk;
  Eurydice_arr_74 pk;
} libcrux_iot_ml_kem_types_MlKemKeyPair_5f;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1088size_t
*/
typedef struct Eurydice_arr_2c_s {
  uint8_t data[1088U];
} Eurydice_arr_2c;

/**
A monomorphic instance of K.
with types libcrux_iot_ml_kem_types_MlKemCiphertext[[$1088size_t]], Eurydice_arr
uint8_t[[$32size_t]]

*/
typedef struct tuple_50_s {
  Eurydice_arr_2c fst;
  Eurydice_arr_600 snd;
} tuple_50;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $64size_t
*/
typedef struct Eurydice_arr_06_s {
  uint8_t data[64U];
} Eurydice_arr_06;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_shared_fc_s {
  const int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_fc;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_mut_fc_s {
  int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_fc;

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_e2_s {
  int16_t data[16U];
} Eurydice_arr_e2;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $48size_t
*/
typedef struct Eurydice_arr_5f_s {
  uint8_t data[48U];
} Eurydice_arr_5f;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $28size_t
*/
typedef struct Eurydice_arr_f1_s {
  uint8_t data[28U];
} Eurydice_arr_f1;

/**
A monomorphic instance of Eurydice.arr
with types uint32_t
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_b2_s {
  uint32_t data[2U];
} Eurydice_arr_b2;

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_core_H_DEFINED
#endif /* libcrux_iot_core_H */
