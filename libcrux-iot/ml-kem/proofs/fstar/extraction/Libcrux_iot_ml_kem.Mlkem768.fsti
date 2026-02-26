module Libcrux_iot_ml_kem.Mlkem768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let v_RANK: usize = mk_usize 3

let v_T_AS_NTT_ENCODED_SIZE: usize =
  ((v_RANK *! Libcrux_iot_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux_iot_ml_kem.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  mk_usize 8

let v_CPA_PKE_SECRET_KEY_SIZE: usize =
  ((v_RANK *! Libcrux_iot_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux_iot_ml_kem.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  mk_usize 8

let v_CPA_PKE_PUBLIC_KEY_SIZE: usize = v_T_AS_NTT_ENCODED_SIZE +! mk_usize 32

let v_SECRET_KEY_SIZE: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE +! v_CPA_PKE_PUBLIC_KEY_SIZE <: usize) +!
    Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE
    <:
    usize) +!
  Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE
