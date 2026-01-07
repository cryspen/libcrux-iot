module Libcrux_iot_ml_kem.Vector.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let v_FIELD_MODULUS: i16 = mk_i16 3329

let v_FIELD_ELEMENTS_IN_VECTOR: usize = mk_usize 16

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = mk_u32 62209

let v_BARRETT_SHIFT: i32 = mk_i32 26

let v_BARRETT_R: i32 = mk_i32 1 <<! v_BARRETT_SHIFT
