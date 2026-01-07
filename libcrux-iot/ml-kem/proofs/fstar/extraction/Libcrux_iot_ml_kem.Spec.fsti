module Libcrux_iot_ml_kem.Spec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

/// -bound <= x <= bound
val bounded_i32 (x bound: i32) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// -bound <= x <= bound
val bounded_i16 (x bound: i16) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val bounded_i16x16 (x: t_Array i16 (mk_usize 16)) (b: i16)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)
