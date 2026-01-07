module Libcrux_iot_ml_kem.Spec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let bounded_i32 (x bound: i32) =
  bound >=. mk_i32 0 && x >=. (Core.Ops.Arith.f_neg bound <: i32) && x <=. bound

let bounded_i16 (x bound: i16) =
  bound >=. mk_i16 0 && x >=. (Core.Ops.Arith.f_neg bound <: i16) && x <=. bound

let bounded_i16x16 (x: t_Array i16 (mk_usize 16)) (b: i16) =
  bounded_i16 (x.[ mk_usize 0 ] <: i16) b && bounded_i16 (x.[ mk_usize 1 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 2 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 3 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 4 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 5 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 6 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 7 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 8 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 9 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 10 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 11 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 12 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 13 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 14 ] <: i16) b &&
  bounded_i16 (x.[ mk_usize 15 ] <: i16) b
