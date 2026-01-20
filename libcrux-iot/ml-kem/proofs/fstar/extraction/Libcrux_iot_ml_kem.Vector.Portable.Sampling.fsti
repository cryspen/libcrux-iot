module Libcrux_iot_ml_kem.Vector.Portable.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

val rej_sample (a: t_Slice u8) (out: t_Slice i16)
    : Prims.Pure (t_Slice i16 & usize)
      (requires
        (Core_models.Slice.impl__len #u8 a <: usize) =. mk_usize 24 &&
        (Core_models.Slice.impl__len #i16 out <: usize) =. mk_usize 16)
      (ensures
        fun temp_0_ ->
          let (out_future: t_Slice i16), (result: usize) = temp_0_ in
          result <=. mk_usize 16 &&
          (Core_models.Slice.impl__len #i16 out_future <: usize) =. mk_usize 16)
