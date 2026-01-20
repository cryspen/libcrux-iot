module Libcrux_iot_ml_kem.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

/// Pad the `slice` with `0`s at the end.
val into_padded_array (v_LEN: usize) (slice: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN)
      (requires (Core_models.Slice.impl__len #u8 slice <: usize) <=. v_LEN)
      (fun _ -> Prims.l_True)

val prf_input_inc
      (v_K: usize)
      (prf_inputs: t_Array (t_Array u8 (mk_usize 33)) v_K)
      (domain_separator: u8)
    : Prims.Pure (t_Array (t_Array u8 (mk_usize 33)) v_K & u8)
      (requires
        domain_separator <=. (Core_models.Num.impl_u8__MAX -! (cast (v_K <: usize) <: u8) <: u8) &&
        v_K <=. mk_usize 4)
      (ensures
        fun temp_0_ ->
          let (prf_inputs_future: t_Array (t_Array u8 (mk_usize 33)) v_K), (result: u8) = temp_0_ in
          result =. (domain_separator +! (cast (v_K <: usize) <: u8) <: u8))
