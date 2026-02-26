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

let into_padded_array (v_LEN: usize) (slice: t_Slice u8) =
  let out:t_Array u8 v_LEN =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      v_LEN
  in
  let out:t_Array u8 v_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core_models.Ops.Range.f_start = mk_usize 0;
          Core_models.Ops.Range.f_end = Core_models.Slice.impl__len #u8 slice <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (out.[ {
                Core_models.Ops.Range.f_start = mk_usize 0;
                Core_models.Ops.Range.f_end = Core_models.Slice.impl__len #u8 slice <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          slice
        <:
        t_Slice u8)
  in
  out

let prf_input_inc
      (v_K: usize)
      (prf_inputs: t_Array (t_Array u8 (mk_usize 33)) v_K)
      (domain_separator: u8)
     =
  let e_domain_separator_init:u8 = domain_separator in
  let e_prf_inputs_init:t_Array (t_Array u8 (mk_usize 33)) v_K =
    Core_models.Clone.f_clone #(t_Array (t_Array u8 (mk_usize 33)) v_K)
      #FStar.Tactics.Typeclasses.solve
      prf_inputs
  in
  let (domain_separator: u8), (prf_inputs: t_Array (t_Array u8 (mk_usize 33)) v_K) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ i ->
          let (domain_separator: u8), (prf_inputs: t_Array (t_Array u8 (mk_usize 33)) v_K) =
            temp_0_
          in
          let i:usize = i in
          domain_separator =. (e_domain_separator_init +! (cast (i <: usize) <: u8) <: u8) <: bool)
      (domain_separator, prf_inputs <: (u8 & t_Array (t_Array u8 (mk_usize 33)) v_K))
      (fun temp_0_ i ->
          let (domain_separator: u8), (prf_inputs: t_Array (t_Array u8 (mk_usize 33)) v_K) =
            temp_0_
          in
          let i:usize = i in
          let prf_inputs:t_Array (t_Array u8 (mk_usize 33)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_inputs
              i
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (prf_inputs.[ i ]
                    <:
                    t_Array u8 (mk_usize 33))
                  (mk_usize 32)
                  (Libcrux_secrets.Traits.f_classify #u8
                      #FStar.Tactics.Typeclasses.solve
                      domain_separator
                    <:
                    u8)
                <:
                t_Array u8 (mk_usize 33))
          in
          let domain_separator:u8 = domain_separator +! mk_u8 1 in
          domain_separator, prf_inputs <: (u8 & t_Array (t_Array u8 (mk_usize 33)) v_K))
  in
  let hax_temp_output:u8 = domain_separator in
  prf_inputs, hax_temp_output <: (t_Array (t_Array u8 (mk_usize 33)) v_K & u8)
