module Libcrux_iot_ml_kem.Vector.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

type t_PortableVector = { f_elements:t_Array i16 (mk_usize 16) }

let impl: Core_models.Clone.t_Clone t_PortableVector =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core_models.Marker.t_Copy t_PortableVector

val zero: Prims.unit -> Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val from_i16_array (array: t_Slice i16) (out: t_PortableVector)
    : Prims.Pure t_PortableVector
      (requires (Core_models.Slice.impl__len #i16 array <: usize) =. mk_usize 16)
      (fun _ -> Prims.l_True)

val to_i16_array (x: t_PortableVector) (out: t_Slice i16)
    : Prims.Pure (t_Slice i16)
      (requires (Core_models.Slice.impl__len #i16 out <: usize) =. mk_usize 16)
      (ensures
        fun out_future ->
          let out_future:t_Slice i16 = out_future in
          (Core_models.Slice.impl__len #i16 out_future <: usize) =. mk_usize 16)
