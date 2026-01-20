module Libcrux_iot_ml_kem.Vector.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Portable.Vector_type in
  let open Libcrux_iot_ml_kem.Vector.Traits in
  let open Libcrux_secrets.Int.Classify_public in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_iot_ml_kem.Vector.Traits.t_Repr
Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Libcrux_iot_ml_kem.Vector.Traits.t_Operations
Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
