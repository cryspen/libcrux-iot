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

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Marker.t_Copy t_PortableVector

let impl_1 = impl_1'

let zero (_: Prims.unit) =
  {
    f_elements
    =
    Libcrux_secrets.Traits.f_classify #(t_Array i16 (mk_usize 16))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_i16 0) (mk_usize 16) <: t_Array i16 (mk_usize 16))
  }
  <:
  t_PortableVector

let from_i16_array (array: t_Slice i16) (out: t_PortableVector) =
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Core_models.Slice.impl__copy_from_slice #i16
        out.f_elements
        (array.[ {
              Core_models.Ops.Range.f_start = mk_usize 0;
              Core_models.Ops.Range.f_end = mk_usize 16
            }
            <:
            Core_models.Ops.Range.t_Range usize ]
          <:
          t_Slice i16)
    }
    <:
    t_PortableVector
  in
  out

let to_i16_array (x: t_PortableVector) (out: t_Slice i16) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #i16 out <: usize) >=. mk_usize 16 <: bool)
      in
      ()
  in
  let out:t_Slice i16 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({ Core_models.Ops.Range.f_start = mk_usize 0; Core_models.Ops.Range.f_end = mk_usize 16 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #i16
          (out.[ {
                Core_models.Ops.Range.f_start = mk_usize 0;
                Core_models.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
          (Libcrux_secrets.Traits.f_declassify #(t_Array i16 (mk_usize 16))
              #FStar.Tactics.Typeclasses.solve
              x.f_elements
            <:
            t_Slice i16)
        <:
        t_Slice i16)
  in
  out
