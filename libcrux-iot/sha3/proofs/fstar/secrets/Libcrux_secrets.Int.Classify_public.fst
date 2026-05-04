module Libcrux_secrets.Int.Classify_public
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Traits in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Libcrux_secrets.Traits.t_Scalar v_T)
    : Libcrux_secrets.Traits.t_ClassifyRef (t_Slice v_T) =
  {
    f_ClassifiedRef = t_Slice v_T;
    f_classify_ref_pre = (fun (self: t_Slice v_T) -> true);
    f_classify_ref_post = (fun (self: t_Slice v_T) (out: t_Slice v_T) -> true);
    f_classify_ref = fun (self: t_Slice v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Libcrux_secrets.Traits.t_Scalar v_T)
    : Libcrux_secrets.Traits.t_DeclassifyRef (t_Slice v_T) =
  {
    f_DeclassifiedRef = t_Slice v_T;
    f_declassify_ref_pre = (fun (self: t_Slice v_T) -> true);
    f_declassify_ref_post = (fun (self: t_Slice v_T) (out: t_Slice v_T) -> true);
    f_declassify_ref = fun (self: t_Slice v_T) -> self
  }
