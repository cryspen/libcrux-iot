module Libcrux_iot_ml_kem.Ind_cpa.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Traits in
  ()

/// An unpacked ML-KEM IND-CPA Private Key
type t_IndCpaPrivateKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = { f_secret_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl
      (v_K: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core_models.Default.t_Default (t_IndCpaPrivateKeyUnpacked v_K v_Vector)

/// An unpacked ML-KEM IND-CPA Public Key
type t_IndCpaPublicKeyUnpacked
  (v_K: usize) (v_K_SQUARED: usize) (v_Vector: Type0)
  {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_tt_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K;
  f_seed_for_A:t_Array u8 (mk_usize 32);
  f_A:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K_SQUARED
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1
      (v_K v_K_SQUARED: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core_models.Default.t_Default (t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector)
