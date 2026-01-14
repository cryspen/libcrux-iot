module Libcrux_iot_ml_kem.Invert_ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Traits in
  ()

val invert_ntt_at_layer_1_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires zeta_i =. mk_usize 128)
      (ensures
        fun temp_0_ ->
          let zeta_i_future, re_future:(usize &
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          zeta_i_future =. mk_usize 64)

val invert_ntt_at_layer_2_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires zeta_i =. mk_usize 64)
      (ensures
        fun temp_0_ ->
          let zeta_i_future, re_future:(usize &
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          zeta_i_future =. mk_usize 32)

val invert_ntt_at_layer_3_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires zeta_i =. mk_usize 32)
      (ensures
        fun temp_0_ ->
          let zeta_i_future, re_future:(usize &
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          zeta_i_future =. mk_usize 16)

val inv_ntt_layer_int_vec_step_reduce
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (coefficients: t_Array v_Vector (mk_usize 16))
      (a b: usize)
      (scratch: v_Vector)
      (zeta_r: i16)
    : Prims.Pure (t_Array v_Vector (mk_usize 16) & v_Vector)
      (requires a <. mk_usize 16 && b <. mk_usize 16)
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_4_plus
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (layer: usize)
      (scratch: v_Vector)
    : Prims.Pure (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)
      (requires layer >=. mk_usize 4 && layer <=. mk_usize 7)
      (fun _ -> Prims.l_True)

val invert_ntt_montgomery
      (v_K: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)
