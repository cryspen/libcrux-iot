module Libcrux_iot_ml_kem.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Traits in
  ()

val ntt_at_layer_1_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (e_initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires zeta_i =. mk_usize 63)
      (fun _ -> Prims.l_True)

val ntt_at_layer_2_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (e_initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires zeta_i =. mk_usize 31)
      (fun _ -> Prims.l_True)

val ntt_at_layer_3_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (e_initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires zeta_i =. mk_usize 15)
      (fun _ -> Prims.l_True)

val ntt_layer_int_vec_step
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (coefficients: t_Array v_Vector (mk_usize 16))
      (a b: usize)
      (scratch: v_Vector)
      (zeta_r: i16)
    : Prims.Pure (t_Array v_Vector (mk_usize 16) & v_Vector)
      (requires a <. mk_usize 16 && b <. mk_usize 16)
      (fun _ -> Prims.l_True)

val ntt_at_layer_4_plus
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (layer: usize)
      (scratch: v_Vector)
      (e_initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)
      (requires
        layer >=. mk_usize 4 && layer <=. mk_usize 7 &&
        zeta_i =. ((mk_usize 1 <<! (mk_usize 7 -! layer <: usize) <: usize) -! mk_usize 1 <: usize))
      (fun _ -> Prims.l_True)

val ntt_at_layer_7_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_binomially_sampled_ring_element
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)
