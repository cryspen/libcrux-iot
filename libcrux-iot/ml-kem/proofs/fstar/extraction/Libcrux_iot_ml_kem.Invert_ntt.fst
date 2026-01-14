module Libcrux_iot_ml_kem.Invert_ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Traits in
  ()

let invert_ntt_at_layer_1_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ i ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let i:usize = i in
          zeta_i =. (mk_usize 128 -! (i *! mk_usize 4 <: usize) <: usize) <: bool)
      (re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                round
                (Libcrux_iot_ml_kem.Vector.Traits.f_inv_ntt_layer_1_step #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_iot_ml_kem.Polynomial.zeta zeta_i <: i16)
                    (Libcrux_iot_ml_kem.Polynomial.zeta (zeta_i -! mk_usize 1 <: usize) <: i16)
                    (Libcrux_iot_ml_kem.Polynomial.zeta (zeta_i -! mk_usize 2 <: usize) <: i16)
                    (Libcrux_iot_ml_kem.Polynomial.zeta (zeta_i -! mk_usize 3 <: usize) <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i -! mk_usize 3 in
          re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  zeta_i, re <: (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

let invert_ntt_at_layer_2_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ i ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let i:usize = i in
          zeta_i =. (mk_usize 64 -! (i *! mk_usize 2 <: usize) <: usize) <: bool)
      (re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                round
                (Libcrux_iot_ml_kem.Vector.Traits.f_inv_ntt_layer_2_step #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_iot_ml_kem.Polynomial.zeta zeta_i <: i16)
                    (Libcrux_iot_ml_kem.Polynomial.zeta (zeta_i -! mk_usize 1 <: usize) <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  zeta_i, re <: (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

let invert_ntt_at_layer_3_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ i ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let i:usize = i in
          zeta_i =. (mk_usize 32 -! i <: usize) <: bool)
      (re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                round
                (Libcrux_iot_ml_kem.Vector.Traits.f_inv_ntt_layer_3_step #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_iot_ml_kem.Polynomial.zeta zeta_i <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  zeta_i, re <: (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

let inv_ntt_layer_int_vec_step_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (coefficients: t_Array v_Vector (mk_usize 16))
      (a b: usize)
      (scratch: v_Vector)
      (zeta_r: i16)
     =
  let scratch:v_Vector = coefficients.[ a ] in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.f_add #v_Vector
      #FStar.Tactics.Typeclasses.solve
      scratch
      (coefficients.[ b ] <: v_Vector)
  in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
      #FStar.Tactics.Typeclasses.solve
      scratch
  in
  let coefficients:t_Array v_Vector (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize coefficients a scratch
  in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.f_negate #v_Vector #FStar.Tactics.Typeclasses.solve scratch
  in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.f_add #v_Vector
      #FStar.Tactics.Typeclasses.solve
      scratch
      (coefficients.[ b ] <: v_Vector)
  in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.f_add #v_Vector
      #FStar.Tactics.Typeclasses.solve
      scratch
      (coefficients.[ b ] <: v_Vector)
  in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.montgomery_multiply_fe #v_Vector scratch zeta_r
  in
  let coefficients:t_Array v_Vector (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize coefficients b scratch
  in
  coefficients, scratch <: (t_Array v_Vector (mk_usize 16) & v_Vector)

#push-options "--admit_smt_queries true"

let invert_ntt_at_layer_4_plus
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (layer: usize)
      (scratch: v_Vector)
     =
  let step:usize = mk_usize 1 <<! layer in
  let step_vec:usize = step /! Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR in
  let re, scratch, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector &
    usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 128 >>! layer <: usize)
      (fun temp_0_ temp_1_ ->
          let re, scratch, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
            v_Vector &
            usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, scratch, zeta_i
        <:
        (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector & usize))
      (fun temp_0_ round ->
          let re, scratch, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
            v_Vector &
            usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i -! mk_usize 1 in
          let a_offset:usize = (round *! mk_usize 2 <: usize) *! step_vec in
          let b_offset:usize = a_offset +! step_vec in
          let re, scratch:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector
          ) =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              step_vec
              (fun temp_0_ temp_1_ ->
                  let re, scratch:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
                    v_Vector) =
                    temp_0_
                  in
                  let _:usize = temp_1_ in
                  true)
              (re, scratch
                <:
                (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector))
              (fun temp_0_ j ->
                  let re, scratch:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
                    v_Vector) =
                    temp_0_
                  in
                  let j:usize = j in
                  let tmp0, tmp1:(t_Array v_Vector (mk_usize 16) & v_Vector) =
                    inv_ntt_layer_int_vec_step_reduce #v_Vector
                      re.Libcrux_iot_ml_kem.Polynomial.f_coefficients
                      (a_offset +! j <: usize)
                      (b_offset +! j <: usize)
                      scratch
                      (Libcrux_iot_ml_kem.Polynomial.zeta zeta_i <: i16)
                  in
                  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
                    { re with Libcrux_iot_ml_kem.Polynomial.f_coefficients = tmp0 }
                    <:
                    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
                  in
                  let scratch:v_Vector = tmp1 in
                  re, scratch
                  <:
                  (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector))
          in
          re, scratch, zeta_i
          <:
          (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector & usize))
  in
  zeta_i, re, scratch
  <:
  (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)

#pop-options

let invert_ntt_montgomery
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
     =
  let zeta_i:usize = Libcrux_iot_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! mk_usize 2 in
  let tmp0, tmp1:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_1_ #v_Vector zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_2_ #v_Vector zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    invert_ntt_at_layer_3_ #v_Vector zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 4) scratch
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 5) scratch
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 6) scratch
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    invert_ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 7) scratch
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__poly_barrett_reduce #v_Vector re
  in
  re, scratch <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)
