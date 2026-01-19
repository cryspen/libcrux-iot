module Libcrux_iot_ml_kem.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Traits in
  ()

let ntt_at_layer_1_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (e_initial_coefficient_bound: usize)
     =
  let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ i ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let i:usize = i in
          zeta_i =. (mk_usize 63 +! (i *! mk_usize 4 <: usize) <: usize) <: bool)
      (re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! mk_usize 1 in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                round
                (Libcrux_iot_ml_kem.Vector.Traits.f_ntt_layer_1_step #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_iot_ml_kem.Polynomial.zeta zeta_i <: i16)
                    (Libcrux_iot_ml_kem.Polynomial.zeta (zeta_i +! mk_usize 1 <: usize) <: i16)
                    (Libcrux_iot_ml_kem.Polynomial.zeta (zeta_i +! mk_usize 2 <: usize) <: i16)
                    (Libcrux_iot_ml_kem.Polynomial.zeta (zeta_i +! mk_usize 3 <: usize) <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i +! mk_usize 3 in
          re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  zeta_i, re <: (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

let ntt_at_layer_2_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (e_initial_coefficient_bound: usize)
     =
  let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ i ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let i:usize = i in
          zeta_i =. (mk_usize 31 +! (i *! mk_usize 2 <: usize) <: usize) <: bool)
      (re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! mk_usize 1 in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                round
                (Libcrux_iot_ml_kem.Vector.Traits.f_ntt_layer_2_step #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ round ] <: v_Vector)
                    (Libcrux_iot_ml_kem.Polynomial.zeta zeta_i <: i16)
                    (Libcrux_iot_ml_kem.Polynomial.zeta (zeta_i +! mk_usize 1 <: usize) <: i16)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let zeta_i:usize = zeta_i +! mk_usize 1 in
          re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
  in
  zeta_i, re <: (usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

let ntt_at_layer_3_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (e_initial_coefficient_bound: usize)
     =
  let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ i ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let i:usize = i in
          zeta_i =. (mk_usize 15 +! i <: usize) <: bool)
      (re, zeta_i <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! mk_usize 1 in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                round
                (Libcrux_iot_ml_kem.Vector.Traits.f_ntt_layer_3_step #v_Vector
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

let ntt_layer_int_vec_step
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (coefficients: t_Array v_Vector (mk_usize 16))
      (a b: usize)
      (scratch: v_Vector)
      (zeta_r: i16)
     =
  let scratch:v_Vector = coefficients.[ b ] in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.montgomery_multiply_fe #v_Vector scratch zeta_r
  in
  let coefficients:t_Array v_Vector (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize coefficients
      b
      (coefficients.[ a ] <: v_Vector)
  in
  let coefficients:t_Array v_Vector (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize coefficients
      a
      (Libcrux_iot_ml_kem.Vector.Traits.f_add #v_Vector
          #FStar.Tactics.Typeclasses.solve
          (coefficients.[ a ] <: v_Vector)
          scratch
        <:
        v_Vector)
  in
  let coefficients:t_Array v_Vector (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize coefficients
      b
      (Libcrux_iot_ml_kem.Vector.Traits.f_sub #v_Vector
          #FStar.Tactics.Typeclasses.solve
          (coefficients.[ b ] <: v_Vector)
          scratch
        <:
        v_Vector)
  in
  coefficients, scratch <: (t_Array v_Vector (mk_usize 16) & v_Vector)

let ntt_at_layer_4_plus
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (zeta_i: usize)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (layer: usize)
      (scratch: v_Vector)
      (e_initial_coefficient_bound: usize)
     =
  let step:usize = mk_usize 1 <<! layer in
  let step_vec:usize = step /! mk_usize 16 in
  let re, scratch, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector &
    usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 128 >>! layer <: usize)
      (fun temp_0_ round ->
          let re, scratch, zeta_i:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
            v_Vector &
            usize) =
            temp_0_
          in
          let round:usize = round in
          zeta_i =.
          (((mk_usize 1 <<! (mk_usize 7 -! layer <: usize) <: usize) -! mk_usize 1 <: usize) +!
            round
            <:
            usize)
          <:
          bool)
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
          let zeta_i:usize = zeta_i +! mk_usize 1 in
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
                  zeta_i =.
                  ((mk_usize 1 <<! (mk_usize 7 -! layer <: usize) <: usize) +! round <: usize)
                  <:
                  bool)
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
                    ntt_layer_int_vec_step #v_Vector
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
                  let _:Prims.unit = () in
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

let ntt_at_layer_7_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
     =
  let step:usize = Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT /! mk_usize 2 in
  let re, scratch:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      step
      (fun temp_0_ temp_1_ ->
          let re, scratch:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector
          ) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, scratch <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector))
      (fun temp_0_ j ->
          let re, scratch:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector
          ) =
            temp_0_
          in
          let j:usize = j in
          let scratch:v_Vector =
            re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ j +! step <: usize ]
          in
          let scratch:v_Vector =
            Libcrux_iot_ml_kem.Vector.Traits.f_multiply_by_constant #v_Vector
              #FStar.Tactics.Typeclasses.solve
              scratch
              (mk_i16 (-1600))
          in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                (j +! step <: usize)
                (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ j ] <: v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                j
                (Libcrux_iot_ml_kem.Vector.Traits.f_add #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ j ] <: v_Vector)
                    scratch
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                (j +! step <: usize)
                (Libcrux_iot_ml_kem.Vector.Traits.f_sub #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ j +! step <: usize ]
                      <:
                      v_Vector)
                    scratch
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re, scratch <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)
      )
  in
  re, scratch <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)

let ntt_binomially_sampled_ring_element
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
     =
  let tmp0, tmp1:(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector) =
    ntt_at_layer_7_ #v_Vector re scratch
  in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  let zeta_i:usize = mk_usize 1 in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 6) scratch (mk_usize 11207)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    ntt_at_layer_4_plus #v_Vector
      zeta_i
      re
      (mk_usize 5)
      scratch
      (mk_usize 11207 +! mk_usize 3328 <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    ntt_at_layer_4_plus #v_Vector
      zeta_i
      re
      (mk_usize 4)
      scratch
      (mk_usize 11207 +! (mk_usize 2 *! mk_usize 3328 <: usize) <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    ntt_at_layer_3_ #v_Vector
      zeta_i
      re
      (mk_usize 11207 +! (mk_usize 3 *! mk_usize 3328 <: usize) <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    ntt_at_layer_2_ #v_Vector
      zeta_i
      re
      (mk_usize 11207 +! (mk_usize 4 *! mk_usize 3328 <: usize) <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    ntt_at_layer_1_ #v_Vector
      zeta_i
      re
      (mk_usize 11207 +! (mk_usize 5 *! mk_usize 3328 <: usize) <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__poly_barrett_reduce #v_Vector re
  in
  re, scratch <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)

let ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
     =
  let zeta_i:usize = mk_usize 0 in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    ntt_at_layer_4_plus #v_Vector zeta_i re (mk_usize 7) scratch (mk_usize 3328)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    ntt_at_layer_4_plus #v_Vector
      zeta_i
      re
      (mk_usize 6)
      scratch
      (mk_usize 2 *! mk_usize 3328 <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    ntt_at_layer_4_plus #v_Vector
      zeta_i
      re
      (mk_usize 5)
      scratch
      (mk_usize 3 *! mk_usize 3328 <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1, tmp2:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector) =
    ntt_at_layer_4_plus #v_Vector
      zeta_i
      re
      (mk_usize 4)
      scratch
      (mk_usize 4 *! mk_usize 3328 <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    ntt_at_layer_3_ #v_Vector zeta_i re (mk_usize 5 *! mk_usize 3328 <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    ntt_at_layer_2_ #v_Vector zeta_i re (mk_usize 6 *! mk_usize 3328 <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    ntt_at_layer_1_ #v_Vector zeta_i re (mk_usize 7 *! mk_usize 3328 <: usize)
  in
  let zeta_i:usize = tmp0 in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let _:Prims.unit = () in
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__poly_barrett_reduce #v_Vector re
  in
  re, scratch <: (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector)
