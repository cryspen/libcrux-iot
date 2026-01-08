module Libcrux_iot_ml_kem.Vector.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

let ntt_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
     =
  let t:i16 =
    Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (vec
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ]
        <:
        i16)
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta <: i16)
  in
  let a_minus_t:i16 =
    Core.Num.impl_i16__wrapping_sub (vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[
          i ]
        <:
        i16)
      t
  in
  let a_plus_t:i16 =
    Core.Num.impl_i16__wrapping_add (vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[
          i ]
        <:
        i16)
      t
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      vec with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        j
        a_minus_t
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      vec with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        i
        a_plus_t
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  vec

let ntt_layer_1_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (mk_usize 0) (mk_usize 2)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (mk_usize 1) (mk_usize 3)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (mk_usize 4) (mk_usize 6)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (mk_usize 5) (mk_usize 7)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta2 (mk_usize 8) (mk_usize 10)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta2 (mk_usize 9) (mk_usize 11)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta3 (mk_usize 12) (mk_usize 14)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta3 (mk_usize 13) (mk_usize 15)
  in
  vec

let ntt_layer_2_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
     =
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (mk_usize 0) (mk_usize 4)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (mk_usize 1) (mk_usize 5)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (mk_usize 2) (mk_usize 6)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (mk_usize 3) (mk_usize 7)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (mk_usize 8) (mk_usize 12)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (mk_usize 9) (mk_usize 13)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (mk_usize 10) (mk_usize 14)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (mk_usize 11) (mk_usize 15)
  in
  vec

let ntt_layer_3_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
     =
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (mk_usize 0) (mk_usize 8)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (mk_usize 1) (mk_usize 9)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (mk_usize 2) (mk_usize 10)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (mk_usize 3) (mk_usize 11)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (mk_usize 4) (mk_usize 12)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (mk_usize 5) (mk_usize 13)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (mk_usize 6) (mk_usize 14)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (mk_usize 7) (mk_usize 15)
  in
  vec

let inv_ntt_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
     =
  let a_minus_b:i16 =
    Core.Num.impl_i16__wrapping_sub (vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[
          j ]
        <:
        i16)
      (vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
  in
  let a_plus_b:i16 =
    Core.Num.impl_i16__wrapping_add (vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[
          j ]
        <:
        i16)
      (vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
  in
  let o0:i16 = Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element a_plus_b in
  let o1:i16 =
    Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta <: i16)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      vec with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        i
        o0
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      vec with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        j
        o1
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  vec

let inv_ntt_layer_1_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (mk_usize 0) (mk_usize 2)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (mk_usize 1) (mk_usize 3)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (mk_usize 4) (mk_usize 6)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (mk_usize 5) (mk_usize 7)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta2 (mk_usize 8) (mk_usize 10)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta2 (mk_usize 9) (mk_usize 11)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta3 (mk_usize 12) (mk_usize 14)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta3 (mk_usize 13) (mk_usize 15)
  in
  vec

let inv_ntt_layer_2_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
     =
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (mk_usize 0) (mk_usize 4)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (mk_usize 1) (mk_usize 5)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (mk_usize 2) (mk_usize 6)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (mk_usize 3) (mk_usize 7)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (mk_usize 8) (mk_usize 12)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (mk_usize 9) (mk_usize 13)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (mk_usize 10) (mk_usize 14)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (mk_usize 11) (mk_usize 15)
  in
  vec

let inv_ntt_layer_3_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
     =
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (mk_usize 0) (mk_usize 8)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (mk_usize 1) (mk_usize 9)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (mk_usize 2) (mk_usize 10)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (mk_usize 3) (mk_usize 11)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (mk_usize 4) (mk_usize 12)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (mk_usize 5) (mk_usize 13)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (mk_usize 6) (mk_usize 14)
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (mk_usize 7) (mk_usize 15)
  in
  vec

let accumulating_ntt_multiply_binomials_fill_cache
      (a b: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i: usize)
      (out: t_Slice i32)
      (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let ai:i16 =
    a.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 2 *! i <: usize ]
  in
  let bi:i16 =
    b.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 2 *! i <: usize ]
  in
  let aj:i16 =
    a.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ (mk_usize 2 *! i <: usize) +!
      mk_usize 1
      <:
      usize ]
  in
  let bj:i16 =
    b.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ (mk_usize 2 *! i <: usize) +!
      mk_usize 1
      <:
      usize ]
  in
  let ai_bi:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          ai
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bi <: i32)
  in
  let bj_zeta_:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          bj
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve zeta <: i32)
  in
  let bj_zeta:i16 =
    Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element bj_zeta_
  in
  let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      cache with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize cache
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        i
        bj_zeta
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let aj_bj_zeta:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          aj
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bj_zeta <: i32)
  in
  let ai_bi_aj_bj:i32 = Core.Num.impl_i32__wrapping_add ai_bi aj_bj_zeta in
  let o0:i32 = ai_bi_aj_bj in
  let ai_bj:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          ai
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bj <: i32)
  in
  let aj_bi:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          aj
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bi <: i32)
  in
  let ai_bj_aj_bi:i32 = Core.Num.impl_i32__wrapping_add ai_bj aj_bi in
  let o1:i32 = ai_bj_aj_bi in
  let out:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (mk_usize 2 *! i <: usize)
      (Core.Num.impl_i32__wrapping_add (out.[ mk_usize 2 *! i <: usize ] <: i32) o0 <: i32)
  in
  let out:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      ((mk_usize 2 *! i <: usize) +! mk_usize 1 <: usize)
      (Core.Num.impl_i32__wrapping_add (out.[ (mk_usize 2 *! i <: usize) +! mk_usize 1 <: usize ]
            <:
            i32)
          o1
        <:
        i32)
  in
  out, cache <: (t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)

let accumulating_ntt_multiply_binomials_use_cache
      (a b: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (i: usize)
      (out: t_Slice i32)
      (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let ai:i16 =
    a.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 2 *! i <: usize ]
  in
  let bi:i16 =
    b.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 2 *! i <: usize ]
  in
  let aj:i16 =
    a.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ (mk_usize 2 *! i <: usize) +!
      mk_usize 1
      <:
      usize ]
  in
  let bj:i16 =
    b.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ (mk_usize 2 *! i <: usize) +!
      mk_usize 1
      <:
      usize ]
  in
  let ai_bi:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          ai
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bi <: i32)
  in
  let aj_bj_zeta:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          aj
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          (cache.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
        <:
        i32)
  in
  let ai_bi_aj_bj:i32 = Core.Num.impl_i32__wrapping_add ai_bi aj_bj_zeta in
  let o0:i32 = ai_bi_aj_bj in
  let ai_bj:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          ai
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bj <: i32)
  in
  let aj_bi:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          aj
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bi <: i32)
  in
  let ai_bj_aj_bi:i32 = Core.Num.impl_i32__wrapping_add ai_bj aj_bi in
  let o1:i32 = ai_bj_aj_bi in
  let out:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (mk_usize 2 *! i <: usize)
      (Core.Num.impl_i32__wrapping_add (out.[ mk_usize 2 *! i <: usize ] <: i32) o0 <: i32)
  in
  let out:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      ((mk_usize 2 *! i <: usize) +! mk_usize 1 <: usize)
      (Core.Num.impl_i32__wrapping_add (out.[ (mk_usize 2 *! i <: usize) +! mk_usize 1 <: usize ]
            <:
            i32)
          o1
        <:
        i32)
  in
  out

let accumulating_ntt_multiply_binomials
      (a b: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i: usize)
      (out: t_Slice i32)
     =
  let ai:i16 =
    a.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 2 *! i <: usize ]
  in
  let bi:i16 =
    b.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 2 *! i <: usize ]
  in
  let aj:i16 =
    a.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ (mk_usize 2 *! i <: usize) +!
      mk_usize 1
      <:
      usize ]
  in
  let bj:i16 =
    b.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ (mk_usize 2 *! i <: usize) +!
      mk_usize 1
      <:
      usize ]
  in
  let ai_bi:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          ai
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bi <: i32)
  in
  let bj_zeta_:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          bj
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve zeta <: i32)
  in
  let bj_zeta:i16 =
    Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element bj_zeta_
  in
  let aj_bj_zeta:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          aj
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bj_zeta <: i32)
  in
  let ai_bi_aj_bj:i32 = Core.Num.impl_i32__wrapping_add ai_bi aj_bj_zeta in
  let o0:i32 = ai_bi_aj_bj in
  let ai_bj:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          ai
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bj <: i32)
  in
  let aj_bi:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          aj
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve bi <: i32)
  in
  let ai_bj_aj_bi:i32 = Core.Num.impl_i32__wrapping_add ai_bj aj_bi in
  let o1:i32 = ai_bj_aj_bi in
  let out:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (mk_usize 2 *! i <: usize)
      (Core.Num.impl_i32__wrapping_add (out.[ mk_usize 2 *! i <: usize ] <: i32) o0 <: i32)
  in
  let out:t_Slice i32 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      ((mk_usize 2 *! i <: usize) +! mk_usize 1 <: usize)
      (Core.Num.impl_i32__wrapping_add (out.[ (mk_usize 2 *! i <: usize) +! mk_usize 1 <: usize ]
            <:
            i32)
          o1
        <:
        i32)
  in
  out

let accumulating_ntt_multiply
      (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice i32)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let nzeta0:i16 = Core.Num.impl_i16__wrapping_neg zeta0 in
  let nzeta1:i16 = Core.Num.impl_i16__wrapping_neg zeta1 in
  let nzeta2:i16 = Core.Num.impl_i16__wrapping_neg zeta2 in
  let nzeta3:i16 = Core.Num.impl_i16__wrapping_neg zeta3 in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta0 <: i16)
      (mk_usize 0)
      out
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve nzeta0 <: i16)
      (mk_usize 1)
      out
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta1 <: i16)
      (mk_usize 2)
      out
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve nzeta1 <: i16)
      (mk_usize 3)
      out
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta2 <: i16)
      (mk_usize 4)
      out
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve nzeta2 <: i16)
      (mk_usize 5)
      out
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta3 <: i16)
      (mk_usize 6)
      out
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve nzeta3 <: i16)
      (mk_usize 7)
      out
  in
  out

let accumulating_ntt_multiply_fill_cache
      (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice i32)
      (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let nzeta0:i16 = Core.Num.impl_i16__wrapping_neg zeta0 in
  let nzeta1:i16 = Core.Num.impl_i16__wrapping_neg zeta1 in
  let nzeta2:i16 = Core.Num.impl_i16__wrapping_neg zeta2 in
  let nzeta3:i16 = Core.Num.impl_i16__wrapping_neg zeta3 in
  let tmp0, tmp1:(t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    accumulating_ntt_multiply_binomials_fill_cache lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta0 <: i16)
      (mk_usize 0)
      out
      cache
  in
  let out:t_Slice i32 = tmp0 in
  let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    accumulating_ntt_multiply_binomials_fill_cache lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve nzeta0 <: i16)
      (mk_usize 1)
      out
      cache
  in
  let out:t_Slice i32 = tmp0 in
  let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    accumulating_ntt_multiply_binomials_fill_cache lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta1 <: i16)
      (mk_usize 2)
      out
      cache
  in
  let out:t_Slice i32 = tmp0 in
  let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    accumulating_ntt_multiply_binomials_fill_cache lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve nzeta1 <: i16)
      (mk_usize 3)
      out
      cache
  in
  let out:t_Slice i32 = tmp0 in
  let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    accumulating_ntt_multiply_binomials_fill_cache lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta2 <: i16)
      (mk_usize 4)
      out
      cache
  in
  let out:t_Slice i32 = tmp0 in
  let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    accumulating_ntt_multiply_binomials_fill_cache lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve nzeta2 <: i16)
      (mk_usize 5)
      out
      cache
  in
  let out:t_Slice i32 = tmp0 in
  let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    accumulating_ntt_multiply_binomials_fill_cache lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve zeta3 <: i16)
      (mk_usize 6)
      out
      cache
  in
  let out:t_Slice i32 = tmp0 in
  let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    accumulating_ntt_multiply_binomials_fill_cache lhs
      rhs
      (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve nzeta3 <: i16)
      (mk_usize 7)
      out
      cache
  in
  let out:t_Slice i32 = tmp0 in
  let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = tmp1 in
  let _:Prims.unit = () in
  out, cache <: (t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)

let accumulating_ntt_multiply_use_cache
      (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice i32)
      (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials_use_cache lhs rhs (mk_usize 0) out cache
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials_use_cache lhs rhs (mk_usize 1) out cache
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials_use_cache lhs rhs (mk_usize 2) out cache
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials_use_cache lhs rhs (mk_usize 3) out cache
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials_use_cache lhs rhs (mk_usize 4) out cache
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials_use_cache lhs rhs (mk_usize 5) out cache
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials_use_cache lhs rhs (mk_usize 6) out cache
  in
  let out:t_Slice i32 =
    accumulating_ntt_multiply_binomials_use_cache lhs rhs (mk_usize 7) out cache
  in
  out
