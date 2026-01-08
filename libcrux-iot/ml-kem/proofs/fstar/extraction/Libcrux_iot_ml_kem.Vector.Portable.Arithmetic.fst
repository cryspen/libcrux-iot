module Libcrux_iot_ml_kem.Vector.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Portable.Vector_type in
  let open Libcrux_secrets.Int in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

let get_n_least_significant_bits (n: u8) (value: u32) =
  value &. (Core.Num.impl_u32__wrapping_sub (mk_u32 1 <<! n <: u32) (mk_u32 1) <: u32)

let add (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let e_lhs0:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      lhs
  in
  let lhs:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun lhs temp_1_ ->
          let lhs:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (Core.Num.impl_i16__wrapping_add (lhs
                      .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                    <:
                    i16)
                  (rhs.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                <:
                i16)
            <:
            t_Array i16 (mk_usize 16)
          }
          <:
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  lhs

let sub (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let e_lhs0:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      lhs
  in
  let lhs:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun lhs temp_1_ ->
          let lhs:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (Core.Num.impl_i16__wrapping_sub (lhs
                      .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                    <:
                    i16)
                  (rhs.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                <:
                i16)
            <:
            t_Array i16 (mk_usize 16)
          }
          <:
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  lhs

let negate (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let e_vec0:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      vec
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec temp_1_ ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let _:usize = temp_1_ in
          true)
      vec
      (fun vec i ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          {
            vec with
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (Core.Num.impl_i16__wrapping_neg (vec
                      .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                    <:
                    i16)
                <:
                i16)
            <:
            t_Array i16 (mk_usize 16)
          }
          <:
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  vec

let multiply_by_constant
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
     =
  let e_vec0:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      vec
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec temp_1_ ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let _:usize = temp_1_ in
          true)
      vec
      (fun vec i ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          {
            vec with
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (Core.Num.impl_i16__wrapping_mul (vec
                      .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                    <:
                    i16)
                  c
                <:
                i16)
            <:
            t_Array i16 (mk_usize 16)
          }
          <:
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  vec

let bitwise_and_with_constant
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
     =
  let e_vec0:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      vec
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec temp_1_ ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let _:usize = temp_1_ in
          true)
      vec
      (fun vec i ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          {
            vec with
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              ((vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) &. c
                <:
                i16)
            <:
            t_Array i16 (mk_usize 16)
          }
          <:
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  vec

let shift_right
      (v_SHIFT_BY: i32)
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let e_vec0:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      vec
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec temp_1_ ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let _:usize = temp_1_ in
          true)
      vec
      (fun vec i ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          {
            vec with
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              ((vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) >>!
                (cast (v_SHIFT_BY <: i32) <: u32)
                <:
                i16)
            <:
            t_Array i16 (mk_usize 16)
          }
          <:
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  vec

let cond_subtract_3329_ (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let e_vec0:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      vec
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec temp_1_ ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let _:usize = temp_1_ in
          true)
      vec
      (fun vec i ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          if
            (Libcrux_secrets.Traits.f_declassify #i16
                #FStar.Tactics.Typeclasses.solve
                (vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
              <:
              i16) >=.
            mk_i16 3329
            <:
            bool
          then
            let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
              {
                vec with
                Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
                =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                    .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
                  i
                  (Core.Num.impl_i16__wrapping_sub (vec
                          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                        <:
                        i16)
                      (mk_i16 3329)
                    <:
                    i16)
              }
              <:
              Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
            in
            vec
          else vec)
  in
  vec

let barrett_reduce_element (value: i16) =
  let t:i32 =
    Core.Num.impl_i32__wrapping_add (Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
              #FStar.Tactics.Typeclasses.solve
              value
            <:
            i32)
          v_BARRETT_MULTIPLIER
        <:
        i32)
      (Libcrux_iot_ml_kem.Vector.Traits.v_BARRETT_R >>! mk_i32 1 <: i32)
  in
  let quotient:i16 =
    Libcrux_secrets.Int.f_as_i16 #i32
      #FStar.Tactics.Typeclasses.solve
      (t >>! (cast (Libcrux_iot_ml_kem.Vector.Traits.v_BARRETT_SHIFT <: i32) <: u32) <: i32)
  in
  Core.Num.impl_i16__wrapping_sub value
    (Core.Num.impl_i16__wrapping_mul quotient Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_MODULUS
      <:
      i16)

let barrett_reduce (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let e_vec0:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      vec
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec temp_1_ ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let _:usize = temp_1_ in
          true)
      vec
      (fun vec i ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          let vi:i16 =
            barrett_reduce_element (vec.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i
                ]
                <:
                i16)
          in
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              vec with
              Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                  .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                vi
            }
            <:
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          vec)
  in
  vec

let montgomery_reduce_element (value: i32) =
  let k:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Int.f_as_i16 #i32 #FStar.Tactics.Typeclasses.solve value <: i16)
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #u32
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_classify #u32
              #FStar.Tactics.Typeclasses.solve
              Libcrux_iot_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
            <:
            u32)
        <:
        i32)
  in
  let k_times_modulus:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Int.f_as_i16 #i32 #FStar.Tactics.Typeclasses.solve k <: i16)
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_classify #i16
              #FStar.Tactics.Typeclasses.solve
              Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_MODULUS
            <:
            i16)
        <:
        i32)
  in
  let c:i16 =
    Libcrux_secrets.Int.f_as_i16 #i32
      #FStar.Tactics.Typeclasses.solve
      (k_times_modulus >>! (cast (v_MONTGOMERY_SHIFT <: u8) <: u32) <: i32)
  in
  let value_high:i16 =
    Libcrux_secrets.Int.f_as_i16 #i32
      #FStar.Tactics.Typeclasses.solve
      (value >>! (cast (v_MONTGOMERY_SHIFT <: u8) <: u32) <: i32)
  in
  Core.Num.impl_i16__wrapping_sub value_high c

let montgomery_multiply_fe_by_fer (fe fer: i16) =
  let product:i32 =
    Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
          #FStar.Tactics.Typeclasses.solve
          fe
        <:
        i32)
      (Libcrux_secrets.Int.f_as_i32 #i16 #FStar.Tactics.Typeclasses.solve fer <: i32)
  in
  montgomery_reduce_element product

let montgomery_multiply_by_constant
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
     =
  let e_vec0:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      vec
  in
  let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec temp_1_ ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let _:usize = temp_1_ in
          true)
      vec
      (fun vec i ->
          let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          {
            vec with
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (montgomery_multiply_fe_by_fer (vec
                      .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                    <:
                    i16)
                  c
                <:
                i16)
            <:
            t_Array i16 (mk_usize 16)
          }
          <:
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  vec
