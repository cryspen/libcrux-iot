module Libcrux_iot_ml_kem.Vector.Portable.Compress
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

let compress_message_coefficient (fe: u16) =
  let shifted:i16 =
    Core.Num.impl_i16__wrapping_sub (Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (mk_i16 1664)
        <:
        i16)
      (Libcrux_secrets.Int.f_as_i16 #u16 #FStar.Tactics.Typeclasses.solve fe <: i16)
  in
  let mask:i16 = shifted >>! mk_i32 15 in
  let shifted_to_positive:i16 = mask ^. shifted in
  let shifted_positive_in_range:i16 =
    Core.Num.impl_i16__wrapping_sub shifted_to_positive (mk_i16 832)
  in
  let r0:i16 = shifted_positive_in_range >>! mk_i32 15 in
  let r1:i16 = r0 &. mk_i16 1 in
  Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve r1

let compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16) =
  let compressed:u64 =
    (Libcrux_secrets.Int.f_as_u64 #u16 #FStar.Tactics.Typeclasses.solve fe <: u64) <<!
    coefficient_bits
  in
  let compressed:u64 = Core.Num.impl_u64__wrapping_add compressed (mk_u64 1664) in
  let compressed:u64 = Core.Num.impl_u64__wrapping_mul compressed (mk_u64 10321340) in
  let compressed:u64 = compressed >>! mk_i32 35 in
  Libcrux_secrets.Int.f_as_i16 #u32
    #FStar.Tactics.Typeclasses.solve
    (Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.get_n_least_significant_bits coefficient_bits
        (Libcrux_secrets.Int.f_as_u32 #u64 #FStar.Tactics.Typeclasses.solve compressed <: u32)
      <:
      u32)

let compress_1_ (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun a temp_1_ ->
          let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let _:usize = temp_1_ in
          true)
      a
      (fun a i ->
          let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let i:usize = i in
          {
            a with
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a
                .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (Libcrux_secrets.Int.f_as_i16 #u8
                  #FStar.Tactics.Typeclasses.solve
                  (compress_message_coefficient (Libcrux_secrets.Int.f_as_u16 #i16
                          #FStar.Tactics.Typeclasses.solve
                          (a.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                        <:
                        u16)
                    <:
                    u8)
                <:
                i16)
            <:
            t_Array i16 (mk_usize 16)
          }
          <:
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  a

let compress
      (v_COEFFICIENT_BITS: i32)
      (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun a temp_1_ ->
          let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let _:usize = temp_1_ in
          true)
      a
      (fun a i ->
          let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let i:usize = i in
          {
            a with
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a
                .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (Libcrux_secrets.Int.f_as_i16 #i16
                  #FStar.Tactics.Typeclasses.solve
                  (compress_ciphertext_coefficient (cast (v_COEFFICIENT_BITS <: i32) <: u8)
                      (Libcrux_secrets.Int.f_as_u16 #i16
                          #FStar.Tactics.Typeclasses.solve
                          (a.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                        <:
                        u16)
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
  a

let decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun a temp_1_ ->
          let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let _:usize = temp_1_ in
          true)
      a
      (fun a i ->
          let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let i:usize = i in
          let decompressed:i32 =
            Core.Num.impl_i32__wrapping_mul (Libcrux_secrets.Int.f_as_i32 #i16
                  #FStar.Tactics.Typeclasses.solve
                  (a.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
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
          let decompressed:i32 =
            Core.Num.impl_i32__wrapping_add (decompressed <<! mk_i32 1 <: i32)
              (mk_i32 1 <<! v_COEFFICIENT_BITS <: i32)
          in
          let decompressed:i32 = decompressed >>! (v_COEFFICIENT_BITS +! mk_i32 1 <: i32) in
          let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              a with
              Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a
                  .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                (Libcrux_secrets.Int.f_as_i16 #i32 #FStar.Tactics.Typeclasses.solve decompressed
                  <:
                  i16)
            }
            <:
            Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          a)
  in
  a
