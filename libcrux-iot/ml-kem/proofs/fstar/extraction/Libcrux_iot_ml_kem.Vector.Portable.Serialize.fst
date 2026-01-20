module Libcrux_iot_ml_kem.Vector.Portable.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

let serialize_1_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 2 <: bool)
      in
      ()
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (mk_usize 0)
      ((((((((Libcrux_secrets.Int.f_as_u8 #i16
                        #FStar.Tactics.Typeclasses.solve
                        (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 0 ]
                          <:
                          i16)
                      <:
                      u8) |.
                    ((Libcrux_secrets.Int.f_as_u8 #i16
                          #FStar.Tactics.Typeclasses.solve
                          (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 1
                            ]
                            <:
                            i16)
                        <:
                        u8) <<!
                      mk_i32 1
                      <:
                      u8)
                    <:
                    u8) |.
                  ((Libcrux_secrets.Int.f_as_u8 #i16
                        #FStar.Tactics.Typeclasses.solve
                        (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 2 ]
                          <:
                          i16)
                      <:
                      u8) <<!
                    mk_i32 2
                    <:
                    u8)
                  <:
                  u8) |.
                ((Libcrux_secrets.Int.f_as_u8 #i16
                      #FStar.Tactics.Typeclasses.solve
                      (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 3 ]
                        <:
                        i16)
                    <:
                    u8) <<!
                  mk_i32 3
                  <:
                  u8)
                <:
                u8) |.
              ((Libcrux_secrets.Int.f_as_u8 #i16
                    #FStar.Tactics.Typeclasses.solve
                    (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 4 ]
                      <:
                      i16)
                  <:
                  u8) <<!
                mk_i32 4
                <:
                u8)
              <:
              u8) |.
            ((Libcrux_secrets.Int.f_as_u8 #i16
                  #FStar.Tactics.Typeclasses.solve
                  (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 5 ] <: i16
                  )
                <:
                u8) <<!
              mk_i32 5
              <:
              u8)
            <:
            u8) |.
          ((Libcrux_secrets.Int.f_as_u8 #i16
                #FStar.Tactics.Typeclasses.solve
                (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 6 ] <: i16)
              <:
              u8) <<!
            mk_i32 6
            <:
            u8)
          <:
          u8) |.
        ((Libcrux_secrets.Int.f_as_u8 #i16
              #FStar.Tactics.Typeclasses.solve
              (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 7 ] <: i16)
            <:
            u8) <<!
          mk_i32 7
          <:
          u8)
        <:
        u8)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (mk_usize 1)
      ((((((((Libcrux_secrets.Int.f_as_u8 #i16
                        #FStar.Tactics.Typeclasses.solve
                        (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 8 ]
                          <:
                          i16)
                      <:
                      u8) |.
                    ((Libcrux_secrets.Int.f_as_u8 #i16
                          #FStar.Tactics.Typeclasses.solve
                          (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 9
                            ]
                            <:
                            i16)
                        <:
                        u8) <<!
                      mk_i32 1
                      <:
                      u8)
                    <:
                    u8) |.
                  ((Libcrux_secrets.Int.f_as_u8 #i16
                        #FStar.Tactics.Typeclasses.solve
                        (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 10 ]
                          <:
                          i16)
                      <:
                      u8) <<!
                    mk_i32 2
                    <:
                    u8)
                  <:
                  u8) |.
                ((Libcrux_secrets.Int.f_as_u8 #i16
                      #FStar.Tactics.Typeclasses.solve
                      (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 11 ]
                        <:
                        i16)
                    <:
                    u8) <<!
                  mk_i32 3
                  <:
                  u8)
                <:
                u8) |.
              ((Libcrux_secrets.Int.f_as_u8 #i16
                    #FStar.Tactics.Typeclasses.solve
                    (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 12 ]
                      <:
                      i16)
                  <:
                  u8) <<!
                mk_i32 4
                <:
                u8)
              <:
              u8) |.
            ((Libcrux_secrets.Int.f_as_u8 #i16
                  #FStar.Tactics.Typeclasses.solve
                  (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 13 ]
                    <:
                    i16)
                <:
                u8) <<!
              mk_i32 5
              <:
              u8)
            <:
            u8) |.
          ((Libcrux_secrets.Int.f_as_u8 #i16
                #FStar.Tactics.Typeclasses.solve
                (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 14 ] <: i16)
              <:
              u8) <<!
            mk_i32 6
            <:
            u8)
          <:
          u8) |.
        ((Libcrux_secrets.Int.f_as_u8 #i16
              #FStar.Tactics.Typeclasses.solve
              (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ mk_usize 15 ] <: i16)
            <:
            u8) <<!
          mk_i32 7
          <:
          u8)
        <:
        u8)
  in
  out

let deserialize_1_
      (v: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 0)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            ((v.[ mk_usize 0 ] <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 1)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 0 ] <: u8) >>! mk_i32 1 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 2)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 0 ] <: u8) >>! mk_i32 2 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 3)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 0 ] <: u8) >>! mk_i32 3 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 4)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 0 ] <: u8) >>! mk_i32 4 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 5)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 0 ] <: u8) >>! mk_i32 5 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 6)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 0 ] <: u8) >>! mk_i32 6 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 7)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 0 ] <: u8) >>! mk_i32 7 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 8)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            ((v.[ mk_usize 1 ] <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 9)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 1 ] <: u8) >>! mk_i32 1 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 10)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 1 ] <: u8) >>! mk_i32 2 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 11)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 1 ] <: u8) >>! mk_i32 3 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 12)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 1 ] <: u8) >>! mk_i32 4 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 13)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 1 ] <: u8) >>! mk_i32 5 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 14)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 1 ] <: u8) >>! mk_i32 6 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 15)
        (Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (((v.[ mk_usize 1 ] <: u8) >>! mk_i32 7 <: u8) &. mk_u8 1 <: u8)
          <:
          i16)
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  out

let serialize_4_int (v: t_Slice i16) =
  let result0:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve (v.[ mk_usize 1 ] <: i16)
        <:
        u8) <<!
      mk_i32 4
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve (v.[ mk_usize 0 ] <: i16)
      <:
      u8)
  in
  let result1:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve (v.[ mk_usize 3 ] <: i16)
        <:
        u8) <<!
      mk_i32 4
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve (v.[ mk_usize 2 ] <: i16)
      <:
      u8)
  in
  let result2:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve (v.[ mk_usize 5 ] <: i16)
        <:
        u8) <<!
      mk_i32 4
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve (v.[ mk_usize 4 ] <: i16)
      <:
      u8)
  in
  let result3:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve (v.[ mk_usize 7 ] <: i16)
        <:
        u8) <<!
      mk_i32 4
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve (v.[ mk_usize 6 ] <: i16)
      <:
      u8)
  in
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve result0,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve result1,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve result2,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve result3
  <:
  (u8 & u8 & u8 & u8)

let serialize_4_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 8 <: bool)
      in
      ()
  in
  let (lhs: u8), (lhs_1_: u8), (lhs_2_: u8), (lhs_3_: u8) =
    serialize_4_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 8
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 0) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 1) lhs_1_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 2) lhs_2_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 3) lhs_3_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_4_: u8), (lhs_5_: u8), (lhs_6_: u8) =
    serialize_4_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 8;
            Core_models.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 4) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 5) lhs_4_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 6) lhs_5_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 7) lhs_6_
  in
  let _:Prims.unit = () in
  out

let deserialize_4_int (bytes: t_Slice u8) =
  let v0:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((bytes.[ mk_usize 0 ] <: u8) &. mk_u8 15 <: u8)
  in
  let v1:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      (((bytes.[ mk_usize 0 ] <: u8) >>! mk_i32 4 <: u8) &. mk_u8 15 <: u8)
  in
  let v2:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((bytes.[ mk_usize 1 ] <: u8) &. mk_u8 15 <: u8)
  in
  let v3:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      (((bytes.[ mk_usize 1 ] <: u8) >>! mk_i32 4 <: u8) &. mk_u8 15 <: u8)
  in
  let v4:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((bytes.[ mk_usize 2 ] <: u8) &. mk_u8 15 <: u8)
  in
  let v5:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      (((bytes.[ mk_usize 2 ] <: u8) >>! mk_i32 4 <: u8) &. mk_u8 15 <: u8)
  in
  let v6:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((bytes.[ mk_usize 3 ] <: u8) &. mk_u8 15 <: u8)
  in
  let v7:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      (((bytes.[ mk_usize 3 ] <: u8) >>! mk_i32 4 <: u8) &. mk_u8 15 <: u8)
  in
  v0, v1, v2, v3, v4, v5, v6, v7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

let deserialize_4_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let
  (lhs: i16),
  (lhs_1_: i16),
  (lhs_2_: i16),
  (lhs_3_: i16),
  (lhs_4_: i16),
  (lhs_5_: i16),
  (lhs_6_: i16),
  (lhs_7_: i16) =
    deserialize_4_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 4
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 0)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 1)
        lhs_1_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 2)
        lhs_2_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 3)
        lhs_3_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 4)
        lhs_4_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 5)
        lhs_5_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 6)
        lhs_6_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 7)
        lhs_7_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let
  (lhs: i16),
  (lhs_8_: i16),
  (lhs_9_: i16),
  (lhs_10_: i16),
  (lhs_11_: i16),
  (lhs_12_: i16),
  (lhs_13_: i16),
  (lhs_14_: i16) =
    deserialize_4_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 4;
            Core_models.Ops.Range.f_end = mk_usize 8
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 8)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 9)
        lhs_8_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 10)
        lhs_9_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 11)
        lhs_10_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 12)
        lhs_11_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 13)
        lhs_12_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 14)
        lhs_13_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 15)
        lhs_14_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  out

let serialize_5_int (v: t_Slice i16) =
  let r0:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      ((v.[ mk_usize 0 ] <: i16) |. ((v.[ mk_usize 1 ] <: i16) <<! mk_i32 5 <: i16) <: i16)
  in
  let r1:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      ((((v.[ mk_usize 1 ] <: i16) >>! mk_i32 3 <: i16) |.
          ((v.[ mk_usize 2 ] <: i16) <<! mk_i32 2 <: i16)
          <:
          i16) |.
        ((v.[ mk_usize 3 ] <: i16) <<! mk_i32 7 <: i16)
        <:
        i16)
  in
  let r2:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      (((v.[ mk_usize 3 ] <: i16) >>! mk_i32 1 <: i16) |.
        ((v.[ mk_usize 4 ] <: i16) <<! mk_i32 4 <: i16)
        <:
        i16)
  in
  let r3:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      ((((v.[ mk_usize 4 ] <: i16) >>! mk_i32 4 <: i16) |.
          ((v.[ mk_usize 5 ] <: i16) <<! mk_i32 1 <: i16)
          <:
          i16) |.
        ((v.[ mk_usize 6 ] <: i16) <<! mk_i32 6 <: i16)
        <:
        i16)
  in
  let r4:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      (((v.[ mk_usize 6 ] <: i16) >>! mk_i32 2 <: i16) |.
        ((v.[ mk_usize 7 ] <: i16) <<! mk_i32 3 <: i16)
        <:
        i16)
  in
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r0,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r1,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r2,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r3,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r4
  <:
  (u8 & u8 & u8 & u8 & u8)

let serialize_5_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 10 <: bool)
      in
      ()
  in
  let (lhs: u8), (lhs_1_: u8), (lhs_2_: u8), (lhs_3_: u8), (lhs_4_: u8) =
    serialize_5_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 8
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 0) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 1) lhs_1_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 2) lhs_2_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 3) lhs_3_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 4) lhs_4_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_5_: u8), (lhs_6_: u8), (lhs_7_: u8), (lhs_8_: u8) =
    serialize_5_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 8;
            Core_models.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 5) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 6) lhs_5_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 7) lhs_6_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 8) lhs_7_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 9) lhs_8_
  in
  let _:Prims.unit = () in
  out

let deserialize_5_int (bytes: t_Slice u8) =
  let v0:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((bytes.[ mk_usize 0 ] <: u8) &. mk_u8 31 <: u8)
  in
  let v1:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((((bytes.[ mk_usize 1 ] <: u8) &. mk_u8 3 <: u8) <<! mk_i32 3 <: u8) |.
        ((bytes.[ mk_usize 0 ] <: u8) >>! mk_i32 5 <: u8)
        <:
        u8)
  in
  let v2:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      (((bytes.[ mk_usize 1 ] <: u8) >>! mk_i32 2 <: u8) &. mk_u8 31 <: u8)
  in
  let v3:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((((bytes.[ mk_usize 2 ] <: u8) &. mk_u8 15 <: u8) <<! mk_i32 1 <: u8) |.
        ((bytes.[ mk_usize 1 ] <: u8) >>! mk_i32 7 <: u8)
        <:
        u8)
  in
  let v4:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((((bytes.[ mk_usize 3 ] <: u8) &. mk_u8 1 <: u8) <<! mk_i32 4 <: u8) |.
        ((bytes.[ mk_usize 2 ] <: u8) >>! mk_i32 4 <: u8)
        <:
        u8)
  in
  let v5:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      (((bytes.[ mk_usize 3 ] <: u8) >>! mk_i32 1 <: u8) &. mk_u8 31 <: u8)
  in
  let v6:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((((bytes.[ mk_usize 4 ] <: u8) &. mk_u8 7 <: u8) <<! mk_i32 2 <: u8) |.
        ((bytes.[ mk_usize 3 ] <: u8) >>! mk_i32 6 <: u8)
        <:
        u8)
  in
  let v7:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8
      #FStar.Tactics.Typeclasses.solve
      ((bytes.[ mk_usize 4 ] <: u8) >>! mk_i32 3 <: u8)
  in
  v0, v1, v2, v3, v4, v5, v6, v7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

let deserialize_5_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let
  (lhs: i16),
  (lhs_1_: i16),
  (lhs_2_: i16),
  (lhs_3_: i16),
  (lhs_4_: i16),
  (lhs_5_: i16),
  (lhs_6_: i16),
  (lhs_7_: i16) =
    deserialize_5_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 5
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 0)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 1)
        lhs_1_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 2)
        lhs_2_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 3)
        lhs_3_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 4)
        lhs_4_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 5)
        lhs_5_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 6)
        lhs_6_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 7)
        lhs_7_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let
  (lhs: i16),
  (lhs_8_: i16),
  (lhs_9_: i16),
  (lhs_10_: i16),
  (lhs_11_: i16),
  (lhs_12_: i16),
  (lhs_13_: i16),
  (lhs_14_: i16) =
    deserialize_5_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 5;
            Core_models.Ops.Range.f_end = mk_usize 10
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 8)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 9)
        lhs_8_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 10)
        lhs_9_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 11)
        lhs_10_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 12)
        lhs_11_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 13)
        lhs_12_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 14)
        lhs_13_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 15)
        lhs_14_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  out

let serialize_10_int (v: t_Slice i16) =
  let r0:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      ((v.[ mk_usize 0 ] <: i16) &. mk_i16 255 <: i16)
  in
  let r1:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 1 ] <: i16) &. mk_i16 63 <: i16)
        <:
        u8) <<!
      mk_i32 2
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        (((v.[ mk_usize 0 ] <: i16) >>! mk_i32 8 <: i16) &. mk_i16 3 <: i16)
      <:
      u8)
  in
  let r2:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 2 ] <: i16) &. mk_i16 15 <: i16)
        <:
        u8) <<!
      mk_i32 4
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        (((v.[ mk_usize 1 ] <: i16) >>! mk_i32 6 <: i16) &. mk_i16 15 <: i16)
      <:
      u8)
  in
  let r3:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 3 ] <: i16) &. mk_i16 3 <: i16)
        <:
        u8) <<!
      mk_i32 6
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        (((v.[ mk_usize 2 ] <: i16) >>! mk_i32 4 <: i16) &. mk_i16 63 <: i16)
      <:
      u8)
  in
  let r4:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      (((v.[ mk_usize 3 ] <: i16) >>! mk_i32 2 <: i16) &. mk_i16 255 <: i16)
  in
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r0,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r1,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r2,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r3,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r4
  <:
  (u8 & u8 & u8 & u8 & u8)

let serialize_10_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 20 <: bool)
      in
      ()
  in
  let (lhs: u8), (lhs_1_: u8), (lhs_2_: u8), (lhs_3_: u8), (lhs_4_: u8) =
    serialize_10_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 4
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 0) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 1) lhs_1_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 2) lhs_2_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 3) lhs_3_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 4) lhs_4_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_5_: u8), (lhs_6_: u8), (lhs_7_: u8), (lhs_8_: u8) =
    serialize_10_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 4;
            Core_models.Ops.Range.f_end = mk_usize 8
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 5) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 6) lhs_5_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 7) lhs_6_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 8) lhs_7_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 9) lhs_8_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_9_: u8), (lhs_10_: u8), (lhs_11_: u8), (lhs_12_: u8) =
    serialize_10_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 8;
            Core_models.Ops.Range.f_end = mk_usize 12
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 10) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 11) lhs_9_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 12) lhs_10_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 13) lhs_11_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 14) lhs_12_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_13_: u8), (lhs_14_: u8), (lhs_15_: u8), (lhs_16_: u8) =
    serialize_10_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 12;
            Core_models.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 15) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 16) lhs_13_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 17) lhs_14_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 18) lhs_15_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 19) lhs_16_
  in
  let _:Prims.unit = () in
  out

let deserialize_10_int (bytes: t_Slice u8) =
  let r0:i16 =
    Libcrux_secrets.Int.f_as_i16 #i16
      #FStar.Tactics.Typeclasses.solve
      ((((Libcrux_secrets.Int.f_as_i16 #u8
                #FStar.Tactics.Typeclasses.solve
                (bytes.[ mk_usize 1 ] <: u8)
              <:
              i16) &.
            mk_i16 3
            <:
            i16) <<!
          mk_i32 8
          <:
          i16) |.
        ((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 0 ] <: u8)
            <:
            i16) &.
          mk_i16 255
          <:
          i16)
        <:
        i16)
  in
  let r1:i16 =
    Libcrux_secrets.Int.f_as_i16 #i16
      #FStar.Tactics.Typeclasses.solve
      ((((Libcrux_secrets.Int.f_as_i16 #u8
                #FStar.Tactics.Typeclasses.solve
                (bytes.[ mk_usize 2 ] <: u8)
              <:
              i16) &.
            mk_i16 15
            <:
            i16) <<!
          mk_i32 6
          <:
          i16) |.
        ((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 1 ] <: u8)
            <:
            i16) >>!
          mk_i32 2
          <:
          i16)
        <:
        i16)
  in
  let r2:i16 =
    Libcrux_secrets.Int.f_as_i16 #i16
      #FStar.Tactics.Typeclasses.solve
      ((((Libcrux_secrets.Int.f_as_i16 #u8
                #FStar.Tactics.Typeclasses.solve
                (bytes.[ mk_usize 3 ] <: u8)
              <:
              i16) &.
            mk_i16 63
            <:
            i16) <<!
          mk_i32 4
          <:
          i16) |.
        ((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 2 ] <: u8)
            <:
            i16) >>!
          mk_i32 4
          <:
          i16)
        <:
        i16)
  in
  let r3:i16 =
    Libcrux_secrets.Int.f_as_i16 #i16
      #FStar.Tactics.Typeclasses.solve
      (((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 4 ] <: u8)
            <:
            i16) <<!
          mk_i32 2
          <:
          i16) |.
        ((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 3 ] <: u8)
            <:
            i16) >>!
          mk_i32 6
          <:
          i16)
        <:
        i16)
  in
  let r4:i16 =
    Libcrux_secrets.Int.f_as_i16 #i16
      #FStar.Tactics.Typeclasses.solve
      ((((Libcrux_secrets.Int.f_as_i16 #u8
                #FStar.Tactics.Typeclasses.solve
                (bytes.[ mk_usize 6 ] <: u8)
              <:
              i16) &.
            mk_i16 3
            <:
            i16) <<!
          mk_i32 8
          <:
          i16) |.
        ((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 5 ] <: u8)
            <:
            i16) &.
          mk_i16 255
          <:
          i16)
        <:
        i16)
  in
  let r5:i16 =
    Libcrux_secrets.Int.f_as_i16 #i16
      #FStar.Tactics.Typeclasses.solve
      ((((Libcrux_secrets.Int.f_as_i16 #u8
                #FStar.Tactics.Typeclasses.solve
                (bytes.[ mk_usize 7 ] <: u8)
              <:
              i16) &.
            mk_i16 15
            <:
            i16) <<!
          mk_i32 6
          <:
          i16) |.
        ((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 6 ] <: u8)
            <:
            i16) >>!
          mk_i32 2
          <:
          i16)
        <:
        i16)
  in
  let r6:i16 =
    Libcrux_secrets.Int.f_as_i16 #i16
      #FStar.Tactics.Typeclasses.solve
      ((((Libcrux_secrets.Int.f_as_i16 #u8
                #FStar.Tactics.Typeclasses.solve
                (bytes.[ mk_usize 8 ] <: u8)
              <:
              i16) &.
            mk_i16 63
            <:
            i16) <<!
          mk_i32 4
          <:
          i16) |.
        ((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 7 ] <: u8)
            <:
            i16) >>!
          mk_i32 4
          <:
          i16)
        <:
        i16)
  in
  let r7:i16 =
    Libcrux_secrets.Int.f_as_i16 #i16
      #FStar.Tactics.Typeclasses.solve
      (((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 9 ] <: u8)
            <:
            i16) <<!
          mk_i32 2
          <:
          i16) |.
        ((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 8 ] <: u8)
            <:
            i16) >>!
          mk_i32 6
          <:
          i16)
        <:
        i16)
  in
  r0, r1, r2, r3, r4, r5, r6, r7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

let deserialize_10_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let
  (lhs: i16),
  (lhs_1_: i16),
  (lhs_2_: i16),
  (lhs_3_: i16),
  (lhs_4_: i16),
  (lhs_5_: i16),
  (lhs_6_: i16),
  (lhs_7_: i16) =
    deserialize_10_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 10
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 0)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 1)
        lhs_1_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 2)
        lhs_2_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 3)
        lhs_3_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 4)
        lhs_4_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 5)
        lhs_5_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 6)
        lhs_6_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 7)
        lhs_7_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let
  (lhs: i16),
  (lhs_8_: i16),
  (lhs_9_: i16),
  (lhs_10_: i16),
  (lhs_11_: i16),
  (lhs_12_: i16),
  (lhs_13_: i16),
  (lhs_14_: i16) =
    deserialize_10_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 10;
            Core_models.Ops.Range.f_end = mk_usize 20
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 8)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 9)
        lhs_8_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 10)
        lhs_9_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 11)
        lhs_10_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 12)
        lhs_11_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 13)
        lhs_12_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 14)
        lhs_13_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 15)
        lhs_14_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  out

let serialize_11_int (v: t_Slice i16) =
  let r0:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16 #FStar.Tactics.Typeclasses.solve (v.[ mk_usize 0 ] <: i16)
  in
  let r1:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 1 ] <: i16) &. mk_i16 31 <: i16)
        <:
        u8) <<!
      mk_i32 3
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        ((v.[ mk_usize 0 ] <: i16) >>! mk_i32 8 <: i16)
      <:
      u8)
  in
  let r2:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 2 ] <: i16) &. mk_i16 3 <: i16)
        <:
        u8) <<!
      mk_i32 6
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        ((v.[ mk_usize 1 ] <: i16) >>! mk_i32 5 <: i16)
      <:
      u8)
  in
  let r3:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      (((v.[ mk_usize 2 ] <: i16) >>! mk_i32 2 <: i16) &. mk_i16 255 <: i16)
  in
  let r4:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 3 ] <: i16) &. mk_i16 127 <: i16)
        <:
        u8) <<!
      mk_i32 1
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        ((v.[ mk_usize 2 ] <: i16) >>! mk_i32 10 <: i16)
      <:
      u8)
  in
  let r5:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 4 ] <: i16) &. mk_i16 15 <: i16)
        <:
        u8) <<!
      mk_i32 4
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        ((v.[ mk_usize 3 ] <: i16) >>! mk_i32 7 <: i16)
      <:
      u8)
  in
  let r6:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 5 ] <: i16) &. mk_i16 1 <: i16)
        <:
        u8) <<!
      mk_i32 7
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        ((v.[ mk_usize 4 ] <: i16) >>! mk_i32 4 <: i16)
      <:
      u8)
  in
  let r7:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      (((v.[ mk_usize 5 ] <: i16) >>! mk_i32 1 <: i16) &. mk_i16 255 <: i16)
  in
  let r8:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 6 ] <: i16) &. mk_i16 63 <: i16)
        <:
        u8) <<!
      mk_i32 2
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        ((v.[ mk_usize 5 ] <: i16) >>! mk_i32 9 <: i16)
      <:
      u8)
  in
  let r9:u8 =
    ((Libcrux_secrets.Int.f_as_u8 #i16
          #FStar.Tactics.Typeclasses.solve
          ((v.[ mk_usize 7 ] <: i16) &. mk_i16 7 <: i16)
        <:
        u8) <<!
      mk_i32 5
      <:
      u8) |.
    (Libcrux_secrets.Int.f_as_u8 #i16
        #FStar.Tactics.Typeclasses.solve
        ((v.[ mk_usize 6 ] <: i16) >>! mk_i32 6 <: i16)
      <:
      u8)
  in
  let r10:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      ((v.[ mk_usize 7 ] <: i16) >>! mk_i32 3 <: i16)
  in
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r0,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r1,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r2,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r3,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r4,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r5,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r6,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r7,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r8,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r9,
  Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve r10
  <:
  (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)

let serialize_11_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 22 <: bool)
      in
      ()
  in
  let
  (lhs: u8),
  (lhs_1_: u8),
  (lhs_2_: u8),
  (lhs_3_: u8),
  (lhs_4_: u8),
  (lhs_5_: u8),
  (lhs_6_: u8),
  (lhs_7_: u8),
  (lhs_8_: u8),
  (lhs_9_: u8),
  (lhs_10_: u8) =
    serialize_11_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 8
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 0) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 1) lhs_1_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 2) lhs_2_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 3) lhs_3_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 4) lhs_4_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 5) lhs_5_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 6) lhs_6_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 7) lhs_7_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 8) lhs_8_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 9) lhs_9_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 10) lhs_10_
  in
  let _:Prims.unit = () in
  let
  (lhs: u8),
  (lhs_11_: u8),
  (lhs_12_: u8),
  (lhs_13_: u8),
  (lhs_14_: u8),
  (lhs_15_: u8),
  (lhs_16_: u8),
  (lhs_17_: u8),
  (lhs_18_: u8),
  (lhs_19_: u8),
  (lhs_20_: u8) =
    serialize_11_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 8;
            Core_models.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 11) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 12) lhs_11_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 13) lhs_12_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 14) lhs_13_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 15) lhs_14_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 16) lhs_15_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 17) lhs_16_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 18) lhs_17_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 19) lhs_18_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 20) lhs_19_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 21) lhs_20_
  in
  let _:Prims.unit = () in
  out

let deserialize_11_int (bytes: t_Slice u8) =
  let r0:i16 =
    (((Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ mk_usize 1 ] <: u8)
          <:
          i16) &.
        mk_i16 7
        <:
        i16) <<!
      mk_i32 8
      <:
      i16) |.
    (Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 0 ] <: u8)
      <:
      i16)
  in
  let r1:i16 =
    (((Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ mk_usize 2 ] <: u8)
          <:
          i16) &.
        mk_i16 63
        <:
        i16) <<!
      mk_i32 5
      <:
      i16) |.
    ((Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 1 ] <: u8)
        <:
        i16) >>!
      mk_i32 3
      <:
      i16)
  in
  let r2:i16 =
    ((((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 4 ] <: u8)
            <:
            i16) &.
          mk_i16 1
          <:
          i16) <<!
        mk_i32 10
        <:
        i16) |.
      ((Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ mk_usize 3 ] <: u8)
          <:
          i16) <<!
        mk_i32 2
        <:
        i16)
      <:
      i16) |.
    ((Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 2 ] <: u8)
        <:
        i16) >>!
      mk_i32 6
      <:
      i16)
  in
  let r3:i16 =
    (((Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ mk_usize 5 ] <: u8)
          <:
          i16) &.
        mk_i16 15
        <:
        i16) <<!
      mk_i32 7
      <:
      i16) |.
    ((Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 4 ] <: u8)
        <:
        i16) >>!
      mk_i32 1
      <:
      i16)
  in
  let r4:i16 =
    (((Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ mk_usize 6 ] <: u8)
          <:
          i16) &.
        mk_i16 127
        <:
        i16) <<!
      mk_i32 4
      <:
      i16) |.
    ((Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 5 ] <: u8)
        <:
        i16) >>!
      mk_i32 4
      <:
      i16)
  in
  let r5:i16 =
    ((((Libcrux_secrets.Int.f_as_i16 #u8
              #FStar.Tactics.Typeclasses.solve
              (bytes.[ mk_usize 8 ] <: u8)
            <:
            i16) &.
          mk_i16 3
          <:
          i16) <<!
        mk_i32 9
        <:
        i16) |.
      ((Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ mk_usize 7 ] <: u8)
          <:
          i16) <<!
        mk_i32 1
        <:
        i16)
      <:
      i16) |.
    ((Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 6 ] <: u8)
        <:
        i16) >>!
      mk_i32 7
      <:
      i16)
  in
  let r6:i16 =
    (((Libcrux_secrets.Int.f_as_i16 #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ mk_usize 9 ] <: u8)
          <:
          i16) &.
        mk_i16 31
        <:
        i16) <<!
      mk_i32 6
      <:
      i16) |.
    ((Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 8 ] <: u8)
        <:
        i16) >>!
      mk_i32 2
      <:
      i16)
  in
  let r7:i16 =
    ((Libcrux_secrets.Int.f_as_i16 #u8
          #FStar.Tactics.Typeclasses.solve
          (bytes.[ mk_usize 10 ] <: u8)
        <:
        i16) <<!
      mk_i32 3
      <:
      i16) |.
    ((Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 9 ] <: u8)
        <:
        i16) >>!
      mk_i32 5
      <:
      i16)
  in
  r0, r1, r2, r3, r4, r5, r6, r7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

let deserialize_11_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let
  (lhs: i16),
  (lhs_1_: i16),
  (lhs_2_: i16),
  (lhs_3_: i16),
  (lhs_4_: i16),
  (lhs_5_: i16),
  (lhs_6_: i16),
  (lhs_7_: i16) =
    deserialize_11_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 11
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 0)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 1)
        lhs_1_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 2)
        lhs_2_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 3)
        lhs_3_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 4)
        lhs_4_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 5)
        lhs_5_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 6)
        lhs_6_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 7)
        lhs_7_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let
  (lhs: i16),
  (lhs_8_: i16),
  (lhs_9_: i16),
  (lhs_10_: i16),
  (lhs_11_: i16),
  (lhs_12_: i16),
  (lhs_13_: i16),
  (lhs_14_: i16) =
    deserialize_11_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 11;
            Core_models.Ops.Range.f_end = mk_usize 22
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 8)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 9)
        lhs_8_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 10)
        lhs_9_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 11)
        lhs_10_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 12)
        lhs_11_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 13)
        lhs_12_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 14)
        lhs_13_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 15)
        lhs_14_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  out

let serialize_12_int (v: t_Slice i16) =
  let r0:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      ((v.[ mk_usize 0 ] <: i16) &. mk_i16 255 <: i16)
  in
  let r1:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      (((v.[ mk_usize 0 ] <: i16) >>! mk_i32 8 <: i16) |.
        (((v.[ mk_usize 1 ] <: i16) &. mk_i16 15 <: i16) <<! mk_i32 4 <: i16)
        <:
        i16)
  in
  let r2:u8 =
    Libcrux_secrets.Int.f_as_u8 #i16
      #FStar.Tactics.Typeclasses.solve
      (((v.[ mk_usize 1 ] <: i16) >>! mk_i32 4 <: i16) &. mk_i16 255 <: i16)
  in
  r0, r1, r2 <: (u8 & u8 & u8)

let serialize_12_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 24 <: bool)
      in
      ()
  in
  let (lhs: u8), (lhs_1_: u8), (lhs_2_: u8) =
    serialize_12_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 2
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 0) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 1) lhs_1_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 2) lhs_2_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_3_: u8), (lhs_4_: u8) =
    serialize_12_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 2;
            Core_models.Ops.Range.f_end = mk_usize 4
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 3) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 4) lhs_3_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 5) lhs_4_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_5_: u8), (lhs_6_: u8) =
    serialize_12_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 4;
            Core_models.Ops.Range.f_end = mk_usize 6
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 6) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 7) lhs_5_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 8) lhs_6_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_7_: u8), (lhs_8_: u8) =
    serialize_12_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 6;
            Core_models.Ops.Range.f_end = mk_usize 8
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 9) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 10) lhs_7_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 11) lhs_8_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_9_: u8), (lhs_10_: u8) =
    serialize_12_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 8;
            Core_models.Ops.Range.f_end = mk_usize 10
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 12) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 13) lhs_9_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 14) lhs_10_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_11_: u8), (lhs_12_: u8) =
    serialize_12_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 10;
            Core_models.Ops.Range.f_end = mk_usize 12
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 15) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 16) lhs_11_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 17) lhs_12_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_13_: u8), (lhs_14_: u8) =
    serialize_12_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 12;
            Core_models.Ops.Range.f_end = mk_usize 14
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 18) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 19) lhs_13_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 20) lhs_14_
  in
  let _:Prims.unit = () in
  let (lhs: u8), (lhs_15_: u8), (lhs_16_: u8) =
    serialize_12_int (v.Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
            Core_models.Ops.Range.f_start = mk_usize 14;
            Core_models.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice i16)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 21) lhs
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 22) lhs_15_
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 23) lhs_16_
  in
  let _:Prims.unit = () in
  out

let deserialize_12_int (bytes: t_Slice u8) =
  let byte0:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 0 ] <: u8)
  in
  let byte1:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 1 ] <: u8)
  in
  let byte2:i16 =
    Libcrux_secrets.Int.f_as_i16 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 2 ] <: u8)
  in
  let r0:i16 = ((byte1 &. mk_i16 15 <: i16) <<! mk_i32 8 <: i16) |. (byte0 &. mk_i16 255 <: i16) in
  let r1:i16 = (byte2 <<! mk_i32 4 <: i16) |. ((byte1 >>! mk_i32 4 <: i16) &. mk_i16 15 <: i16) in
  r0, r1 <: (i16 & i16)

let deserialize_12_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let (lhs: i16), (lhs_1_: i16) =
    deserialize_12_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 3
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 0)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 1)
        lhs_1_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let (lhs: i16), (lhs_2_: i16) =
    deserialize_12_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 3;
            Core_models.Ops.Range.f_end = mk_usize 6
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 2)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 3)
        lhs_2_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let (lhs: i16), (lhs_3_: i16) =
    deserialize_12_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 6;
            Core_models.Ops.Range.f_end = mk_usize 9
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 4)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 5)
        lhs_3_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let (lhs: i16), (lhs_4_: i16) =
    deserialize_12_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 9;
            Core_models.Ops.Range.f_end = mk_usize 12
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 6)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 7)
        lhs_4_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let (lhs: i16), (lhs_5_: i16) =
    deserialize_12_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 12;
            Core_models.Ops.Range.f_end = mk_usize 15
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 8)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 9)
        lhs_5_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let (lhs: i16), (lhs_6_: i16) =
    deserialize_12_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 15;
            Core_models.Ops.Range.f_end = mk_usize 18
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 10)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 11)
        lhs_6_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let (lhs: i16), (lhs_7_: i16) =
    deserialize_12_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 18;
            Core_models.Ops.Range.f_end = mk_usize 21
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 12)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 13)
        lhs_7_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  let (lhs: i16), (lhs_8_: i16) =
    deserialize_12_int (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 21;
            Core_models.Ops.Range.f_end = mk_usize 24
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 14)
        lhs
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_iot_ml_kem.Vector.Portable.Vector_type.f_elements
        (mk_usize 15)
        lhs_8_
    }
    <:
    Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let _:Prims.unit = () in
  out
