module Libcrux_iot_ml_kem.Vector.Portable.Serialize
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

val serialize_1_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 2)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 2)

val deserialize_1_
      (v: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 v <: usize) =. mk_usize 2)
      (fun _ -> Prims.l_True)

val serialize_4_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 8)
      (fun _ -> Prims.l_True)

val serialize_4_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 8)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 8)

val deserialize_4_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 4)
      (fun _ -> Prims.l_True)

val deserialize_4_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 8)
      (fun _ -> Prims.l_True)

val serialize_5_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 8)
      (fun _ -> Prims.l_True)

val serialize_5_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 10)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 10)

val deserialize_5_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 5)
      (fun _ -> Prims.l_True)

val deserialize_5_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 10)
      (fun _ -> Prims.l_True)

val serialize_10_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 4)
      (fun _ -> Prims.l_True)

val serialize_10_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 20)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 20)

val deserialize_10_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 10)
      (fun _ -> Prims.l_True)

val deserialize_10_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 20)
      (fun _ -> Prims.l_True)

val serialize_11_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 8)
      (fun _ -> Prims.l_True)

val serialize_11_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 22)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 22)

val deserialize_11_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 11)
      (fun _ -> Prims.l_True)

val deserialize_11_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 22)
      (fun _ -> Prims.l_True)

val serialize_12_int (v: t_Slice i16)
    : Prims.Pure (u8 & u8 & u8)
      (requires (Core.Slice.impl__len #i16 v <: usize) =. mk_usize 2)
      (fun _ -> Prims.l_True)

val serialize_12_
      (v: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 24)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 24)

val deserialize_12_int (bytes: t_Slice u8)
    : Prims.Pure (i16 & i16)
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 3)
      (fun _ -> Prims.l_True)

val deserialize_12_
      (bytes: t_Slice u8)
      (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires (Core.Slice.impl__len #u8 bytes <: usize) =. mk_usize 24)
      (fun _ -> Prims.l_True)
