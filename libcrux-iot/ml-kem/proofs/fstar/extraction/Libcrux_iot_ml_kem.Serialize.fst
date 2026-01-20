module Libcrux_iot_ml_kem.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Traits in
  let open Libcrux_secrets.Int.Classify_public in
  let open Libcrux_secrets.Traits in
  ()

let to_unsigned_field_modulus
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a out: v_Vector)
     =
  let out:v_Vector = Libcrux_iot_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector a out in
  out

let compress_then_serialize_message
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
     =
  let (scratch: v_Vector), (serialized: t_Slice u8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 serialized <: usize) =.
          Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE
          <:
          bool)
      (scratch, serialized <: (v_Vector & t_Slice u8))
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          let scratch:v_Vector =
            to_unsigned_field_modulus #v_Vector
              (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
              scratch
          in
          let scratch:v_Vector =
            Libcrux_iot_ml_kem.Vector.Traits.f_compress_1_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              scratch
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core_models.Ops.Range.f_start = mk_usize 2 *! i <: usize;
                  Core_models.Ops.Range.f_end = (mk_usize 2 *! i <: usize) +! mk_usize 2 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Libcrux_iot_ml_kem.Vector.Traits.f_serialize_1_ #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  scratch
                  (serialized.[ {
                        Core_models.Ops.Range.f_start = mk_usize 2 *! i <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (mk_usize 2 *! i <: usize) +! mk_usize 2 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          scratch, serialized <: (v_Vector & t_Slice u8))
  in
  serialized, scratch <: (t_Slice u8 & v_Vector)

let deserialize_then_decompress_message
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Array u8 (mk_usize 32))
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re i ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i:usize = i in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_deserialize_1_ #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (serialized.[ {
                          Core_models.Ops.Range.f_start = mk_usize 2 *! i <: usize;
                          Core_models.Ops.Range.f_end
                          =
                          (mk_usize 2 *! i <: usize) +! mk_usize 2 <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
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
                i
                (Libcrux_iot_ml_kem.Vector.Traits.decompress_1_ #v_Vector
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let serialize_uncompressed_ring_element
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 serialized <: usize) =.
            Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
            <:
            bool)
      in
      ()
  in
  let (scratch: v_Vector), (serialized: t_Slice u8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 serialized <: usize) =.
          Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
          <:
          bool)
      (scratch, serialized <: (v_Vector & t_Slice u8))
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          let scratch:v_Vector =
            to_unsigned_field_modulus #v_Vector
              (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
              scratch
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core_models.Ops.Range.f_start = mk_usize 24 *! i <: usize;
                  Core_models.Ops.Range.f_end = (mk_usize 24 *! i <: usize) +! mk_usize 24 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Libcrux_iot_ml_kem.Vector.Traits.f_serialize_12_ #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  scratch
                  (serialized.[ {
                        Core_models.Ops.Range.f_start = mk_usize 24 *! i <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (mk_usize 24 *! i <: usize) +! mk_usize 24 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          scratch, serialized <: (v_Vector & t_Slice u8))
  in
  scratch, serialized <: (v_Vector & t_Slice u8)

let deserialize_to_uncompressed_ring_element
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 24)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let (i: usize), (bytes: t_Slice u8) = temp_1_ in
          {
            re with
            Libcrux_iot_ml_kem.Polynomial.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux_iot_ml_kem.Polynomial.f_coefficients
              i
              (Libcrux_iot_ml_kem.Vector.Traits.f_deserialize_12_ #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  bytes
                  (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
            <:
            t_Array v_Vector (mk_usize 16)
          }
          <:
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  re

let deserialize_to_reduced_ring_element
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 24)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let (i: usize), (bytes: t_Slice u8) = temp_1_ in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_deserialize_12_ #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    bytes
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
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
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_cond_subtract_3329_ #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_ring_elements_reduced
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key: t_Slice u8)
      (deserialized_pk: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
     =
  let deserialized_pk:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
      public_key
      (fun deserialized_pk i ->
          let deserialized_pk:t_Slice
          (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            deserialized_pk
          in
          let i:usize = i in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              deserialized_pk
            <:
            usize) =.
          v_K
          <:
          bool)
      deserialized_pk
      (fun deserialized_pk temp_1_ ->
          let deserialized_pk:t_Slice
          (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            deserialized_pk
          in
          let (i: usize), (ring_element: t_Slice u8) = temp_1_ in
          let deserialized_pk:t_Slice
          (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize deserialized_pk
              i
              (deserialize_to_reduced_ring_element #v_Vector
                  (Libcrux_secrets.Traits.f_classify_ref #(t_Slice u8)
                      #FStar.Tactics.Typeclasses.solve
                      ring_element
                    <:
                    t_Slice u8)
                  (deserialized_pk.[ i ]
                    <:
                    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          deserialized_pk)
  in
  deserialized_pk

let compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 serialized <: usize) =. v_OUT_LEN <: bool
          )
      in
      ()
  in
  let (scratch: v_Vector), (serialized: t_Slice u8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 serialized <: usize) =. v_OUT_LEN <: bool)
      (scratch, serialized <: (v_Vector & t_Slice u8))
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          let scratch:v_Vector =
            to_unsigned_field_modulus #v_Vector
              (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
              scratch
          in
          let scratch:v_Vector =
            Libcrux_iot_ml_kem.Vector.Traits.f_compress #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (mk_i32 10)
              scratch
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core_models.Ops.Range.f_start = mk_usize 20 *! i <: usize;
                  Core_models.Ops.Range.f_end = (mk_usize 20 *! i <: usize) +! mk_usize 20 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Libcrux_iot_ml_kem.Vector.Traits.f_serialize_10_ #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  scratch
                  (serialized.[ {
                        Core_models.Ops.Range.f_start = mk_usize 20 *! i <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (mk_usize 20 *! i <: usize) +! mk_usize 20 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          scratch, serialized <: (v_Vector & t_Slice u8))
  in
  serialized, scratch <: (t_Slice u8 & v_Vector)

let compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 serialized <: usize) =. v_OUT_LEN <: bool
          )
      in
      ()
  in
  let (scratch: v_Vector), (serialized: t_Slice u8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 serialized <: usize) =. v_OUT_LEN <: bool)
      (scratch, serialized <: (v_Vector & t_Slice u8))
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          let scratch:v_Vector =
            Libcrux_iot_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector
              (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
              scratch
          in
          let scratch:v_Vector =
            Libcrux_iot_ml_kem.Vector.Traits.f_compress #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (mk_i32 11)
              scratch
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core_models.Ops.Range.f_start = mk_usize 22 *! i <: usize;
                  Core_models.Ops.Range.f_end = (mk_usize 22 *! i <: usize) +! mk_usize 22 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Libcrux_iot_ml_kem.Vector.Traits.f_serialize_11_ #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  scratch
                  (serialized.[ {
                        Core_models.Ops.Range.f_start = mk_usize 22 *! i <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (mk_usize 22 *! i <: usize) +! mk_usize 22 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          scratch, serialized <: (v_Vector & t_Slice u8))
  in
  serialized, scratch <: (t_Slice u8 & v_Vector)

let compress_then_serialize_ring_element_u
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
     =
  let (scratch: v_Vector), (serialized: t_Slice u8) =
    match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
    | Rust_primitives.Integers.MkInt 10 ->
      let (tmp0: t_Slice u8), (tmp1: v_Vector) =
        compress_then_serialize_10_ v_OUT_LEN #v_Vector re serialized scratch
      in
      let serialized:t_Slice u8 = tmp0 in
      let scratch:v_Vector = tmp1 in
      scratch, serialized <: (v_Vector & t_Slice u8)
    | Rust_primitives.Integers.MkInt 11 ->
      let (tmp0: t_Slice u8), (tmp1: v_Vector) =
        compress_then_serialize_11_ v_OUT_LEN #v_Vector re serialized scratch
      in
      let serialized:t_Slice u8 = tmp0 in
      let scratch:v_Vector = tmp1 in
      scratch, serialized <: (v_Vector & t_Slice u8)
    | _ -> scratch, serialized <: (v_Vector & t_Slice u8)
  in
  serialized, scratch <: (t_Slice u8 & v_Vector)

let compress_then_serialize_4_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
     =
  let (scratch: v_Vector), (serialized: t_Slice u8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 serialized <: usize) =. mk_usize 128 <: bool)
      (scratch, serialized <: (v_Vector & t_Slice u8))
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          let scratch:v_Vector =
            to_unsigned_field_modulus #v_Vector
              (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
              scratch
          in
          let scratch:v_Vector =
            Libcrux_iot_ml_kem.Vector.Traits.f_compress #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (mk_i32 4)
              scratch
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core_models.Ops.Range.f_start = mk_usize 8 *! i <: usize;
                  Core_models.Ops.Range.f_end = (mk_usize 8 *! i <: usize) +! mk_usize 8 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Libcrux_iot_ml_kem.Vector.Traits.f_serialize_4_ #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  scratch
                  (serialized.[ {
                        Core_models.Ops.Range.f_start = mk_usize 8 *! i <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (mk_usize 8 *! i <: usize) +! mk_usize 8 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          scratch, serialized <: (v_Vector & t_Slice u8))
  in
  serialized, scratch <: (t_Slice u8 & v_Vector)

let compress_then_serialize_5_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
     =
  let (scratch: v_Vector), (serialized: t_Slice u8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 serialized <: usize) =. mk_usize 160 <: bool)
      (scratch, serialized <: (v_Vector & t_Slice u8))
      (fun temp_0_ i ->
          let (scratch: v_Vector), (serialized: t_Slice u8) = temp_0_ in
          let i:usize = i in
          let scratch:v_Vector =
            Libcrux_iot_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector
              (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
              scratch
          in
          let scratch:v_Vector =
            Libcrux_iot_ml_kem.Vector.Traits.f_compress #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (mk_i32 5)
              scratch
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core_models.Ops.Range.f_start = mk_usize 10 *! i <: usize;
                  Core_models.Ops.Range.f_end = (mk_usize 10 *! i <: usize) +! mk_usize 10 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Libcrux_iot_ml_kem.Vector.Traits.f_serialize_5_ #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  scratch
                  (serialized.[ {
                        Core_models.Ops.Range.f_start = mk_usize 10 *! i <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (mk_usize 10 *! i <: usize) +! mk_usize 10 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          scratch, serialized <: (v_Vector & t_Slice u8))
  in
  serialized, scratch <: (t_Slice u8 & v_Vector)

let compress_then_serialize_ring_element_v
      (v_K v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (out: t_Slice u8)
      (scratch: v_Vector)
     =
  let (out: t_Slice u8), (scratch: v_Vector) =
    match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
    | Rust_primitives.Integers.MkInt 4 ->
      let (tmp0: t_Slice u8), (tmp1: v_Vector) =
        compress_then_serialize_4_ #v_Vector re out scratch
      in
      let out:t_Slice u8 = tmp0 in
      let scratch:v_Vector = tmp1 in
      out, scratch <: (t_Slice u8 & v_Vector)
    | Rust_primitives.Integers.MkInt 5 ->
      let (tmp0: t_Slice u8), (tmp1: v_Vector) =
        compress_then_serialize_5_ #v_Vector re out scratch
      in
      let out:t_Slice u8 = tmp0 in
      let scratch:v_Vector = tmp1 in
      out, scratch <: (t_Slice u8 & v_Vector)
    | _ -> out, scratch <: (t_Slice u8 & v_Vector)
  in
  out, scratch <: (t_Slice u8 & v_Vector)

let deserialize_then_decompress_10_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 20)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let (i: usize), (bytes: t_Slice u8) = temp_1_ in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_deserialize_10_ #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    bytes
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
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
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (mk_i32 10)
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_11_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 22)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let (i: usize), (bytes: t_Slice u8) = temp_1_ in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_deserialize_11_ #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    bytes
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
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
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (mk_i32 11)
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
      (output: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let output:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
    | Rust_primitives.Integers.MkInt 10 ->
      deserialize_then_decompress_10_ #v_Vector serialized output
    | Rust_primitives.Integers.MkInt 11 ->
      deserialize_then_decompress_11_ #v_Vector serialized output
    | _ -> output
  in
  output

let deserialize_then_decompress_4_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 8)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let (i: usize), (bytes: t_Slice u8) = temp_1_ in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_deserialize_4_ #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    bytes
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
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
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (mk_i32 4)
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_5_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 10)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let (i: usize), (bytes: t_Slice u8) = temp_1_ in
          let re:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_iot_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_iot_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_deserialize_5_ #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    bytes
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
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
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (mk_i32 5)
                    (re.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_ring_element_v
      (v_K v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
      (output: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let output:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
    | Rust_primitives.Integers.MkInt 4 -> deserialize_then_decompress_4_ #v_Vector serialized output
    | Rust_primitives.Integers.MkInt 5 -> deserialize_then_decompress_5_ #v_Vector serialized output
    | _ -> output
  in
  output
