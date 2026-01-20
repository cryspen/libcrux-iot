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

val to_unsigned_field_modulus
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a out: v_Vector)
    : Prims.Pure v_Vector Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_message
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires
        (Core_models.Slice.impl__len #u8 serialized <: usize) =.
        Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (ensures
        fun temp_0_ ->
          let (serialized_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 serialized_future <: usize) =.
          (Core_models.Slice.impl__len #u8 serialized <: usize))

val deserialize_then_decompress_message
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Array u8 (mk_usize 32))
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_uncompressed_ring_element
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (serialized: t_Slice u8)
    : Prims.Pure (v_Vector & t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 serialized <: usize) =.
        Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
      (ensures
        fun temp_0_ ->
          let (scratch_future: v_Vector), (serialized_future: t_Slice u8) = temp_0_ in
          (Core_models.Slice.impl__len #u8 serialized_future <: usize) =.
          (Core_models.Slice.impl__len #u8 serialized <: usize))

val deserialize_to_uncompressed_ring_element
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Core_models.Slice.impl__len #u8 serialized <: usize) =.
        Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
      (fun _ -> Prims.l_True)

/// Only use with public values.
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
val deserialize_to_reduced_ring_element
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Core_models.Slice.impl__len #u8 serialized <: usize) =.
        Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
      (fun _ -> Prims.l_True)

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
/// This function MUST NOT be used on secret inputs.
val deserialize_ring_elements_reduced
      (v_K: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: t_Slice u8)
      (deserialized_pk: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
    : Prims.Pure (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (requires
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            deserialized_pk
          <:
          usize) =.
        v_K &&
        ((Core_models.Slice.impl__len #u8 public_key <: usize) /!
          Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
          <:
          usize) =.
        v_K)
      (ensures
        fun deserialized_pk_future ->
          let deserialized_pk_future:t_Slice
          (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            deserialized_pk_future
          in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              deserialized_pk_future
            <:
            usize) =.
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              deserialized_pk
            <:
            usize))

val compress_then_serialize_10_
      (v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires
        (Core_models.Slice.impl__len #u8 serialized <: usize) =. v_BLOCK_LEN &&
        v_BLOCK_LEN >=.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 20 <: usize))
      (ensures
        fun temp_0_ ->
          let (serialized_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 serialized_future <: usize) =.
          (Core_models.Slice.impl__len #u8 serialized <: usize))

val compress_then_serialize_11_
      (v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires
        (Core_models.Slice.impl__len #u8 serialized <: usize) =. v_BLOCK_LEN &&
        v_BLOCK_LEN >=.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 22 <: usize))
      (ensures
        fun temp_0_ ->
          let (serialized_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 serialized_future <: usize) =.
          (Core_models.Slice.impl__len #u8 serialized <: usize))

val compress_then_serialize_ring_element_u
      (v_U_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires
        (v_U_COMPRESSION_FACTOR =. mk_usize 10 &&
        v_BLOCK_LEN >=.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 20 <: usize) ||
        v_U_COMPRESSION_FACTOR =. mk_usize 11 &&
        v_BLOCK_LEN >=.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 22 <: usize)) &&
        (Core_models.Slice.impl__len #u8 serialized <: usize) =. v_BLOCK_LEN)
      (ensures
        fun temp_0_ ->
          let (serialized_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 serialized_future <: usize) =.
          (Core_models.Slice.impl__len #u8 serialized <: usize))

val compress_then_serialize_4_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires (Core_models.Slice.impl__len #u8 serialized <: usize) =. mk_usize 128)
      (ensures
        fun temp_0_ ->
          let (serialized_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 serialized_future <: usize) =.
          (Core_models.Slice.impl__len #u8 serialized <: usize))

val compress_then_serialize_5_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires (Core_models.Slice.impl__len #u8 serialized <: usize) =. mk_usize 160)
      (ensures
        fun temp_0_ ->
          let (serialized_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 serialized_future <: usize) =.
          (Core_models.Slice.impl__len #u8 serialized <: usize))

val compress_then_serialize_ring_element_v
      (v_K v_V_COMPRESSION_FACTOR v_C2_LEN: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (out: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires
        (Core_models.Slice.impl__len #u8 out <: usize) =. v_C2_LEN &&
        (v_V_COMPRESSION_FACTOR =. mk_usize 4 && v_C2_LEN =. mk_usize 128 ||
        v_V_COMPRESSION_FACTOR =. mk_usize 5 && v_C2_LEN =. mk_usize 160))
      (ensures
        fun temp_0_ ->
          let (out_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize))

val deserialize_then_decompress_10_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires (Core_models.Slice.impl__len #u8 serialized <: usize) =. mk_usize 320)
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_11_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires (Core_models.Slice.impl__len #u8 serialized <: usize) =. mk_usize 352)
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_u
      (v_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
      (output: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (v_U_COMPRESSION_FACTOR =. mk_usize 10 || v_U_COMPRESSION_FACTOR =. mk_usize 11) &&
        (Core_models.Slice.impl__len #u8 serialized <: usize) =.
        (mk_usize 32 *! v_U_COMPRESSION_FACTOR <: usize))
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_4_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires (Core_models.Slice.impl__len #u8 serialized <: usize) =. mk_usize 128)
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_5_
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
      (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires (Core_models.Slice.impl__len #u8 serialized <: usize) =. mk_usize 160)
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_v
      (v_K v_V_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
      (output: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (v_V_COMPRESSION_FACTOR =. mk_usize 4 || v_V_COMPRESSION_FACTOR =. mk_usize 5) &&
        (Core_models.Slice.impl__len #u8 serialized <: usize) =.
        (mk_usize 32 *! v_V_COMPRESSION_FACTOR <: usize))
      (fun _ -> Prims.l_True)
