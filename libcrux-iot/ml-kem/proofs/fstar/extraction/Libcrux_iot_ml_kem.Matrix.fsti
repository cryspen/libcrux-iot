module Libcrux_iot_ml_kem.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Hash_functions in
  let open Libcrux_iot_ml_kem.Vector.Traits in
  let open Libcrux_secrets.Int.Classify_public in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

val entry
      (v_K: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (matrix: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (i j: usize)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        v_K <=. mk_usize 4 && i <. v_K && j <. v_K &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            matrix
          <:
          usize) =.
        (v_K *! v_K <: usize))
      (fun _ -> Prims.l_True)

val sample_matrix_entry
      (#v_Vector #v_Hasher: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i1: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |}
      (out: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (seed: t_Slice u8)
      (i j: usize)
    : Prims.Pure (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires (Core_models.Slice.impl__len #u8 seed <: usize) =. mk_usize 32)
      (fun _ -> Prims.l_True)

val sample_matrix_A
      (v_K: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i1: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |}
      (v_A_transpose: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (seed: t_Array u8 (mk_usize 34))
      (transpose: bool)
    : Prims.Pure (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (requires
        v_K <=. mk_usize 4 &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            v_A_transpose
          <:
          usize) =.
        (v_K *! v_K <: usize))
      (ensures
        fun v_A_transpose_future ->
          let v_A_transpose_future:t_Slice
          (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            v_A_transpose_future
          in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              v_A_transpose_future
            <:
            usize) =.
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              v_A_transpose
            <:
            usize))

/// The following functions compute various expressions involving
/// vectors and matrices. The computation of these expressions has been
/// abstracted away into these functions in order to save on loop iterations.
/// Compute v − InverseNTT(sᵀ ◦ NTT(u))
val compute_message
      (v_K: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (v: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (secret_as_ntt u_as_ntt:
          t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (result: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure
      (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector &
        t_Array i32 (mk_usize 256)) Prims.l_True (fun _ -> Prims.l_True)

/// Compute InverseNTT(tᵀ ◦ r\u{302}) + e₂ + message
val compute_ring_element_v
      (v_K: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: t_Slice u8)
      (tt_as_ntt_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (r_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (error_2_ message result: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure
      (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
        v_Vector &
        t_Array i32 (mk_usize 256))
      (requires
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            r_as_ntt
          <:
          usize) =.
        v_K &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            cache
          <:
          usize) =.
        v_K &&
        ((Core_models.Slice.impl__len #u8 public_key <: usize) /!
          Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
          <:
          usize) =.
        v_K)
      (fun _ -> Prims.l_True)

/// Compute u := InvertNTT(Aᵀ ◦ r\u{302}) + e₁
val compute_vector_u
      (v_K: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i1: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |}
      (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (seed: t_Slice u8)
      (r_as_ntt error_1_ result:
          t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure
      (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
        t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
        v_Vector &
        t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
        t_Array i32 (mk_usize 256))
      (requires
        (Core_models.Slice.impl__len #u8 seed <: usize) =. mk_usize 32 &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            r_as_ntt
          <:
          usize) =.
        v_K &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            error_1_
          <:
          usize) =.
        v_K &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            result
          <:
          usize) =.
        v_K &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            cache
          <:
          usize) =.
        v_K &&
        v_K >. mk_usize 0)
      (ensures
        fun temp_0_ ->
          let
          (matrix_entry_future: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
          (result_future: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (scratch_future: v_Vector),
          (cache_future: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (accumulator_future: t_Array i32 (mk_usize 256)) =
            temp_0_
          in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              result_future
            <:
            usize) =.
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              result
            <:
            usize) &&
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              cache_future
            <:
            usize) =.
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              cache
            <:
            usize))

/// Compute Â ◦ ŝ + ê
val compute_As_plus_e
      (v_K: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (tt_as_ntt: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (matrix_A: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (s_as_ntt error_as_ntt s_cache:
          t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure
      (t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
        t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
        t_Array i32 (mk_usize 256))
      (requires
        v_K >. mk_usize 0 && v_K <=. mk_usize 4 &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            matrix_A
          <:
          usize) =.
        (v_K *! v_K <: usize))
      (fun _ -> Prims.l_True)
