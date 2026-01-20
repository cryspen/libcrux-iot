module Libcrux_iot_ml_kem.Vector.Portable.Ntt
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

val ntt_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires i <. mk_usize 16 && j <. mk_usize 16)
      (fun _ -> Prims.l_True)

val ntt_layer_1_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_layer_2_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_layer_3_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val inv_ntt_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires i <. mk_usize 16 && j <. mk_usize 16)
      (fun _ -> Prims.l_True)

val inv_ntt_layer_1_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val inv_ntt_layer_2_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val inv_ntt_layer_3_step
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say \"almost\" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val accumulating_ntt_multiply_binomials_fill_cache
      (a b: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i: usize)
      (out: t_Slice i32)
      (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (requires i <. mk_usize 8 && (Core_models.Slice.impl__len #i32 out <: usize) >=. mk_usize 16)
      (ensures
        fun temp_0_ ->
          let
          (out_future: t_Slice i32),
          (cache_future: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
            temp_0_
          in
          (Core_models.Slice.impl__len #i32 out_future <: usize) =.
          (Core_models.Slice.impl__len #i32 out <: usize))

val accumulating_ntt_multiply_binomials_use_cache
      (a b: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (i: usize)
      (out: t_Slice i32)
      (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Slice i32)
      (requires i <. mk_usize 8 && (Core_models.Slice.impl__len #i32 out <: usize) >=. mk_usize 16)
      (ensures
        fun out_future ->
          let out_future:t_Slice i32 = out_future in
          (Core_models.Slice.impl__len #i32 out_future <: usize) =.
          (Core_models.Slice.impl__len #i32 out <: usize))

val accumulating_ntt_multiply_binomials
      (a b: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i: usize)
      (out: t_Slice i32)
    : Prims.Pure (t_Slice i32)
      (requires i <. mk_usize 8 && (Core_models.Slice.impl__len #i32 out <: usize) >=. mk_usize 16)
      (ensures
        fun out_future ->
          let out_future:t_Slice i32 = out_future in
          (Core_models.Slice.impl__len #i32 out_future <: usize) =.
          (Core_models.Slice.impl__len #i32 out <: usize))

val accumulating_ntt_multiply
      (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice i32)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure (t_Slice i32)
      (requires (Core_models.Slice.impl__len #i32 out <: usize) >=. mk_usize 16)
      (ensures
        fun out_future ->
          let out_future:t_Slice i32 = out_future in
          (Core_models.Slice.impl__len #i32 out_future <: usize) =.
          (Core_models.Slice.impl__len #i32 out <: usize))

val accumulating_ntt_multiply_fill_cache
      (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice i32)
      (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure (t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (requires (Core_models.Slice.impl__len #i32 out <: usize) >=. mk_usize 16)
      (ensures
        fun temp_0_ ->
          let
          (out_future: t_Slice i32),
          (cache_future: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
            temp_0_
          in
          (Core_models.Slice.impl__len #i32 out_future <: usize) =.
          (Core_models.Slice.impl__len #i32 out <: usize))

val accumulating_ntt_multiply_use_cache
      (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (out: t_Slice i32)
      (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (t_Slice i32)
      (requires (Core_models.Slice.impl__len #i32 out <: usize) >=. mk_usize 16)
      (ensures
        fun out_future ->
          let out_future:t_Slice i32 = out_future in
          (Core_models.Slice.impl__len #i32 out_future <: usize) =.
          (Core_models.Slice.impl__len #i32 out <: usize))
