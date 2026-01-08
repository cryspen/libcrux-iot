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

let v_MONTGOMERY_SHIFT: u8 = mk_u8 16

let v_MONTGOMERY_R: i32 = mk_i32 1 <<! v_MONTGOMERY_SHIFT

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
let v_BARRETT_MULTIPLIER: i32 = mk_i32 20159

val get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32 (requires n <=. mk_u8 16) (fun _ -> Prims.l_True)

val add (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val sub (lhs rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val negate (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val multiply_by_constant
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val bitwise_and_with_constant
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val shift_right
      (v_SHIFT_BY: i32)
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16)
      (fun _ -> Prims.l_True)

/// Note: This function is not secret independent
/// Only use with public values.
val cond_subtract_3329_ (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Signed Barrett Reduction
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
/// Note: The input bound is 28296 to prevent overflow in the multiplication of quotient by FIELD_MODULUS
val barrett_reduce_element (value: i16) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val barrett_reduce (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Signed Montgomery Reduction
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
/// `|result| ≤ ceil(|value| / MONTGOMERY_R) + 1665
/// In particular, if `|value| ≤ FIELD_MODULUS-1 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS-1`.
/// And, if `|value| ≤ pow2 16 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS + 1664
val montgomery_reduce_element (value: i32) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

/// If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
val montgomery_multiply_fe_by_fer (fe fer: i16)
    : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant
      (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)
