module Libcrux_iot_ml_kem.Constant_time_ops
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

/// Return 1 if `value` is not zero and 0 otherwise.
val inz (value: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          if value =. mk_u8 0 then result =. mk_u8 0 else result =. mk_u8 1)

val is_non_zero (value: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          if value =. mk_u8 0 then result =. mk_u8 0 else result =. mk_u8 1)

/// Return 1 if the bytes of `lhs` and `rhs` do not exactly
/// match and 0 otherwise.
val compare (lhs rhs: t_Slice u8)
    : Prims.Pure u8
      (requires
        (Core_models.Slice.impl__len #u8 lhs <: usize) =.
        (Core_models.Slice.impl__len #u8 rhs <: usize))
      (ensures
        fun result ->
          let result:u8 = result in
          if lhs =. rhs then result =. mk_u8 0 else result =. mk_u8 1)

val compare_ciphertexts_in_constant_time (lhs rhs: t_Slice u8)
    : Prims.Pure u8
      (requires
        (Core_models.Slice.impl__len #u8 lhs <: usize) =.
        (Core_models.Slice.impl__len #u8 rhs <: usize))
      (ensures
        fun result ->
          let result:u8 = result in
          if lhs =. rhs then result =. mk_u8 0 else result =. mk_u8 1)

/// If `selector` is not zero, return the bytes in `rhs`; return the bytes in
/// `lhs` otherwise.
val select_ct (lhs rhs: t_Slice u8) (selector: u8) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 lhs <: usize) =.
        (Core_models.Slice.impl__len #u8 rhs <: usize) &&
        (Core_models.Slice.impl__len #u8 out <: usize) =.
        (Core_models.Slice.impl__len #u8 lhs <: usize))
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          if selector =. mk_u8 0 then out_future =. lhs else out_future =. rhs)

val select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 lhs <: usize) =.
        (Core_models.Slice.impl__len #u8 rhs <: usize) &&
        (Core_models.Slice.impl__len #u8 out <: usize) =.
        (Core_models.Slice.impl__len #u8 lhs <: usize))
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          if selector =. mk_u8 0 then out_future =. lhs else out_future =. rhs)

val compare_ciphertexts_select_shared_secret_in_constant_time
      (lhs_c rhs_c lhs_s rhs_s out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 lhs_c <: usize) =.
        (Core_models.Slice.impl__len #u8 rhs_c <: usize) &&
        (Core_models.Slice.impl__len #u8 lhs_s <: usize) =.
        (Core_models.Slice.impl__len #u8 rhs_s <: usize) &&
        (Core_models.Slice.impl__len #u8 out <: usize) =.
        (Core_models.Slice.impl__len #u8 lhs_s <: usize))
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          if lhs_c =. rhs_c then out_future =. lhs_s else out_future =. rhs_s)
