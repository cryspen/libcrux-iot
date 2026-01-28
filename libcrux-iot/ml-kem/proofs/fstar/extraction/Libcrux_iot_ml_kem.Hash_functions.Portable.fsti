module Libcrux_iot_ml_kem.Hash_functions.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

/// The state.
/// It\'s only used for SHAKE128.
/// All other functions don\'t actually use any members.
val t_PortableHash:eqtype

val shake128_init_absorb_final (input: t_Slice (t_Array u8 (mk_usize 34)))
    : Prims.Pure t_PortableHash Prims.l_True (fun _ -> Prims.l_True)

val shake128_squeeze_first_three_blocks
      (state: t_PortableHash)
      (output: t_Slice (t_Array u8 (mk_usize 504)))
    : Prims.Pure (t_PortableHash & t_Slice (t_Array u8 (mk_usize 504)))
      Prims.l_True
      (fun _ -> Prims.l_True)

val shake128_squeeze_next_block
      (state: t_PortableHash)
      (output: t_Slice (t_Array u8 (mk_usize 168)))
    : Prims.Pure (t_PortableHash & t_Slice (t_Array u8 (mk_usize 168)))
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_iot_ml_kem.Hash_functions.t_Hash t_PortableHash

val v_G (input output: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 output <: usize) =. mk_usize 64)
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          (Core_models.Slice.impl__len #u8 output_future <: usize) =.
          (Core_models.Slice.impl__len #u8 output <: usize))

val v_H (input output: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 output <: usize) =. mk_usize 32)
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          (Core_models.Slice.impl__len #u8 output_future <: usize) =.
          (Core_models.Slice.impl__len #u8 output <: usize))

val v_PRF (v_LEN: usize) (input out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        v_LEN <=. (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize) &&
        (Core_models.Slice.impl__len #u8 out <: usize) =. v_LEN)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize))

val v_PRFxN (input: t_Slice (t_Array u8 (mk_usize 33))) (outputs: t_Slice u8) (out_len: usize)
    : Prims.Pure (t_Slice u8)
      (requires
        ((Core_models.Slice.impl__len #(t_Array u8 (mk_usize 33)) input <: usize) =. mk_usize 2 ||
        (Core_models.Slice.impl__len #(t_Array u8 (mk_usize 33)) input <: usize) =. mk_usize 3 ||
        (Core_models.Slice.impl__len #(t_Array u8 (mk_usize 33)) input <: usize) =. mk_usize 4) &&
        out_len <=. (cast (Core_models.Num.impl_u32__MAX /! mk_u32 4 <: u32) <: usize) &&
        (Core_models.Slice.impl__len #u8 outputs <: usize) =.
        ((Core_models.Slice.impl__len #(t_Array u8 (mk_usize 33)) input <: usize) *! out_len
          <:
          usize))
      (ensures
        fun outputs_future ->
          let outputs_future:t_Slice u8 = outputs_future in
          (Core_models.Slice.impl__len #u8 outputs_future <: usize) =.
          (Core_models.Slice.impl__len #u8 outputs <: usize))
