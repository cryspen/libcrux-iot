module Libcrux_iot_ml_kem.Hash_functions.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

assume
val t_PortableHash': eqtype

let t_PortableHash = t_PortableHash'

assume
val shake128_init_absorb_final': input: t_Slice (t_Array u8 (mk_usize 34))
  -> Prims.Pure t_PortableHash Prims.l_True (fun _ -> Prims.l_True)

let shake128_init_absorb_final = shake128_init_absorb_final'

assume
val shake128_squeeze_first_three_blocks':
    state: t_PortableHash ->
    output: t_Slice (t_Array u8 (mk_usize 504))
  -> Prims.Pure (t_PortableHash & t_Slice (t_Array u8 (mk_usize 504)))
      Prims.l_True
      (fun _ -> Prims.l_True)

let shake128_squeeze_first_three_blocks = shake128_squeeze_first_three_blocks'

assume
val shake128_squeeze_next_block':
    state: t_PortableHash ->
    output: t_Slice (t_Array u8 (mk_usize 168))
  -> Prims.Pure (t_PortableHash & t_Slice (t_Array u8 (mk_usize 168)))
      Prims.l_True
      (fun _ -> Prims.l_True)

let shake128_squeeze_next_block = shake128_squeeze_next_block'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Libcrux_iot_ml_kem.Hash_functions.t_Hash t_PortableHash

let impl = impl'

assume
val v_G': input: t_Slice u8 -> output: t_Slice u8
  -> Prims.Pure (t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 output <: usize) =. mk_usize 64)
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          (Core_models.Slice.impl__len #u8 output_future <: usize) =.
          (Core_models.Slice.impl__len #u8 output <: usize))

let v_G = v_G'

assume
val v_H': input: t_Slice u8 -> output: t_Slice u8
  -> Prims.Pure (t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 output <: usize) =. mk_usize 32)
      (ensures
        fun output_future ->
          let output_future:t_Slice u8 = output_future in
          (Core_models.Slice.impl__len #u8 output_future <: usize) =.
          (Core_models.Slice.impl__len #u8 output <: usize))

let v_H = v_H'

assume
val v_PRF': v_LEN: usize -> input: t_Slice u8 -> out: t_Slice u8
  -> Prims.Pure (t_Slice u8)
      (requires
        v_LEN <=. (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize) &&
        (Core_models.Slice.impl__len #u8 out <: usize) =. v_LEN)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize))

let v_PRF (v_LEN: usize) = v_PRF' v_LEN

assume
val v_PRFxN': input: t_Slice (t_Array u8 (mk_usize 33)) -> outputs: t_Slice u8 -> out_len: usize
  -> Prims.Pure (t_Slice u8)
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

let v_PRFxN = v_PRFxN'
