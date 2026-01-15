module Libcrux_iot_ml_kem.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

/// The SHA3 block size.
let v_BLOCK_SIZE: usize = mk_usize 168

/// The size of 3 SHA3 blocks.
let v_THREE_BLOCKS: usize = v_BLOCK_SIZE *! mk_usize 3

/// Abstraction for the hashing, to pick the fastest version depending on the
/// platform features available.
/// In libcrux-iot we currently support a portable instantiations of
/// this trait right now, whereas mainline libcrux supports additional
/// SIMD platform.
class t_Hash (v_Self: Type0) = {
  f_G_pre:input: t_Slice u8 -> output: t_Slice u8 -> pred: Type0{true ==> pred};
  f_G_post:input: t_Slice u8 -> output: t_Slice u8 -> output_future: t_Slice u8
    -> pred:
      Type0
        { pred ==>
          (Core.Slice.impl__len #u8 output_future <: usize) =.
          (Core.Slice.impl__len #u8 output <: usize) };
  f_G:x0: t_Slice u8 -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8) (f_G_pre x0 x1) (fun result -> f_G_post x0 x1 result);
  f_H_pre:input: t_Slice u8 -> output: t_Slice u8 -> pred: Type0{true ==> pred};
  f_H_post:input: t_Slice u8 -> output: t_Slice u8 -> output_future: t_Slice u8
    -> pred:
      Type0
        { pred ==>
          (Core.Slice.impl__len #u8 output_future <: usize) =.
          (Core.Slice.impl__len #u8 output <: usize) };
  f_H:x0: t_Slice u8 -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8) (f_H_pre x0 x1) (fun result -> f_H_post x0 x1 result);
  f_PRF_pre:v_LEN: usize -> input: t_Slice u8 -> out: t_Slice u8
    -> pred:
      Type0
        { v_LEN <=. (cast (Core.Num.impl_u32__MAX <: u32) <: usize) &&
          (Core.Slice.impl__len #u8 out <: usize) =. v_LEN ==>
          pred };
  f_PRF_post:v_LEN: usize -> input: t_Slice u8 -> out: t_Slice u8 -> out_future: t_Slice u8
    -> pred:
      Type0
        { pred ==>
          (Core.Slice.impl__len #u8 out_future <: usize) =. (Core.Slice.impl__len #u8 out <: usize)
        };
  f_PRF:v_LEN: usize -> x0: t_Slice u8 -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8) (f_PRF_pre v_LEN x0 x1) (fun result -> f_PRF_post v_LEN x0 x1 result);
  f_PRFxN_pre:input: t_Slice (t_Array u8 (mk_usize 33)) -> outputs: t_Slice u8 -> out_len: usize
    -> pred:
      Type0
        { ((Core.Slice.impl__len #(t_Array u8 (mk_usize 33)) input <: usize) =. mk_usize 2 ||
          (Core.Slice.impl__len #(t_Array u8 (mk_usize 33)) input <: usize) =. mk_usize 3 ||
          (Core.Slice.impl__len #(t_Array u8 (mk_usize 33)) input <: usize) =. mk_usize 4) &&
          out_len <=. (cast (Core.Num.impl_u32__MAX /! mk_u32 4 <: u32) <: usize) &&
          (Core.Slice.impl__len #u8 outputs <: usize) =.
          ((Core.Slice.impl__len #(t_Array u8 (mk_usize 33)) input <: usize) *! out_len <: usize) ==>
          pred };
  f_PRFxN_post:
      input: t_Slice (t_Array u8 (mk_usize 33)) ->
      outputs: t_Slice u8 ->
      out_len: usize ->
      outputs_future: t_Slice u8
    -> pred:
      Type0
        { pred ==>
          (Core.Slice.impl__len #u8 outputs_future <: usize) =.
          (Core.Slice.impl__len #u8 outputs <: usize) };
  f_PRFxN:x0: t_Slice (t_Array u8 (mk_usize 33)) -> x1: t_Slice u8 -> x2: usize
    -> Prims.Pure (t_Slice u8) (f_PRFxN_pre x0 x1 x2) (fun result -> f_PRFxN_post x0 x1 x2 result);
  f_shake128_init_absorb_final_pre:input: t_Slice (t_Array u8 (mk_usize 34))
    -> pred: Type0{true ==> pred};
  f_shake128_init_absorb_final_post:t_Slice (t_Array u8 (mk_usize 34)) -> v_Self -> Type0;
  f_shake128_init_absorb_final:x0: t_Slice (t_Array u8 (mk_usize 34))
    -> Prims.Pure v_Self
        (f_shake128_init_absorb_final_pre x0)
        (fun result -> f_shake128_init_absorb_final_post x0 result);
  f_shake128_squeeze_first_three_blocks_pre:
      self_: v_Self ->
      output: t_Slice (t_Array u8 (mk_usize 504))
    -> pred: Type0{true ==> pred};
  f_shake128_squeeze_first_three_blocks_post:
      v_Self ->
      t_Slice (t_Array u8 (mk_usize 504)) ->
      (v_Self & t_Slice (t_Array u8 (mk_usize 504)))
    -> Type0;
  f_shake128_squeeze_first_three_blocks:x0: v_Self -> x1: t_Slice (t_Array u8 (mk_usize 504))
    -> Prims.Pure (v_Self & t_Slice (t_Array u8 (mk_usize 504)))
        (f_shake128_squeeze_first_three_blocks_pre x0 x1)
        (fun result -> f_shake128_squeeze_first_three_blocks_post x0 x1 result);
  f_shake128_squeeze_next_block_pre:self_: v_Self -> output: t_Slice (t_Array u8 (mk_usize 168))
    -> pred: Type0{true ==> pred};
  f_shake128_squeeze_next_block_post:
      v_Self ->
      t_Slice (t_Array u8 (mk_usize 168)) ->
      (v_Self & t_Slice (t_Array u8 (mk_usize 168)))
    -> Type0;
  f_shake128_squeeze_next_block:x0: v_Self -> x1: t_Slice (t_Array u8 (mk_usize 168))
    -> Prims.Pure (v_Self & t_Slice (t_Array u8 (mk_usize 168)))
        (f_shake128_squeeze_next_block_pre x0 x1)
        (fun result -> f_shake128_squeeze_next_block_post x0 x1 result)
}
