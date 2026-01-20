module Libcrux_iot_ml_kem.Vector.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = mk_i16 1353

let v_FIELD_MODULUS: i16 = mk_i16 3329

let v_FIELD_ELEMENTS_IN_VECTOR: usize = mk_usize 16

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = mk_u32 62209

let v_BARRETT_SHIFT: i32 = mk_i32 26

let v_BARRETT_R: i32 = mk_i32 1 <<! v_BARRETT_SHIFT

class t_Repr (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i1:Core_models.Clone.t_Clone v_Self;
  f_repr_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_repr_post:v_Self -> t_Array i16 (mk_usize 16) -> Type0;
  f_repr:x0: v_Self
    -> Prims.Pure (t_Array i16 (mk_usize 16)) (f_repr_pre x0) (fun result -> f_repr_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Repr v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Repr v_Self|} -> i._super_i1

class t_Operations (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i1:Core_models.Clone.t_Clone v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i2:t_Repr v_Self;
  f_ZERO_pre:x: Prims.unit
    -> pred:
      Type0
        { (let _:Prims.unit = x in
            true) ==>
          pred };
  f_ZERO_post:Prims.unit -> v_Self -> Type0;
  f_ZERO:x0: Prims.unit -> Prims.Pure v_Self (f_ZERO_pre x0) (fun result -> f_ZERO_post x0 result);
  f_from_i16_array_pre:array: t_Slice i16 -> out: v_Self
    -> pred: Type0{(Core_models.Slice.impl__len #i16 array <: usize) =. mk_usize 16 ==> pred};
  f_from_i16_array_post:t_Slice i16 -> v_Self -> v_Self -> Type0;
  f_from_i16_array:x0: t_Slice i16 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_from_i16_array_pre x0 x1)
        (fun result -> f_from_i16_array_post x0 x1 result);
  f_to_i16_array_pre:x: v_Self -> out: t_Slice i16
    -> pred: Type0{(Core_models.Slice.impl__len #i16 out <: usize) =. mk_usize 16 ==> pred};
  f_to_i16_array_post:v_Self -> t_Slice i16 -> t_Slice i16 -> Type0;
  f_to_i16_array:x0: v_Self -> x1: t_Slice i16
    -> Prims.Pure (t_Slice i16)
        (f_to_i16_array_pre x0 x1)
        (fun result -> f_to_i16_array_post x0 x1 result);
  f_reducing_from_i32_array_pre:array: t_Slice i32 -> out: v_Self
    -> pred: Type0{(Core_models.Slice.impl__len #i32 array <: usize) =. mk_usize 16 ==> pred};
  f_reducing_from_i32_array_post:t_Slice i32 -> v_Self -> v_Self -> Type0;
  f_reducing_from_i32_array:x0: t_Slice i32 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_reducing_from_i32_array_pre x0 x1)
        (fun result -> f_reducing_from_i32_array_post x0 x1 result);
  f_add_pre:lhs: v_Self -> rhs: v_Self -> pred: Type0{true ==> pred};
  f_add_post:v_Self -> v_Self -> v_Self -> Type0;
  f_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result);
  f_sub_pre:lhs: v_Self -> rhs: v_Self -> pred: Type0{true ==> pred};
  f_sub_post:v_Self -> v_Self -> v_Self -> Type0;
  f_sub:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_sub_pre x0 x1) (fun result -> f_sub_post x0 x1 result);
  f_negate_pre:vec: v_Self -> pred: Type0{true ==> pred};
  f_negate_post:v_Self -> v_Self -> Type0;
  f_negate:x0: v_Self -> Prims.Pure v_Self (f_negate_pre x0) (fun result -> f_negate_post x0 result);
  f_multiply_by_constant_pre:vec: v_Self -> c: i16 -> pred: Type0{true ==> pred};
  f_multiply_by_constant_post:v_Self -> i16 -> v_Self -> Type0;
  f_multiply_by_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_multiply_by_constant_pre x0 x1)
        (fun result -> f_multiply_by_constant_post x0 x1 result);
  f_bitwise_and_with_constant_pre:vec: v_Self -> c: i16 -> pred: Type0{true ==> pred};
  f_bitwise_and_with_constant_post:v_Self -> i16 -> v_Self -> Type0;
  f_bitwise_and_with_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_bitwise_and_with_constant_pre x0 x1)
        (fun result -> f_bitwise_and_with_constant_post x0 x1 result);
  f_shift_right_pre:v_SHIFT_BY: i32 -> vec: v_Self
    -> pred: Type0{v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16 ==> pred};
  f_shift_right_post:v_SHIFT_BY: i32 -> v_Self -> v_Self -> Type0;
  f_shift_right:v_SHIFT_BY: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_shift_right_pre v_SHIFT_BY x0)
        (fun result -> f_shift_right_post v_SHIFT_BY x0 result);
  f_cond_subtract_3329__pre:vec: v_Self -> pred: Type0{true ==> pred};
  f_cond_subtract_3329__post:v_Self -> v_Self -> Type0;
  f_cond_subtract_3329_:x0: v_Self
    -> Prims.Pure v_Self
        (f_cond_subtract_3329__pre x0)
        (fun result -> f_cond_subtract_3329__post x0 result);
  f_barrett_reduce_pre:vec: v_Self -> pred: Type0{true ==> pred};
  f_barrett_reduce_post:v_Self -> v_Self -> Type0;
  f_barrett_reduce:x0: v_Self
    -> Prims.Pure v_Self (f_barrett_reduce_pre x0) (fun result -> f_barrett_reduce_post x0 result);
  f_montgomery_multiply_by_constant_pre:vec: v_Self -> c: i16 -> pred: Type0{true ==> pred};
  f_montgomery_multiply_by_constant_post:v_Self -> i16 -> v_Self -> Type0;
  f_montgomery_multiply_by_constant:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_montgomery_multiply_by_constant_pre x0 x1)
        (fun result -> f_montgomery_multiply_by_constant_post x0 x1 result);
  f_compress_1__pre:vec: v_Self -> pred: Type0{true ==> pred};
  f_compress_1__post:v_Self -> v_Self -> Type0;
  f_compress_1_:x0: v_Self
    -> Prims.Pure v_Self (f_compress_1__pre x0) (fun result -> f_compress_1__post x0 result);
  f_compress_pre:v_COEFFICIENT_BITS: i32 -> vec: v_Self
    -> pred: Type0{v_COEFFICIENT_BITS >=. mk_i32 0 && v_COEFFICIENT_BITS <=. mk_i32 16 ==> pred};
  f_compress_post:v_COEFFICIENT_BITS: i32 -> v_Self -> v_Self -> Type0;
  f_compress:v_COEFFICIENT_BITS: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_compress_pre v_COEFFICIENT_BITS x0)
        (fun result -> f_compress_post v_COEFFICIENT_BITS x0 result);
  f_decompress_ciphertext_coefficient_pre:v_COEFFICIENT_BITS: i32 -> vec: v_Self
    -> pred: Type0{mk_i32 0 <=. v_COEFFICIENT_BITS && v_COEFFICIENT_BITS <. mk_i32 31 ==> pred};
  f_decompress_ciphertext_coefficient_post:v_COEFFICIENT_BITS: i32 -> v_Self -> v_Self -> Type0;
  f_decompress_ciphertext_coefficient:v_COEFFICIENT_BITS: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_decompress_ciphertext_coefficient_pre v_COEFFICIENT_BITS x0)
        (fun result -> f_decompress_ciphertext_coefficient_post v_COEFFICIENT_BITS x0 result);
  f_ntt_layer_1_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16 -> zeta2: i16 -> zeta3: i16
    -> pred: Type0{true ==> pred};
  f_ntt_layer_1_step_post:v_Self -> i16 -> i16 -> i16 -> i16 -> v_Self -> Type0;
  f_ntt_layer_1_step:x0: v_Self -> x1: i16 -> x2: i16 -> x3: i16 -> x4: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_1_step_pre x0 x1 x2 x3 x4)
        (fun result -> f_ntt_layer_1_step_post x0 x1 x2 x3 x4 result);
  f_ntt_layer_2_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16 -> pred: Type0{true ==> pred};
  f_ntt_layer_2_step_post:v_Self -> i16 -> i16 -> v_Self -> Type0;
  f_ntt_layer_2_step:x0: v_Self -> x1: i16 -> x2: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_2_step_pre x0 x1 x2)
        (fun result -> f_ntt_layer_2_step_post x0 x1 x2 result);
  f_ntt_layer_3_step_pre:a: v_Self -> zeta: i16 -> pred: Type0{true ==> pred};
  f_ntt_layer_3_step_post:v_Self -> i16 -> v_Self -> Type0;
  f_ntt_layer_3_step:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_ntt_layer_3_step_pre x0 x1)
        (fun result -> f_ntt_layer_3_step_post x0 x1 result);
  f_inv_ntt_layer_1_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16 -> zeta2: i16 -> zeta3: i16
    -> pred: Type0{true ==> pred};
  f_inv_ntt_layer_1_step_post:v_Self -> i16 -> i16 -> i16 -> i16 -> v_Self -> Type0;
  f_inv_ntt_layer_1_step:x0: v_Self -> x1: i16 -> x2: i16 -> x3: i16 -> x4: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_1_step_pre x0 x1 x2 x3 x4)
        (fun result -> f_inv_ntt_layer_1_step_post x0 x1 x2 x3 x4 result);
  f_inv_ntt_layer_2_step_pre:a: v_Self -> zeta0: i16 -> zeta1: i16 -> pred: Type0{true ==> pred};
  f_inv_ntt_layer_2_step_post:v_Self -> i16 -> i16 -> v_Self -> Type0;
  f_inv_ntt_layer_2_step:x0: v_Self -> x1: i16 -> x2: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_2_step_pre x0 x1 x2)
        (fun result -> f_inv_ntt_layer_2_step_post x0 x1 x2 result);
  f_inv_ntt_layer_3_step_pre:a: v_Self -> zeta: i16 -> pred: Type0{true ==> pred};
  f_inv_ntt_layer_3_step_post:v_Self -> i16 -> v_Self -> Type0;
  f_inv_ntt_layer_3_step:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self
        (f_inv_ntt_layer_3_step_pre x0 x1)
        (fun result -> f_inv_ntt_layer_3_step_post x0 x1 result);
  f_accumulating_ntt_multiply_pre:
      lhs: v_Self ->
      rhs: v_Self ->
      out: t_Slice i32 ->
      zeta0: i16 ->
      zeta1: i16 ->
      zeta2: i16 ->
      zeta3: i16
    -> pred: Type0{(Core_models.Slice.impl__len #i32 out <: usize) >=. mk_usize 16 ==> pred};
  f_accumulating_ntt_multiply_post:
      lhs: v_Self ->
      rhs: v_Self ->
      out: t_Slice i32 ->
      zeta0: i16 ->
      zeta1: i16 ->
      zeta2: i16 ->
      zeta3: i16 ->
      out_future: t_Slice i32
    -> pred:
      Type0
        { pred ==>
          (Core_models.Slice.impl__len #i32 out_future <: usize) =.
          (Core_models.Slice.impl__len #i32 out <: usize) };
  f_accumulating_ntt_multiply:
      x0: v_Self ->
      x1: v_Self ->
      x2: t_Slice i32 ->
      x3: i16 ->
      x4: i16 ->
      x5: i16 ->
      x6: i16
    -> Prims.Pure (t_Slice i32)
        (f_accumulating_ntt_multiply_pre x0 x1 x2 x3 x4 x5 x6)
        (fun result -> f_accumulating_ntt_multiply_post x0 x1 x2 x3 x4 x5 x6 result);
  f_accumulating_ntt_multiply_fill_cache_pre:
      lhs: v_Self ->
      rhs: v_Self ->
      out: t_Slice i32 ->
      cache: v_Self ->
      zeta0: i16 ->
      zeta1: i16 ->
      zeta2: i16 ->
      zeta3: i16
    -> pred: Type0{(Core_models.Slice.impl__len #i32 out <: usize) >=. mk_usize 16 ==> pred};
  f_accumulating_ntt_multiply_fill_cache_post:
      lhs: v_Self ->
      rhs: v_Self ->
      out: t_Slice i32 ->
      cache: v_Self ->
      zeta0: i16 ->
      zeta1: i16 ->
      zeta2: i16 ->
      zeta3: i16 ->
      x: (t_Slice i32 & v_Self)
    -> pred:
      Type0
        { pred ==>
          (let (out_future: t_Slice i32), (cache_future: v_Self) = x in
            (Core_models.Slice.impl__len #i32 out_future <: usize) =.
            (Core_models.Slice.impl__len #i32 out <: usize)) };
  f_accumulating_ntt_multiply_fill_cache:
      x0: v_Self ->
      x1: v_Self ->
      x2: t_Slice i32 ->
      x3: v_Self ->
      x4: i16 ->
      x5: i16 ->
      x6: i16 ->
      x7: i16
    -> Prims.Pure (t_Slice i32 & v_Self)
        (f_accumulating_ntt_multiply_fill_cache_pre x0 x1 x2 x3 x4 x5 x6 x7)
        (fun result -> f_accumulating_ntt_multiply_fill_cache_post x0 x1 x2 x3 x4 x5 x6 x7 result);
  f_accumulating_ntt_multiply_use_cache_pre:
      lhs: v_Self ->
      rhs: v_Self ->
      out: t_Slice i32 ->
      cache: v_Self
    -> pred: Type0{(Core_models.Slice.impl__len #i32 out <: usize) >=. mk_usize 16 ==> pred};
  f_accumulating_ntt_multiply_use_cache_post:
      lhs: v_Self ->
      rhs: v_Self ->
      out: t_Slice i32 ->
      cache: v_Self ->
      out_future: t_Slice i32
    -> pred:
      Type0
        { pred ==>
          (Core_models.Slice.impl__len #i32 out_future <: usize) =.
          (Core_models.Slice.impl__len #i32 out <: usize) };
  f_accumulating_ntt_multiply_use_cache:x0: v_Self -> x1: v_Self -> x2: t_Slice i32 -> x3: v_Self
    -> Prims.Pure (t_Slice i32)
        (f_accumulating_ntt_multiply_use_cache_pre x0 x1 x2 x3)
        (fun result -> f_accumulating_ntt_multiply_use_cache_post x0 x1 x2 x3 result);
  f_serialize_1__pre:a: v_Self -> out: t_Slice u8
    -> pred: Type0{(Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 2 ==> pred};
  f_serialize_1__post:a: v_Self -> out: t_Slice u8 -> out_future: t_Slice u8
    -> pred: Type0{pred ==> (Core_models.Slice.impl__len #u8 out_future <: usize) =. mk_usize 2};
  f_serialize_1_:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_serialize_1__pre x0 x1)
        (fun result -> f_serialize_1__post x0 x1 result);
  f_deserialize_1__pre:a: t_Slice u8 -> out: v_Self
    -> pred: Type0{(Core_models.Slice.impl__len #u8 a <: usize) =. mk_usize 2 ==> pred};
  f_deserialize_1__post:t_Slice u8 -> v_Self -> v_Self -> Type0;
  f_deserialize_1_:x0: t_Slice u8 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_deserialize_1__pre x0 x1)
        (fun result -> f_deserialize_1__post x0 x1 result);
  f_serialize_4__pre:a: v_Self -> out: t_Slice u8
    -> pred: Type0{(Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 8 ==> pred};
  f_serialize_4__post:a: v_Self -> out: t_Slice u8 -> out_future: t_Slice u8
    -> pred: Type0{pred ==> (Core_models.Slice.impl__len #u8 out_future <: usize) =. mk_usize 8};
  f_serialize_4_:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_serialize_4__pre x0 x1)
        (fun result -> f_serialize_4__post x0 x1 result);
  f_deserialize_4__pre:a: t_Slice u8 -> out: v_Self
    -> pred: Type0{(Core_models.Slice.impl__len #u8 a <: usize) =. mk_usize 8 ==> pred};
  f_deserialize_4__post:t_Slice u8 -> v_Self -> v_Self -> Type0;
  f_deserialize_4_:x0: t_Slice u8 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_deserialize_4__pre x0 x1)
        (fun result -> f_deserialize_4__post x0 x1 result);
  f_serialize_5__pre:a: v_Self -> out: t_Slice u8
    -> pred: Type0{(Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 10 ==> pred};
  f_serialize_5__post:a: v_Self -> out: t_Slice u8 -> out_future: t_Slice u8
    -> pred: Type0{pred ==> (Core_models.Slice.impl__len #u8 out_future <: usize) =. mk_usize 10};
  f_serialize_5_:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_serialize_5__pre x0 x1)
        (fun result -> f_serialize_5__post x0 x1 result);
  f_deserialize_5__pre:a: t_Slice u8 -> out: v_Self
    -> pred: Type0{(Core_models.Slice.impl__len #u8 a <: usize) =. mk_usize 10 ==> pred};
  f_deserialize_5__post:t_Slice u8 -> v_Self -> v_Self -> Type0;
  f_deserialize_5_:x0: t_Slice u8 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_deserialize_5__pre x0 x1)
        (fun result -> f_deserialize_5__post x0 x1 result);
  f_serialize_10__pre:a: v_Self -> out: t_Slice u8
    -> pred: Type0{(Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 20 ==> pred};
  f_serialize_10__post:a: v_Self -> out: t_Slice u8 -> out_future: t_Slice u8
    -> pred: Type0{pred ==> (Core_models.Slice.impl__len #u8 out_future <: usize) =. mk_usize 20};
  f_serialize_10_:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_serialize_10__pre x0 x1)
        (fun result -> f_serialize_10__post x0 x1 result);
  f_deserialize_10__pre:a: t_Slice u8 -> out: v_Self
    -> pred: Type0{(Core_models.Slice.impl__len #u8 a <: usize) =. mk_usize 20 ==> pred};
  f_deserialize_10__post:t_Slice u8 -> v_Self -> v_Self -> Type0;
  f_deserialize_10_:x0: t_Slice u8 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_deserialize_10__pre x0 x1)
        (fun result -> f_deserialize_10__post x0 x1 result);
  f_serialize_11__pre:a: v_Self -> out: t_Slice u8
    -> pred: Type0{(Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 22 ==> pred};
  f_serialize_11__post:a: v_Self -> out: t_Slice u8 -> out_future: t_Slice u8
    -> pred: Type0{pred ==> (Core_models.Slice.impl__len #u8 out_future <: usize) =. mk_usize 22};
  f_serialize_11_:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_serialize_11__pre x0 x1)
        (fun result -> f_serialize_11__post x0 x1 result);
  f_deserialize_11__pre:a: t_Slice u8 -> out: v_Self
    -> pred: Type0{(Core_models.Slice.impl__len #u8 a <: usize) =. mk_usize 22 ==> pred};
  f_deserialize_11__post:t_Slice u8 -> v_Self -> v_Self -> Type0;
  f_deserialize_11_:x0: t_Slice u8 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_deserialize_11__pre x0 x1)
        (fun result -> f_deserialize_11__post x0 x1 result);
  f_serialize_12__pre:a: v_Self -> out: t_Slice u8
    -> pred: Type0{(Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 24 ==> pred};
  f_serialize_12__post:a: v_Self -> out: t_Slice u8 -> out_future: t_Slice u8
    -> pred: Type0{pred ==> (Core_models.Slice.impl__len #u8 out_future <: usize) =. mk_usize 24};
  f_serialize_12_:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_serialize_12__pre x0 x1)
        (fun result -> f_serialize_12__post x0 x1 result);
  f_deserialize_12__pre:a: t_Slice u8 -> out: v_Self
    -> pred: Type0{(Core_models.Slice.impl__len #u8 a <: usize) =. mk_usize 24 ==> pred};
  f_deserialize_12__post:t_Slice u8 -> v_Self -> v_Self -> Type0;
  f_deserialize_12_:x0: t_Slice u8 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_deserialize_12__pre x0 x1)
        (fun result -> f_deserialize_12__post x0 x1 result);
  f_rej_sample_pre:a: t_Slice u8 -> out: t_Slice i16
    -> pred:
      Type0
        { (Core_models.Slice.impl__len #u8 a <: usize) =. mk_usize 24 &&
          (Core_models.Slice.impl__len #i16 out <: usize) =. mk_usize 16 ==>
          pred };
  f_rej_sample_post:a: t_Slice u8 -> out: t_Slice i16 -> x: (t_Slice i16 & usize)
    -> pred:
      Type0
        { pred ==>
          (let (out_future: t_Slice i16), (result: usize) = x in
            result <=. mk_usize 16 &&
            (Core_models.Slice.impl__len #i16 out_future <: usize) =. mk_usize 16) };
  f_rej_sample:x0: t_Slice u8 -> x1: t_Slice i16
    -> Prims.Pure (t_Slice i16 & usize)
        (f_rej_sample_pre x0 x1)
        (fun result -> f_rej_sample_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Operations v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Operations v_Self|} -> i._super_i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Operations v_Self|} -> i._super_i2

let montgomery_multiply_fe
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Operations v_T)
      (v: v_T)
      (fer: i16)
    : v_T =
  let v:v_T = f_montgomery_multiply_by_constant #v_T #FStar.Tactics.Typeclasses.solve v fer in
  v

let to_standard_domain
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Operations v_T)
      (v: v_T)
    : v_T =
  let v:v_T =
    f_montgomery_multiply_by_constant #v_T
      #FStar.Tactics.Typeclasses.solve
      v
      v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS
  in
  v

let to_unsigned_representative
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Operations v_T)
      (a out: v_T)
    : v_T =
  let out:v_T = a in
  let out:v_T = f_shift_right #v_T #FStar.Tactics.Typeclasses.solve (mk_i32 15) out in
  let out:v_T =
    f_bitwise_and_with_constant #v_T #FStar.Tactics.Typeclasses.solve out v_FIELD_MODULUS
  in
  let out:v_T = f_add #v_T #FStar.Tactics.Typeclasses.solve out a in
  out

let decompress_1_
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Operations v_T)
      (vec: v_T)
    : v_T =
  let vec:v_T = f_negate #v_T #FStar.Tactics.Typeclasses.solve vec in
  let vec:v_T =
    f_bitwise_and_with_constant #v_T #FStar.Tactics.Typeclasses.solve vec (mk_i16 1665)
  in
  vec
