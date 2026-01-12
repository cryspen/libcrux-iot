module Libcrux_iot_ml_kem.Vector.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Portable.Vector_type in
  let open Libcrux_iot_ml_kem.Vector.Traits in
  let open Libcrux_secrets.Int.Classify_public in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_iot_ml_kem.Vector.Traits.t_Repr
Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
  {
    _super_250177790225314374 = FStar.Tactics.Typeclasses.solve;
    _super_14156401398203956914 = FStar.Tactics.Typeclasses.solve;
    f_repr_pre
    =
    (fun (self: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_repr_post
    =
    (fun
        (self: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: t_Array i16 (mk_usize 16))
        ->
        true);
    f_repr
    =
    fun (self: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
      let out:t_Array i16 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_i16 0) (mk_usize 16) in
      let out:t_Array i16 (mk_usize 16) =
        Libcrux_iot_ml_kem.Vector.Portable.Vector_type.to_i16_array self out
      in
      out
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_iot_ml_kem.Vector.Traits.t_Operations
Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
  {
    _super_250177790225314374 = FStar.Tactics.Typeclasses.solve;
    _super_14156401398203956914 = FStar.Tactics.Typeclasses.solve;
    _super_13976135183713343918 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post
    =
    (fun (_: Prims.unit) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        true);
    f_ZERO = (fun (_: Prims.unit) -> Libcrux_iot_ml_kem.Vector.Portable.Vector_type.zero ());
    f_from_i16_array_pre
    =
    (fun
        (array: t_Slice i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        (Core.Slice.impl__len #i16 array <: usize) =. mk_usize 16);
    f_from_i16_array_post
    =
    (fun
        (array: t_Slice i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_from_i16_array
    =
    (fun
        (array: t_Slice i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.from_i16_array array out
        in
        out);
    f_reducing_from_i32_array_pre
    =
    (fun
        (array: t_Slice i32)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        (Core.Slice.impl__len #i32 array <: usize) =. mk_usize 16);
    f_reducing_from_i32_array_post
    =
    (fun
        (array: t_Slice i32)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_reducing_from_i32_array
    =
    (fun
        (array: t_Slice i32)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.reducing_from_i32_array array out
        in
        out);
    f_to_i16_array_pre
    =
    (fun (x: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice i16) ->
        (Core.Slice.impl__len #i16 out <: usize) =. mk_usize 16);
    f_to_i16_array_post
    =
    (fun
        (x: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i16)
        (out1: t_Slice i16)
        ->
        true);
    f_to_i16_array
    =
    (fun (x: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice i16) ->
        let out:t_Slice i16 = Libcrux_iot_ml_kem.Vector.Portable.Vector_type.to_i16_array x out in
        out);
    f_from_bytes_pre
    =
    (fun
        (array: t_Slice u8)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        (Core.Slice.impl__len #u8 array <: usize) >=. mk_usize 32);
    f_from_bytes_post
    =
    (fun
        (array: t_Slice u8)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_from_bytes
    =
    (fun
        (array: t_Slice u8)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.from_bytes (Libcrux_secrets.Traits.f_classify_ref
                #(t_Slice u8)
                #FStar.Tactics.Typeclasses.solve
                array
              <:
              t_Slice u8)
            out
        in
        out);
    f_to_bytes_pre
    =
    (fun (x: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (bytes: t_Slice u8) ->
        (Core.Slice.impl__len #u8 bytes <: usize) >=. mk_usize 32);
    f_to_bytes_post
    =
    (fun
        (x: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (bytes: t_Slice u8)
        (bytes_future: t_Slice u8)
        ->
        (Core.Slice.impl__len #u8 bytes_future <: usize) =.
        (Core.Slice.impl__len #u8 bytes <: usize));
    f_to_bytes
    =
    (fun (x: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (bytes: t_Slice u8) ->
        let bytes:t_Slice u8 = Libcrux_iot_ml_kem.Vector.Portable.Vector_type.to_bytes x bytes in
        bytes);
    f_add_pre
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_add_post
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_add
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let lhs:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.add lhs rhs
        in
        lhs);
    f_sub_pre
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_sub_post
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_sub
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let lhs:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.sub lhs rhs
        in
        lhs);
    f_negate_pre
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_negate_post
    =
    (fun
        (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_negate
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.negate vec
        in
        vec);
    f_multiply_by_constant_pre
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) -> true);
    f_multiply_by_constant_post
    =
    (fun
        (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (c: i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_multiply_by_constant
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) ->
        let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.multiply_by_constant vec c
        in
        vec);
    f_bitwise_and_with_constant_pre
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) -> true);
    f_bitwise_and_with_constant_post
    =
    (fun
        (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (c: i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_bitwise_and_with_constant
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) ->
        let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.bitwise_and_with_constant vec c
        in
        vec);
    f_shift_right_pre
    =
    (fun (v_SHIFT_BY: i32) (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16);
    f_shift_right_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_shift_right
    =
    (fun (v_SHIFT_BY: i32) (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.shift_right v_SHIFT_BY vec
        in
        vec);
    f_cond_subtract_3329__pre
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_cond_subtract_3329__post
    =
    (fun
        (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_cond_subtract_3329_
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.cond_subtract_3329_ vec
        in
        vec);
    f_barrett_reduce_pre
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_barrett_reduce_post
    =
    (fun
        (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_barrett_reduce
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.barrett_reduce vec
        in
        vec);
    f_montgomery_multiply_by_constant_pre
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (r: i16) -> true);
    f_montgomery_multiply_by_constant_post
    =
    (fun
        (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (r: i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_montgomery_multiply_by_constant
    =
    (fun (vec: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (r: i16) ->
        let vec:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_by_constant vec
            (Libcrux_secrets.Traits.f_classify #i16 #FStar.Tactics.Typeclasses.solve r <: i16)
        in
        vec);
    f_compress_1__pre
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_compress_1__post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_compress_1_
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Compress.compress_1_ a
        in
        a);
    f_compress_pre
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        v_COEFFICIENT_BITS >=. mk_i32 0 && v_COEFFICIENT_BITS <=. mk_i32 16);
    f_compress_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_compress
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Compress.compress v_COEFFICIENT_BITS a
        in
        a);
    f_decompress_ciphertext_coefficient_pre
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        mk_i32 0 <=. v_COEFFICIENT_BITS && v_COEFFICIENT_BITS <. mk_i32 31);
    f_decompress_ciphertext_coefficient_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_decompress_ciphertext_coefficient
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Compress.decompress_ciphertext_coefficient v_COEFFICIENT_BITS
            a
        in
        a);
    f_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        true);
    f_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Ntt.ntt_layer_1_step a zeta0 zeta1 zeta2 zeta3
        in
        a);
    f_ntt_layer_2_step_pre
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        ->
        true);
    f_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_ntt_layer_2_step
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        ->
        let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Ntt.ntt_layer_2_step a zeta0 zeta1
        in
        a);
    f_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) -> true);
    f_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta: i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_ntt_layer_3_step
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) ->
        let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Ntt.ntt_layer_3_step a zeta
        in
        a);
    f_inv_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        true);
    f_inv_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_inv_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Ntt.inv_ntt_layer_1_step a zeta0 zeta1 zeta2 zeta3
        in
        a);
    f_inv_ntt_layer_2_step_pre
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        ->
        true);
    f_inv_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_inv_ntt_layer_2_step
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        ->
        let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Ntt.inv_ntt_layer_2_step a zeta0 zeta1
        in
        a);
    f_inv_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) -> true);
    f_inv_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta: i16)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_inv_ntt_layer_3_step
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) ->
        let a:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Ntt.inv_ntt_layer_3_step a zeta
        in
        a);
    f_accumulating_ntt_multiply_pre
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i32)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        (Core.Slice.impl__len #i32 out <: usize) >=. mk_usize 16);
    f_accumulating_ntt_multiply_post
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i32)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out_future: t_Slice i32)
        ->
        (Core.Slice.impl__len #i32 out_future <: usize) =. (Core.Slice.impl__len #i32 out <: usize));
    f_accumulating_ntt_multiply
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i32)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        let out:t_Slice i32 =
          Libcrux_iot_ml_kem.Vector.Portable.Ntt.accumulating_ntt_multiply lhs
            rhs
            out
            zeta0
            zeta1
            zeta2
            zeta3
        in
        out);
    f_accumulating_ntt_multiply_fill_cache_pre
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i32)
        (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        (Core.Slice.impl__len #i32 out <: usize) >=. mk_usize 16);
    f_accumulating_ntt_multiply_fill_cache_post
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i32)
        (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out_future, cache_future:
          (t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector))
        ->
        (Core.Slice.impl__len #i32 out_future <: usize) =. (Core.Slice.impl__len #i32 out <: usize));
    f_accumulating_ntt_multiply_fill_cache
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i32)
        (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        let tmp0, tmp1:(t_Slice i32 &
          Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
          Libcrux_iot_ml_kem.Vector.Portable.Ntt.accumulating_ntt_multiply_fill_cache lhs
            rhs
            out
            cache
            zeta0
            zeta1
            zeta2
            zeta3
        in
        let out:t_Slice i32 = tmp0 in
        let cache:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector = tmp1 in
        let _:Prims.unit = () in
        out, cache
        <:
        (t_Slice i32 & Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector));
    f_accumulating_ntt_multiply_use_cache_pre
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i32)
        (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        (Core.Slice.impl__len #i32 out <: usize) >=. mk_usize 16);
    f_accumulating_ntt_multiply_use_cache_post
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i32)
        (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out_future: t_Slice i32)
        ->
        (Core.Slice.impl__len #i32 out_future <: usize) =. (Core.Slice.impl__len #i32 out <: usize));
    f_accumulating_ntt_multiply_use_cache
    =
    (fun
        (lhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (rhs: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice i32)
        (cache: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        let out:t_Slice i32 =
          Libcrux_iot_ml_kem.Vector.Portable.Ntt.accumulating_ntt_multiply_use_cache lhs
            rhs
            out
            cache
        in
        out);
    f_serialize_1__pre
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 2);
    f_serialize_1__post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice u8)
        (out_future: t_Slice u8)
        ->
        (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 2);
    f_serialize_1_
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_iot_ml_kem.Vector.Portable.Serialize.serialize_1_ a out in
        out);
    f_deserialize_1__pre
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 2);
    f_deserialize_1__post
    =
    (fun
        (a: t_Slice u8)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_deserialize_1_
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Serialize.deserialize_1_ a out
        in
        out);
    f_serialize_4__pre
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 8);
    f_serialize_4__post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice u8)
        (out_future: t_Slice u8)
        ->
        (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 8);
    f_serialize_4_
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_iot_ml_kem.Vector.Portable.Serialize.serialize_4_ a out in
        out);
    f_deserialize_4__pre
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 8);
    f_deserialize_4__post
    =
    (fun
        (a: t_Slice u8)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_deserialize_4_
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Serialize.deserialize_4_ (Libcrux_secrets.Traits.f_classify_ref
                #(t_Slice u8)
                #FStar.Tactics.Typeclasses.solve
                a
              <:
              t_Slice u8)
            out
        in
        out);
    f_serialize_5__pre
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 10);
    f_serialize_5__post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice u8)
        (out_future: t_Slice u8)
        ->
        (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 10);
    f_serialize_5_
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_iot_ml_kem.Vector.Portable.Serialize.serialize_5_ a out in
        out);
    f_deserialize_5__pre
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 10);
    f_deserialize_5__post
    =
    (fun
        (a: t_Slice u8)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_deserialize_5_
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Serialize.deserialize_5_ (Libcrux_secrets.Traits.f_classify_ref
                #(t_Slice u8)
                #FStar.Tactics.Typeclasses.solve
                a
              <:
              t_Slice u8)
            out
        in
        out);
    f_serialize_10__pre
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 20);
    f_serialize_10__post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice u8)
        (out_future: t_Slice u8)
        ->
        (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 20);
    f_serialize_10_
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_iot_ml_kem.Vector.Portable.Serialize.serialize_10_ a out in
        out);
    f_deserialize_10__pre
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 20);
    f_deserialize_10__post
    =
    (fun
        (a: t_Slice u8)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_deserialize_10_
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Serialize.deserialize_10_ (Libcrux_secrets.Traits.f_classify_ref
                #(t_Slice u8)
                #FStar.Tactics.Typeclasses.solve
                a
              <:
              t_Slice u8)
            out
        in
        out);
    f_serialize_11__pre
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 22);
    f_serialize_11__post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice u8)
        (out_future: t_Slice u8)
        ->
        (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 22);
    f_serialize_11_
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_iot_ml_kem.Vector.Portable.Serialize.serialize_11_ a out in
        out);
    f_deserialize_11__pre
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 22);
    f_deserialize_11__post
    =
    (fun
        (a: t_Slice u8)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_deserialize_11_
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Serialize.deserialize_11_ (Libcrux_secrets.Traits.f_classify_ref
                #(t_Slice u8)
                #FStar.Tactics.Typeclasses.solve
                a
              <:
              t_Slice u8)
            out
        in
        out);
    f_serialize_12__pre
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 24);
    f_serialize_12__post
    =
    (fun
        (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Slice u8)
        (out_future: t_Slice u8)
        ->
        (Core.Slice.impl__len #u8 out_future <: usize) =. mk_usize 24);
    f_serialize_12_
    =
    (fun (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_iot_ml_kem.Vector.Portable.Serialize.serialize_12_ a out in
        out);
    f_deserialize_12__pre
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 24);
    f_deserialize_12__post
    =
    (fun
        (a: t_Slice u8)
        (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out1: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        ->
        true);
    f_deserialize_12_
    =
    (fun (a: t_Slice u8) (out: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
        let out:Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
          Libcrux_iot_ml_kem.Vector.Portable.Serialize.deserialize_12_ a out
        in
        out);
    f_rej_sample_pre
    =
    (fun (a: t_Slice u8) (out: t_Slice i16) ->
        (Core.Slice.impl__len #u8 a <: usize) =. mk_usize 24 &&
        (Core.Slice.impl__len #i16 out <: usize) =. mk_usize 16);
    f_rej_sample_post
    =
    (fun (a: t_Slice u8) (out: t_Slice i16) (out_future, result: (t_Slice i16 & usize)) ->
        result <=. mk_usize 16 && (Core.Slice.impl__len #i16 out_future <: usize) =. mk_usize 16);
    f_rej_sample
    =
    fun (a: t_Slice u8) (out: t_Slice i16) ->
      let tmp0, out1:(t_Slice i16 & usize) =
        Libcrux_iot_ml_kem.Vector.Portable.Sampling.rej_sample a out
      in
      let out:t_Slice i16 = tmp0 in
      let hax_temp_output:usize = out1 in
      out, hax_temp_output <: (t_Slice i16 & usize)
  }
