module Libcrux_iot_ml_kem.Vector.Traits.Spec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let add_pre (lhs rhs: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index lhs i) + v (Seq.index rhs i))

let add_post (lhs rhs result: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. i < 16 ==> (v (Seq.index result i) == v (Seq.index lhs i) + v (Seq.index rhs i))

let sub_pre (lhs rhs: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index lhs i) - v (Seq.index rhs i))

let sub_post (lhs rhs result: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. i < 16 ==> (v (Seq.index result i) == v (Seq.index lhs i) - v (Seq.index rhs i))

let negate_pre (vec: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index vec i))

let negate_post (vec result: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. i < 16 ==> v (Seq.index result i) == - (v (Seq.index vec i))

let multiply_by_constant_pre (vec: t_Array i16 (mk_usize 16)) (c: i16) : Hax_lib.Prop.t_Prop =
  forall i. i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index vec i) * v c)

let multiply_by_constant_post
      (vec: t_Array i16 (mk_usize 16))
      (c: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = forall i. v (Seq.index result i) == v (Seq.index vec i) * v c

let bitwise_and_with_constant_constant_post
      (vec: t_Array i16 (mk_usize 16))
      (c: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = result == Spec.Utils.map_array (fun x -> x &. c) vec

let shift_right_post
      (vec: t_Array i16 (mk_usize 16))
      (shift_by: i32)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop =
  (v shift_by >= 0 /\ v shift_by < 16) ==>
  result == Spec.Utils.map_array (fun x -> x >>! shift_by) vec

let cond_subtract_3329_pre (vec: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b_array (pow2 12 - 1) vec

let cond_subtract_3329_post (vec result: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  result ==
  Spec.Utils.map_array (fun x -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x) vec

let barrett_reduce_pre (vec: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b_array 28296 vec

let barrett_reduce_post (vec result: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b_array 3328 result /\
  (forall i. (v (Seq.index result i) % 3329) == (v (Seq.index vec i) % 3329))

let montgomery_multiply_by_constant_pre (vec: t_Array i16 (mk_usize 16)) (c: i16)
    : Hax_lib.Prop.t_Prop = Spec.Utils.is_i16b 1664 c

let montgomery_multiply_by_constant_post
      (vec: t_Array i16 (mk_usize 16))
      (c: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b_array 3328 result /\
  (forall i. ((v (Seq.index result i) % 3329) == (v (Seq.index vec i) * v c * 169) % 3329))

let compress_1_pre (vec: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. v (Seq.index vec i) >= 0 /\ v (Seq.index vec i) < 3329

let compress_1_post (vec result: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i. bounded (Seq.index result i) 1

let compress_pre (vec: t_Array i16 (mk_usize 16)) (coefficient_bits: i32) : Hax_lib.Prop.t_Prop =
  (v coefficient_bits == 4 \/ v coefficient_bits == 5 \/ v coefficient_bits == 10 \/
    v coefficient_bits == 11) /\ (forall i. v (Seq.index vec i) >= 0 /\ v (Seq.index vec i) < 3329)

let compress_post
      (vec: t_Array i16 (mk_usize 16))
      (coefficient_bits: i32)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop =
  (v coefficient_bits == 4 \/ v coefficient_bits == 5 \/ v coefficient_bits == 10 \/
    v coefficient_bits == 11) ==>
  (forall i. bounded (Seq.index result i) (v coefficient_bits))

let decompress_ciphertext_coefficient_pre (vec: t_Array i16 (mk_usize 16)) (coefficient_bits: i32)
    : Hax_lib.Prop.t_Prop =
  (v coefficient_bits == 4 \/ v coefficient_bits == 5 \/ v coefficient_bits == 10 \/
    v coefficient_bits == 11) /\
  (forall i. v (Seq.index vec i) >= 0 /\ v (Seq.index vec i) < pow2 (v coefficient_bits))
