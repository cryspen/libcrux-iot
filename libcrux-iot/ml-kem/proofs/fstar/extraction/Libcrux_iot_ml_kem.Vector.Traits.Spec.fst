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

let to_unsigned_representative_pre (vec: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b_array 3328 vec

let to_unsigned_representative_post (vec result: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i.
    let x = Seq.index vec i in
    let y = Seq.index result i in
    (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329))

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

let decompress_1_pre (vec: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  forall i.
    let x = Seq.index vec i in
    (x == mk_i16 0 \/ x == mk_i16 1)

let decompress_ciphertext_coefficient_pre (vec: t_Array i16 (mk_usize 16)) (coefficient_bits: i32)
    : Hax_lib.Prop.t_Prop =
  (v coefficient_bits == 4 \/ v coefficient_bits == 5 \/ v coefficient_bits == 10 \/
    v coefficient_bits == 11) /\
  (forall i. v (Seq.index vec i) >= 0 /\ v (Seq.index vec i) < pow2 (v coefficient_bits))

let ntt_layer_1_step_pre (vec: t_Array i16 (mk_usize 16)) (zeta0 zeta1 zeta2 zeta3: i16)
    : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ Spec.Utils.is_i16b 1664 zeta2 /\
  Spec.Utils.is_i16b 1664 zeta3 /\ Spec.Utils.is_i16b_array (11207 + 5 * 3328) vec

let ntt_layer_1_step_post
      (vec: t_Array i16 (mk_usize 16))
      (zeta0 zeta1 zeta2 zeta3: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Spec.Utils.is_i16b_array (11207 + 6 * 3328) result

let ntt_layer_2_step_pre (vec: t_Array i16 (mk_usize 16)) (zeta0 zeta1: i16) : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
  Spec.Utils.is_i16b_array (11207 + 4 * 3328) vec

let ntt_layer_2_step_post
      (vec: t_Array i16 (mk_usize 16))
      (zeta0 zeta1: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Spec.Utils.is_i16b_array (11207 + 5 * 3328) result

let ntt_layer_3_step_pre (vec: t_Array i16 (mk_usize 16)) (zeta0: i16) : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b_array (11207 + 3 * 3328) vec

let ntt_layer_3_step_post
      (vec: t_Array i16 (mk_usize 16))
      (zeta0: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Spec.Utils.is_i16b_array (11207 + 4 * 3328) result

let inv_ntt_layer_1_step_pre (vec: t_Array i16 (mk_usize 16)) (zeta0 zeta1 zeta2 zeta3: i16)
    : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ Spec.Utils.is_i16b 1664 zeta2 /\
  Spec.Utils.is_i16b 1664 zeta3 /\ Spec.Utils.is_i16b_array (4 * 3328) vec

let inv_ntt_layer_1_step_post
      (vec: t_Array i16 (mk_usize 16))
      (zeta0 zeta1 zeta2 zeta3: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Spec.Utils.is_i16b_array 3328 result

let inv_ntt_layer_2_step_pre (vec: t_Array i16 (mk_usize 16)) (zeta0 zeta1: i16)
    : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
  Spec.Utils.is_i16b_array 3328 vec

let inv_ntt_layer_2_step_post
      (vec: t_Array i16 (mk_usize 16))
      (zeta0 zeta1: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Spec.Utils.is_i16b_array 3328 result

let inv_ntt_layer_3_step_pre (vec: t_Array i16 (mk_usize 16)) (zeta0: i16) : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b_array 3328 vec

let inv_ntt_layer_3_step_post
      (vec: t_Array i16 (mk_usize 16))
      (zeta0: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Spec.Utils.is_i16b_array 3328 result

let ntt_multiply_pre (lhs rhs out: t_Array i16 (mk_usize 16)) (zeta0 zeta1 zeta2 zeta3: i16)
    : Hax_lib.Prop.t_Prop =
  Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ Spec.Utils.is_i16b 1664 zeta2 /\
  Spec.Utils.is_i16b 1664 zeta3 /\ Spec.Utils.is_i16b_array 3328 lhs /\
  Spec.Utils.is_i16b_array 3328 rhs

let ntt_multiply_post
      (lhs rhs out: t_Array i16 (mk_usize 16))
      (zeta0 zeta1 zeta2 zeta3: i16)
      (result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Spec.Utils.is_i16b_array 3328 result

let serialize_1_pre (vec: t_Array i16 (mk_usize 16)) (out: t_Slice u8) : Hax_lib.Prop.t_Prop =
  Seq.length out == 2 /\ Spec.MLKEM.serialize_pre 1 vec

let serialize_1_post (vec: t_Array i16 (mk_usize 16)) (out result: t_Slice u8) : Hax_lib.Prop.t_Prop =
  Seq.length result == 2 /\
  (Spec.MLKEM.serialize_pre 1 vec ==> Spec.MLKEM.serialize_post 1 vec result)

let deserialize_1_pre (input: t_Slice u8) (out: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  Seq.length input == 2

let deserialize_1_post (input: t_Slice u8) (out result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Seq.length input == 2 ==> Spec.MLKEM.deserialize_post 1 input result

let serialize_4_pre (vec: t_Array i16 (mk_usize 16)) (out: t_Slice u8) : Hax_lib.Prop.t_Prop =
  Seq.length out == 8 /\ Spec.MLKEM.serialize_pre 4 vec

let serialize_4_post (vec: t_Array i16 (mk_usize 16)) (out result: t_Slice u8) : Hax_lib.Prop.t_Prop =
  Seq.length result == 8 /\
  (Spec.MLKEM.serialize_pre 4 vec ==> Spec.MLKEM.serialize_post 4 vec result)

let deserialize_4_pre (input: t_Slice u8) (out: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  Seq.length input == 8

let deserialize_4_post (input: t_Slice u8) (out result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Seq.length input == 8 ==> Spec.MLKEM.deserialize_post 4 input result

let serialize_10_pre (vec: t_Array i16 (mk_usize 16)) (out: t_Slice u8) : Hax_lib.Prop.t_Prop =
  Seq.length out == 20 /\ Spec.MLKEM.serialize_pre 10 vec

let serialize_10_post (vec: t_Array i16 (mk_usize 16)) (out result: t_Slice u8)
    : Hax_lib.Prop.t_Prop =
  Seq.length result == 20 /\
  (Spec.MLKEM.serialize_pre 10 vec ==> Spec.MLKEM.serialize_post 10 vec result)

let deserialize_10_pre (input: t_Slice u8) (out: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  Seq.length input == 20

let deserialize_10_post (input: t_Slice u8) (out result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Seq.length input == 20 ==> Spec.MLKEM.deserialize_post 10 input result

let serialize_12_pre (vec: t_Array i16 (mk_usize 16)) (out: t_Slice u8) : Hax_lib.Prop.t_Prop =
  Seq.length out == 24 /\ Spec.MLKEM.serialize_pre 12 vec

let serialize_12_post (vec: t_Array i16 (mk_usize 16)) (out result: t_Slice u8)
    : Hax_lib.Prop.t_Prop =
  Seq.length result == 24 /\
  (Spec.MLKEM.serialize_pre 12 vec ==> Spec.MLKEM.serialize_post 12 vec result)

let deserialize_12_pre (input: t_Slice u8) (out: t_Array i16 (mk_usize 16)) : Hax_lib.Prop.t_Prop =
  Seq.length input == 24

let deserialize_12_post (input: t_Slice u8) (out result: t_Array i16 (mk_usize 16))
    : Hax_lib.Prop.t_Prop = Seq.length input == 24 ==> Spec.MLKEM.deserialize_post 12 input result
