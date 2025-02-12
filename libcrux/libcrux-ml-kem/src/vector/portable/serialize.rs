//! A module for serializing and deserializing PortableVector
//! Verification status: Lax

// A general style adopted here is to first define an internal function
// called serialize_N_int or deserialize_N_int that (de)serializes
// the minimal number of inputs K such that N*K is a multiple of 8.
// These functions are then called multiple times in the main function,
// called serialize_N or deserialize_N.
// This refactoring reduces redundancy, and also makes the code easier for
// F* to handle. As a general rule, any function that modifies an array
// more than 8 times with complex expressions starts to strain F*, so
// we separate out the code that does the computation (in _int functions)
// and code that updates arrays (in the outer functions).

use super::vector_type::*;

#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val serialize_1_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 1)) 
  (ensures bit_vec_of_int_t_array (${serialize_1} inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 1)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let serialize_1_lemma inputs =
  serialize_1_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${serialize_1} inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 1))

#pop-options
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let serialize_1_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 1))
   : squash (
     let inputs = bit_vec_of_int_t_array v 1 in
     let outputs = bit_vec_of_int_t_array (${serialize_1} ({ f_elements = v })) 8 in
     (forall (i: nat {i < 16}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[inline(always)]
pub(crate) fn serialize_1(v: [i16; 16]) -> [u8; 2] {
    let result0 = (v[0] as u8)
        | ((v[1] as u8) << 1)
        | ((v[2] as u8) << 2)
        | ((v[3] as u8) << 3)
        | ((v[4] as u8) << 4)
        | ((v[5] as u8) << 5)
        | ((v[6] as u8) << 6)
        | ((v[7] as u8) << 7);
    let result1 = (v[8] as u8)
        | ((v[9] as u8) << 1)
        | ((v[10] as u8) << 2)
        | ((v[11] as u8) << 3)
        | ((v[12] as u8) << 4)
        | ((v[13] as u8) << 5)
        | ((v[14] as u8) << 6)
        | ((v[15] as u8) << 7);
    [result0, result1]
}

//deserialize_1_bounded_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "
val deserialize_1_bounded_lemma (inputs: t_Array u8 (sz 2)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (${deserialize_1} inputs).f_elements i) 1)
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
let deserialize_1_bounded_lemma inputs =
  admit()
"
    )
)]
//deserialize_1_lemma
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val deserialize_1_lemma (inputs: t_Array u8 (sz 2)) : Lemma
  (ensures bit_vec_of_int_t_array (${deserialize_1} inputs).f_elements 1 == bit_vec_of_int_t_array inputs 8)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let deserialize_1_lemma inputs =
  deserialize_1_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${deserialize_1} inputs).f_elements 1) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options
"
    )
)]
//deserialize_1_bit_vec_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let deserialize_1_bit_vec_lemma (v: t_Array u8 (sz 2))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (${deserialize_1} v).f_elements 1 in
     (forall (i: nat {i < 16}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 2}
"#))]
#[inline(always)]
pub(crate) fn deserialize_1(v: &[u8]) -> UnpackedFieldElementArray {
    let result0 = (v[0] & 0x1) as i16;
    let result1 = ((v[0] >> 1) & 0x1) as i16;
    let result2 = ((v[0] >> 2) & 0x1) as i16;
    let result3 = ((v[0] >> 3) & 0x1) as i16;
    let result4 = ((v[0] >> 4) & 0x1) as i16;
    let result5 = ((v[0] >> 5) & 0x1) as i16;
    let result6 = ((v[0] >> 6) & 0x1) as i16;
    let result7 = ((v[0] >> 7) & 0x1) as i16;
    let result8 = (v[1] & 0x1) as i16;
    let result9 = ((v[1] >> 1) & 0x1) as i16;
    let result10 = ((v[1] >> 2) & 0x1) as i16;
    let result11 = ((v[1] >> 3) & 0x1) as i16;
    let result12 = ((v[1] >> 4) & 0x1) as i16;
    let result13 = ((v[1] >> 5) & 0x1) as i16;
    let result14 = ((v[1] >> 6) & 0x1) as i16;
    let result15 = ((v[1] >> 7) & 0x1) as i16;
    [
        result0, result1, result2, result3, result4, result5, result6, result7, result8, result9,
        result10, result11, result12, result13, result14, result15,
    ]
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 8}
"#))]
pub(crate) fn serialize_4_int(v: &[i16]) -> (u8, u8, u8, u8) {
    let result0 = ((v[1] as u8) << 4) | (v[0] as u8);
    let result1 = ((v[3] as u8) << 4) | (v[2] as u8);
    let result2 = ((v[5] as u8) << 4) | (v[4] as u8);
    let result3 = ((v[7] as u8) << 4) | (v[6] as u8);
    (result0, result1, result2, result3)
}

#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val serialize_4_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 4)) 
  (ensures bit_vec_of_int_t_array (${serialize_4} inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 4)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let serialize_4_lemma inputs =
  serialize_4_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${serialize_4} inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 4))

#pop-options
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let serialize_4_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 4))
   : squash (
     let inputs = bit_vec_of_int_t_array v 4 in
     let outputs = bit_vec_of_int_t_array (${serialize_4} ({ f_elements = v })) 8 in
     (forall (i: nat {i < 64}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[inline(always)]
pub(crate) fn serialize_4(v: UnpackedFieldElementArray) -> [u8; 8] {
    let result0_3 = serialize_4_int(&v[0..8]);
    let result4_7 = serialize_4_int(&v[8..16]);
    [
        result0_3.0,
        result0_3.1,
        result0_3.2,
        result0_3.3,
        result4_7.0,
        result4_7.1,
        result4_7.2,
        result4_7.3,
    ]
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 4}
"#))]
pub(crate) fn deserialize_4_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let v0 = (bytes[0] & 0x0F) as i16;
    let v1 = ((bytes[0] >> 4) & 0x0F) as i16;
    let v2 = (bytes[1] & 0x0F) as i16;
    let v3 = ((bytes[1] >> 4) & 0x0F) as i16;
    let v4 = (bytes[2] & 0x0F) as i16;
    let v5 = ((bytes[2] >> 4) & 0x0F) as i16;
    let v6 = (bytes[3] & 0x0F) as i16;
    let v7 = ((bytes[3] >> 4) & 0x0F) as i16;
    (v0, v1, v2, v3, v4, v5, v6, v7)
}

//deserialize_4_bounded_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "
val deserialize_4_bounded_lemma (inputs: t_Array u8 (sz 8)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (${deserialize_4} inputs).f_elements i) 4)
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
let deserialize_4_bounded_lemma inputs =
  admit()
"
    )
)]
//deserialize_4_lemma
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val deserialize_4_lemma (inputs: t_Array u8 (sz 8)) : Lemma
  (ensures bit_vec_of_int_t_array (${deserialize_4} inputs).f_elements 4 == bit_vec_of_int_t_array inputs 8)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let deserialize_4_lemma inputs =
  deserialize_4_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${deserialize_4} inputs).f_elements 4) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options
"
    )
)]
//deserialize_4_bit_vec_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let deserialize_4_bit_vec_lemma (v: t_Array u8 (sz 8))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (${deserialize_4} v).f_elements 4 in
     (forall (i: nat {i < 64}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 8}
"#))]
#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8]) -> UnpackedFieldElementArray {
    let v0_7 = deserialize_4_int(&bytes[0..4]);
    let v8_15 = deserialize_4_int(&bytes[4..8]);

        [
            v0_7.0, v0_7.1, v0_7.2, v0_7.3, v0_7.4, v0_7.5, v0_7.6, v0_7.7, v8_15.0, v8_15.1,
            v8_15.2, v8_15.3, v8_15.4, v8_15.5, v8_15.6, v8_15.7,
        ]

}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 8}
"#))]
pub(crate) fn serialize_5_int(v: &[i16]) -> (u8, u8, u8, u8, u8) {
    let r0 = (v[0] | v[1] << 5) as u8;
    let r1 = (v[1] >> 3 | v[2] << 2 | v[3] << 7) as u8;
    let r2 = (v[3] >> 1 | v[4] << 4) as u8;
    let r3 = (v[4] >> 4 | v[5] << 1 | v[6] << 6) as u8;
    let r4 = (v[6] >> 2 | v[7] << 3) as u8;
    (r0, r1, r2, r3, r4)
}

#[inline(always)]
pub(crate) fn serialize_5(v: UnpackedFieldElementArray) -> [u8; 10] {
    let r0_4 = serialize_5_int(&v[0..8]);
    let r5_9 = serialize_5_int(&v[8..16]);
    [
        r0_4.0, r0_4.1, r0_4.2, r0_4.3, r0_4.4, r5_9.0, r5_9.1, r5_9.2, r5_9.3, r5_9.4,
    ]
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 5}
"#))]
pub(crate) fn deserialize_5_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let v0 = (bytes[0] & 0x1F) as i16;
    let v1 = ((bytes[1] & 0x3) << 3 | (bytes[0] >> 5)) as i16;
    let v2 = ((bytes[1] >> 2) & 0x1F) as i16;
    let v3 = (((bytes[2] & 0xF) << 1) | (bytes[1] >> 7)) as i16;
    let v4 = (((bytes[3] & 1) << 4) | (bytes[2] >> 4)) as i16;
    let v5 = ((bytes[3] >> 1) & 0x1F) as i16;
    let v6 = (((bytes[4] & 0x7) << 2) | (bytes[3] >> 6)) as i16;
    let v7 = (bytes[4] >> 3) as i16;
    (v0, v1, v2, v3, v4, v5, v6, v7)
}

#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 10}
"#))]
#[inline(always)]
pub(crate) fn deserialize_5(bytes: &[u8]) -> UnpackedFieldElementArray {
    let v0_7 = deserialize_5_int(&bytes[0..5]);
    let v8_15 = deserialize_5_int(&bytes[5..10]);

[
            v0_7.0, v0_7.1, v0_7.2, v0_7.3, v0_7.4, v0_7.5, v0_7.6, v0_7.7, v8_15.0, v8_15.1,
            v8_15.2, v8_15.3, v8_15.4, v8_15.5, v8_15.6, v8_15.7,
        ]

}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 4}
"#))]
pub(crate) fn serialize_10_int(v: &[i16]) -> (u8, u8, u8, u8, u8) {
    let r0 = (v[0] & 0xFF) as u8;
    let r1 = ((v[1] & 0x3F) as u8) << 2 | ((v[0] >> 8) & 0x03) as u8;
    let r2 = ((v[2] & 0x0F) as u8) << 4 | ((v[1] >> 6) & 0x0F) as u8;
    let r3 = ((v[3] & 0x03) as u8) << 6 | ((v[2] >> 4) & 0x3F) as u8;
    let r4 = ((v[3] >> 2) & 0xFF) as u8;
    (r0, r1, r2, r3, r4)
}

#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val serialize_10_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 10)) 
  (ensures bit_vec_of_int_t_array (${serialize_10} inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 10)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let serialize_10_lemma inputs =
  serialize_10_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${serialize_10} inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 10))

#pop-options
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let serialize_10_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 10))
   : squash (
     let inputs = bit_vec_of_int_t_array v 10 in
     let outputs = bit_vec_of_int_t_array (${serialize_10} ({ f_elements = v })) 8 in
     (forall (i: nat {i < 160}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[inline(always)]
pub(crate) fn serialize_10(v: UnpackedFieldElementArray) -> [u8; 20] {
    let r0_4 = serialize_10_int(&v[0..4]);
    let r5_9 = serialize_10_int(&v[4..8]);
    let r10_14 = serialize_10_int(&v[8..12]);
    let r15_19 = serialize_10_int(&v[12..16]);
    [
        r0_4.0, r0_4.1, r0_4.2, r0_4.3, r0_4.4, r5_9.0, r5_9.1, r5_9.2, r5_9.3, r5_9.4, r10_14.0,
        r10_14.1, r10_14.2, r10_14.3, r10_14.4, r15_19.0, r15_19.1, r15_19.2, r15_19.3, r15_19.4,
    ]
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 10}
"#))]
pub(crate) fn deserialize_10_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let r0 = ((bytes[1] as i16 & 0x03) << 8 | (bytes[0] as i16 & 0xFF)) as i16;
    let r1 = ((bytes[2] as i16 & 0x0F) << 6 | (bytes[1] as i16 >> 2)) as i16;
    let r2 = ((bytes[3] as i16 & 0x3F) << 4 | (bytes[2] as i16 >> 4)) as i16;
    let r3 = (((bytes[4] as i16) << 2) | (bytes[3] as i16 >> 6)) as i16;
    let r4 = ((bytes[6] as i16 & 0x03) << 8 | (bytes[5] as i16 & 0xFF)) as i16;
    let r5 = ((bytes[7] as i16 & 0x0F) << 6 | (bytes[6] as i16 >> 2)) as i16;
    let r6 = ((bytes[8] as i16 & 0x3F) << 4 | (bytes[7] as i16 >> 4)) as i16;
    let r7 = (((bytes[9] as i16) << 2) | (bytes[8] as i16 >> 6)) as i16;
    (r0, r1, r2, r3, r4, r5, r6, r7)
}

//deserialize_10_bounded_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "
val deserialize_10_bounded_lemma (inputs: t_Array u8 (sz 20)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (${deserialize_10} inputs).f_elements i) 10)
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
let deserialize_10_bounded_lemma inputs =
  admit()
"
    )
)]
//deserialize_10_lemma
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val deserialize_10_lemma (inputs: t_Array u8 (sz 20)) : Lemma
  (ensures bit_vec_of_int_t_array (${deserialize_10} inputs).f_elements 10 == bit_vec_of_int_t_array inputs 8)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let deserialize_10_lemma inputs =
  deserialize_10_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${deserialize_10} inputs).f_elements 10) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options
"
    )
)]
//deserialize_10_bit_vec_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let deserialize_10_bit_vec_lemma (v: t_Array u8 (sz 20))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (${deserialize_10} v).f_elements 10 in
     (forall (i: nat {i < 160}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 20}
"#))]
#[inline(always)]
pub(crate) fn deserialize_10(bytes: &[u8]) -> UnpackedFieldElementArray {
    let v0_7 = deserialize_10_int(&bytes[0..10]);
    let v8_15 = deserialize_10_int(&bytes[10..20]);

        [
            v0_7.0, v0_7.1, v0_7.2, v0_7.3, v0_7.4, v0_7.5, v0_7.6, v0_7.7, v8_15.0, v8_15.1,
            v8_15.2, v8_15.3, v8_15.4, v8_15.5, v8_15.6, v8_15.7,
        ]
    
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 8}
"#))]
pub(crate) fn serialize_11_int(v: &[i16]) -> (u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8) {
    let r0 = v[0] as u8;
    let r1 = ((v[1] & 0x1F) as u8) << 3 | ((v[0] >> 8) as u8);
    let r2 = ((v[2] & 0x3) as u8) << 6 | ((v[1] >> 5) as u8);
    let r3 = ((v[2] >> 2) & 0xFF) as u8;
    let r4 = ((v[3] & 0x7F) as u8) << 1 | (v[2] >> 10) as u8;
    let r5 = ((v[4] & 0xF) as u8) << 4 | (v[3] >> 7) as u8;
    let r6 = ((v[5] & 0x1) as u8) << 7 | (v[4] >> 4) as u8;
    let r7 = ((v[5] >> 1) & 0xFF) as u8;
    let r8 = ((v[6] & 0x3F) as u8) << 2 | (v[5] >> 9) as u8;
    let r9 = ((v[7] & 0x7) as u8) << 5 | (v[6] >> 6) as u8;
    let r10 = (v[7] >> 3) as u8;
    (r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10)
}

#[inline(always)]
pub(crate) fn serialize_11(v: UnpackedFieldElementArray) -> [u8; 22] {
    let r0_10 = serialize_11_int(&v[0..8]);
    let r11_21 = serialize_11_int(&v[8..16]);
    [
        r0_10.0, r0_10.1, r0_10.2, r0_10.3, r0_10.4, r0_10.5, r0_10.6, r0_10.7, r0_10.8, r0_10.9,
        r0_10.10, r11_21.0, r11_21.1, r11_21.2, r11_21.3, r11_21.4, r11_21.5, r11_21.6, r11_21.7,
        r11_21.8, r11_21.9, r11_21.10,
    ]
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 11}
"#))]
pub(crate) fn deserialize_11_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let r0 = (bytes[1] as i16 & 0x7) << 8 | bytes[0] as i16;
    let r1 = (bytes[2] as i16 & 0x3F) << 5 | (bytes[1] as i16 >> 3);
    let r2 = (bytes[4] as i16 & 0x1) << 10 | ((bytes[3] as i16) << 2) | ((bytes[2] as i16) >> 6);
    let r3 = (bytes[5] as i16 & 0xF) << 7 | (bytes[4] as i16 >> 1);
    let r4 = (bytes[6] as i16 & 0x7F) << 4 | (bytes[5] as i16 >> 4);
    let r5 = (bytes[8] as i16 & 0x3) << 9 | ((bytes[7] as i16) << 1) | ((bytes[6] as i16) >> 7);
    let r6 = (bytes[9] as i16 & 0x1F) << 6 | (bytes[8] as i16 >> 2);
    let r7 = ((bytes[10] as i16) << 3) | (bytes[9] as i16 >> 5);
    (r0, r1, r2, r3, r4, r5, r6, r7)
}

#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 22}
"#))]
#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[u8]) -> UnpackedFieldElementArray {
    let v0_7 = deserialize_11_int(&bytes[0..11]);
    let v8_15 = deserialize_11_int(&bytes[11..22]);

        [
            v0_7.0, v0_7.1, v0_7.2, v0_7.3, v0_7.4, v0_7.5, v0_7.6, v0_7.7, v8_15.0, v8_15.1,
            v8_15.2, v8_15.3, v8_15.4, v8_15.5, v8_15.6, v8_15.7,
        ]
    
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 2}
"#))]
pub(crate) fn serialize_12_int(v: &[i16]) -> (u8, u8, u8) {
    let r0 = (v[0] & 0xFF) as u8;
    let r1 = ((v[0] >> 8) | ((v[1] & 0x0F) << 4)) as u8;
    let r2 = ((v[1] >> 4) & 0xFF) as u8;
    (r0, r1, r2)
}

#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val serialize_12_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 12)) 
  (ensures bit_vec_of_int_t_array (${serialize_12} inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 12)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let serialize_12_lemma inputs =
  serialize_12_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${serialize_12} inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 12))

#pop-options
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let serialize_12_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 12))
   : squash (
     let inputs = bit_vec_of_int_t_array v 12 in
     let outputs = bit_vec_of_int_t_array (${serialize_12} ({ f_elements = v })) 8 in
     (forall (i: nat {i < 192}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[inline(always)]
pub(crate) fn serialize_12(v: UnpackedFieldElementArray) -> [u8; 24] {
    let r0_2 = serialize_12_int(&v[0..2]);
    let r3_5 = serialize_12_int(&v[2..4]);
    let r6_8 = serialize_12_int(&v[4..6]);
    let r9_11 = serialize_12_int(&v[6..8]);
    let r12_14 = serialize_12_int(&v[8..10]);
    let r15_17 = serialize_12_int(&v[10..12]);
    let r18_20 = serialize_12_int(&v[12..14]);
    let r21_23 = serialize_12_int(&v[14..16]);
    [
        r0_2.0, r0_2.1, r0_2.2, r3_5.0, r3_5.1, r3_5.2, r6_8.0, r6_8.1, r6_8.2, r9_11.0, r9_11.1,
        r9_11.2, r12_14.0, r12_14.1, r12_14.2, r15_17.0, r15_17.1, r15_17.2, r18_20.0, r18_20.1,
        r18_20.2, r21_23.0, r21_23.1, r21_23.2,
    ]
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 3}
"#))]
pub(crate) fn deserialize_12_int(bytes: &[u8]) -> (i16, i16) {
    let byte0 = bytes[0] as i16;
    let byte1 = bytes[1] as i16;
    let byte2 = bytes[2] as i16;
    let r0 = (byte1 & 0x0F) << 8 | (byte0 & 0xFF);
    let r1 = (byte2 << 4) | ((byte1 >> 4) & 0x0F);
    (r0, r1)
}

//deserialize_12_bounded_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "
val deserialize_12_bounded_lemma (inputs: t_Array u8 (sz 24)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (${deserialize_12} inputs).f_elements i) 12)
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
let deserialize_12_bounded_lemma inputs =
  admit()
"
    )
)]
//deserialize_12_lemma
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val deserialize_12_lemma (inputs: t_Array u8 (sz 24)) : Lemma
  (ensures bit_vec_of_int_t_array (${deserialize_12} inputs).f_elements 12 == bit_vec_of_int_t_array inputs 8)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let deserialize_12_lemma inputs =
  deserialize_12_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${deserialize_12} inputs).f_elements 12) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options
"
    )
)]
//deserialize_12_bit_vec_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let deserialize_12_bit_vec_lemma (v: t_Array u8 (sz 24))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (${deserialize_12} v).f_elements 12 in
     (forall (i: nat {i < 192}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 24}
"#))]
#[inline(always)]
pub(crate) fn deserialize_12(bytes: &[u8]) -> UnpackedFieldElementArray {
    let v0_1 = deserialize_12_int(&bytes[0..3]);
    let v2_3 = deserialize_12_int(&bytes[3..6]);
    let v4_5 = deserialize_12_int(&bytes[6..9]);
    let v6_7 = deserialize_12_int(&bytes[9..12]);
    let v8_9 = deserialize_12_int(&bytes[12..15]);
    let v10_11 = deserialize_12_int(&bytes[15..18]);
    let v12_13 = deserialize_12_int(&bytes[18..21]);
    let v14_15 = deserialize_12_int(&bytes[21..24]);
         [
            v0_1.0, v0_1.1, v2_3.0, v2_3.1, v4_5.0, v4_5.1, v6_7.0, v6_7.1, v8_9.0, v8_9.1,
            v10_11.0, v10_11.1, v12_13.0, v12_13.1, v14_15.0, v14_15.1,
        ]
    }
