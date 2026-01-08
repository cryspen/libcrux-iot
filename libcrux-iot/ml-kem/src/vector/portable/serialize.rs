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
use libcrux_secrets::*;

#[hax_lib::requires(out.len() == 2)]
#[hax_lib::ensures(|_| future(out).len() == 2)]
#[inline(always)]
pub(crate) fn serialize_1(v: &PortableVector, out: &mut [U8]) {
    #[cfg(not(eurydice))]
    debug_assert!(out.len() == 2);

    out[0] = (v.elements[0].as_u8())
        | ((v.elements[1].as_u8()) << 1)
        | ((v.elements[2].as_u8()) << 2)
        | ((v.elements[3].as_u8()) << 3)
        | ((v.elements[4].as_u8()) << 4)
        | ((v.elements[5].as_u8()) << 5)
        | ((v.elements[6].as_u8()) << 6)
        | ((v.elements[7].as_u8()) << 7);

    out[1] = (v.elements[8].as_u8())
        | ((v.elements[9].as_u8()) << 1)
        | ((v.elements[10].as_u8()) << 2)
        | ((v.elements[11].as_u8()) << 3)
        | ((v.elements[12].as_u8()) << 4)
        | ((v.elements[13].as_u8()) << 5)
        | ((v.elements[14].as_u8()) << 6)
        | ((v.elements[15].as_u8()) << 7);
}

//deserialize_1_bit_vec_lemma

#[hax_lib::requires(v.len() == 2)]
#[inline(always)]
pub(crate) fn deserialize_1(v: &[U8], out: &mut PortableVector) {
    out.elements[0] = (v[0] & 0x1).as_i16();
    out.elements[1] = ((v[0] >> 1) & 0x1).as_i16();
    out.elements[2] = ((v[0] >> 2) & 0x1).as_i16();
    out.elements[3] = ((v[0] >> 3) & 0x1).as_i16();
    out.elements[4] = ((v[0] >> 4) & 0x1).as_i16();
    out.elements[5] = ((v[0] >> 5) & 0x1).as_i16();
    out.elements[6] = ((v[0] >> 6) & 0x1).as_i16();
    out.elements[7] = ((v[0] >> 7) & 0x1).as_i16();
    out.elements[8] = (v[1] & 0x1).as_i16();
    out.elements[9] = ((v[1] >> 1) & 0x1).as_i16();
    out.elements[10] = ((v[1] >> 2) & 0x1).as_i16();
    out.elements[11] = ((v[1] >> 3) & 0x1).as_i16();
    out.elements[12] = ((v[1] >> 4) & 0x1).as_i16();
    out.elements[13] = ((v[1] >> 5) & 0x1).as_i16();
    out.elements[14] = ((v[1] >> 6) & 0x1).as_i16();
    out.elements[15] = ((v[1] >> 7) & 0x1).as_i16();
}

#[hax_lib::requires(v.len() == 8)]
#[inline(always)]
pub(crate) fn serialize_4_int(v: &[I16]) -> (u8, u8, u8, u8) {
    let result0 = ((v[1].as_u8()) << 4) | (v[0].as_u8());
    let result1 = ((v[3].as_u8()) << 4) | (v[2].as_u8());
    let result2 = ((v[5].as_u8()) << 4) | (v[4].as_u8());
    let result3 = ((v[7].as_u8()) << 4) | (v[6].as_u8());
    (
        result0.declassify(),
        result1.declassify(),
        result2.declassify(),
        result3.declassify(),
    )
}

#[hax_lib::requires(out.len() == 8)]
#[hax_lib::ensures(|_| future(out).len() == 8)]
#[inline(always)]
pub(crate) fn serialize_4(v: &PortableVector, out: &mut [u8]) {
    #[cfg(not(eurydice))]
    debug_assert!(out.len() == 8);
    (out[0], out[1], out[2], out[3]) = serialize_4_int(&v.elements[0..8]);
    (out[4], out[5], out[6], out[7]) = serialize_4_int(&v.elements[8..16]);
}

#[hax_lib::requires(bytes.len() == 4)]
#[inline(always)]
pub(crate) fn deserialize_4_int(bytes: &[U8]) -> (I16, I16, I16, I16, I16, I16, I16, I16) {
    let v0 = (bytes[0] & 0x0F).as_i16();
    let v1 = ((bytes[0] >> 4) & 0x0F).as_i16();
    let v2 = (bytes[1] & 0x0F).as_i16();
    let v3 = ((bytes[1] >> 4) & 0x0F).as_i16();
    let v4 = (bytes[2] & 0x0F).as_i16();
    let v5 = ((bytes[2] >> 4) & 0x0F).as_i16();
    let v6 = (bytes[3] & 0x0F).as_i16();
    let v7 = ((bytes[3] >> 4) & 0x0F).as_i16();
    (v0, v1, v2, v3, v4, v5, v6, v7)
}

#[hax_lib::requires(bytes.len() == 8)]
#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[U8], out: &mut PortableVector) {
    (
        out.elements[0],
        out.elements[1],
        out.elements[2],
        out.elements[3],
        out.elements[4],
        out.elements[5],
        out.elements[6],
        out.elements[7],
    ) = deserialize_4_int(&bytes[0..4]);
    (
        out.elements[8],
        out.elements[9],
        out.elements[10],
        out.elements[11],
        out.elements[12],
        out.elements[13],
        out.elements[14],
        out.elements[15],
    ) = deserialize_4_int(&bytes[4..8]);
}

#[hax_lib::requires(v.len() == 8)]
#[inline(always)]
pub(crate) fn serialize_5_int(v: &[I16]) -> (u8, u8, u8, u8, u8) {
    let r0 = (v[0] | v[1] << 5).as_u8();
    let r1 = (v[1] >> 3 | v[2] << 2 | v[3] << 7).as_u8();
    let r2 = (v[3] >> 1 | v[4] << 4).as_u8();
    let r3 = (v[4] >> 4 | v[5] << 1 | v[6] << 6).as_u8();
    let r4 = (v[6] >> 2 | v[7] << 3).as_u8();
    (
        r0.declassify(),
        r1.declassify(),
        r2.declassify(),
        r3.declassify(),
        r4.declassify(),
    )
}

#[hax_lib::requires(out.len() == 10)]
#[hax_lib::ensures(|_| future(out).len() == 10)]
#[inline(always)]
pub(crate) fn serialize_5(v: &PortableVector, out: &mut [u8]) {
    #[cfg(not(eurydice))]
    debug_assert!(out.len() == 10);
    (out[0], out[1], out[2], out[3], out[4]) = serialize_5_int(&v.elements[0..8]);
    (out[5], out[6], out[7], out[8], out[9]) = serialize_5_int(&v.elements[8..16]);
}

#[hax_lib::requires(bytes.len() == 5)]
#[inline(always)]
pub(crate) fn deserialize_5_int(bytes: &[U8]) -> (I16, I16, I16, I16, I16, I16, I16, I16) {
    let v0 = (bytes[0] & 0x1F).as_i16();
    let v1 = ((bytes[1] & 0x3) << 3 | (bytes[0] >> 5)).as_i16();
    let v2 = ((bytes[1] >> 2) & 0x1F).as_i16();
    let v3 = (((bytes[2] & 0xF) << 1) | (bytes[1] >> 7)).as_i16();
    let v4 = (((bytes[3] & 1) << 4) | (bytes[2] >> 4)).as_i16();
    let v5 = ((bytes[3] >> 1) & 0x1F).as_i16();
    let v6 = (((bytes[4] & 0x7) << 2) | (bytes[3] >> 6)).as_i16();
    let v7 = (bytes[4] >> 3).as_i16();
    (v0, v1, v2, v3, v4, v5, v6, v7)
}

#[hax_lib::requires(bytes.len() == 10)]
#[inline(always)]
pub(crate) fn deserialize_5(bytes: &[U8], out: &mut PortableVector) {
    (
        out.elements[0],
        out.elements[1],
        out.elements[2],
        out.elements[3],
        out.elements[4],
        out.elements[5],
        out.elements[6],
        out.elements[7],
    ) = deserialize_5_int(&bytes[0..5]);
    (
        out.elements[8],
        out.elements[9],
        out.elements[10],
        out.elements[11],
        out.elements[12],
        out.elements[13],
        out.elements[14],
        out.elements[15],
    ) = deserialize_5_int(&bytes[5..10]);
}

#[hax_lib::requires(v.len() == 4)]
#[inline(always)]
pub(crate) fn serialize_10_int(v: &[I16]) -> (u8, u8, u8, u8, u8) {
    let r0 = (v[0] & 0xFF).as_u8();
    let r1 = ((v[1] & 0x3F).as_u8()) << 2 | ((v[0] >> 8) & 0x03).as_u8();
    let r2 = ((v[2] & 0x0F).as_u8()) << 4 | ((v[1] >> 6) & 0x0F).as_u8();
    let r3 = ((v[3] & 0x03).as_u8()) << 6 | ((v[2] >> 4) & 0x3F).as_u8();
    let r4 = ((v[3] >> 2) & 0xFF).as_u8();
    (
        r0.declassify(),
        r1.declassify(),
        r2.declassify(),
        r3.declassify(),
        r4.declassify(),
    )
}

#[hax_lib::requires(out.len() == 20)]
#[hax_lib::ensures(|_| future(out).len() == 20)]
#[inline(always)]
pub(crate) fn serialize_10(v: &PortableVector, out: &mut [u8]) {
    #[cfg(not(eurydice))]
    debug_assert!(out.len() == 20);
    (out[0], out[1], out[2], out[3], out[4]) = serialize_10_int(&v.elements[0..4]);
    (out[5], out[6], out[7], out[8], out[9]) = serialize_10_int(&v.elements[4..8]);
    (out[10], out[11], out[12], out[13], out[14]) = serialize_10_int(&v.elements[8..12]);
    (out[15], out[16], out[17], out[18], out[19]) = serialize_10_int(&v.elements[12..16]);
}

#[hax_lib::requires(bytes.len() == 10)]
#[inline(always)]
pub(crate) fn deserialize_10_int(bytes: &[U8]) -> (I16, I16, I16, I16, I16, I16, I16, I16) {
    let r0 = ((bytes[1].as_i16() & 0x03) << 8 | (bytes[0].as_i16() & 0xFF)).as_i16();
    let r1 = ((bytes[2].as_i16() & 0x0F) << 6 | (bytes[1].as_i16() >> 2)).as_i16();
    let r2 = ((bytes[3].as_i16() & 0x3F) << 4 | (bytes[2].as_i16() >> 4)).as_i16();
    let r3 = (((bytes[4].as_i16()) << 2) | (bytes[3].as_i16() >> 6)).as_i16();
    let r4 = ((bytes[6].as_i16() & 0x03) << 8 | (bytes[5].as_i16() & 0xFF)).as_i16();
    let r5 = ((bytes[7].as_i16() & 0x0F) << 6 | (bytes[6].as_i16() >> 2)).as_i16();
    let r6 = ((bytes[8].as_i16() & 0x3F) << 4 | (bytes[7].as_i16() >> 4)).as_i16();
    let r7 = (((bytes[9].as_i16()) << 2) | (bytes[8].as_i16() >> 6)).as_i16();
    (r0, r1, r2, r3, r4, r5, r6, r7)
}

#[hax_lib::requires(bytes.len() == 20)]
#[inline(always)]
pub(crate) fn deserialize_10(bytes: &[U8], out: &mut PortableVector) {
    (
        out.elements[0],
        out.elements[1],
        out.elements[2],
        out.elements[3],
        out.elements[4],
        out.elements[5],
        out.elements[6],
        out.elements[7],
    ) = deserialize_10_int(&bytes[0..10]);
    (
        out.elements[8],
        out.elements[9],
        out.elements[10],
        out.elements[11],
        out.elements[12],
        out.elements[13],
        out.elements[14],
        out.elements[15],
    ) = deserialize_10_int(&bytes[10..20]);
}

#[hax_lib::requires(v.len() == 8)]
#[inline(always)]
pub(crate) fn serialize_11_int(v: &[I16]) -> (u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8) {
    let r0 = v[0].as_u8();
    let r1 = ((v[1] & 0x1F).as_u8()) << 3 | ((v[0] >> 8).as_u8());
    let r2 = ((v[2] & 0x3).as_u8()) << 6 | ((v[1] >> 5).as_u8());
    let r3 = ((v[2] >> 2) & 0xFF).as_u8();
    let r4 = ((v[3] & 0x7F).as_u8()) << 1 | (v[2] >> 10).as_u8();
    let r5 = ((v[4] & 0xF).as_u8()) << 4 | (v[3] >> 7).as_u8();
    let r6 = ((v[5] & 0x1).as_u8()) << 7 | (v[4] >> 4).as_u8();
    let r7 = ((v[5] >> 1) & 0xFF).as_u8();
    let r8 = ((v[6] & 0x3F).as_u8()) << 2 | (v[5] >> 9).as_u8();
    let r9 = ((v[7] & 0x7).as_u8()) << 5 | (v[6] >> 6).as_u8();
    let r10 = (v[7] >> 3).as_u8();
    (
        r0.declassify(),
        r1.declassify(),
        r2.declassify(),
        r3.declassify(),
        r4.declassify(),
        r5.declassify(),
        r6.declassify(),
        r7.declassify(),
        r8.declassify(),
        r9.declassify(),
        r10.declassify(),
    )
}

#[hax_lib::requires(out.len() == 22)]
#[hax_lib::ensures(|_| future(out).len() == 22)]
#[inline(always)]
pub(crate) fn serialize_11(v: &PortableVector, out: &mut [u8]) {
    #[cfg(not(eurydice))]
    debug_assert!(out.len() == 22);
    (
        out[0], out[1], out[2], out[3], out[4], out[5], out[6], out[7], out[8], out[9], out[10],
    ) = serialize_11_int(&v.elements[0..8]);
    (
        out[11], out[12], out[13], out[14], out[15], out[16], out[17], out[18], out[19], out[20],
        out[21],
    ) = serialize_11_int(&v.elements[8..16]);
}

#[hax_lib::requires(bytes.len() == 11)]
#[inline(always)]
pub(crate) fn deserialize_11_int(bytes: &[U8]) -> (I16, I16, I16, I16, I16, I16, I16, I16) {
    let r0 = (bytes[1].as_i16() & 0x7) << 8 | bytes[0].as_i16();
    let r1 = (bytes[2].as_i16() & 0x3F) << 5 | (bytes[1].as_i16() >> 3);
    let r2 =
        (bytes[4].as_i16() & 0x1) << 10 | ((bytes[3].as_i16()) << 2) | ((bytes[2].as_i16()) >> 6);
    let r3 = (bytes[5].as_i16() & 0xF) << 7 | (bytes[4].as_i16() >> 1);
    let r4 = (bytes[6].as_i16() & 0x7F) << 4 | (bytes[5].as_i16() >> 4);
    let r5 =
        (bytes[8].as_i16() & 0x3) << 9 | ((bytes[7].as_i16()) << 1) | ((bytes[6].as_i16()) >> 7);
    let r6 = (bytes[9].as_i16() & 0x1F) << 6 | (bytes[8].as_i16() >> 2);
    let r7 = ((bytes[10].as_i16()) << 3) | (bytes[9].as_i16() >> 5);
    (r0, r1, r2, r3, r4, r5, r6, r7)
}

#[hax_lib::requires(bytes.len() == 22)]
#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[U8], out: &mut PortableVector) {
    (
        out.elements[0],
        out.elements[1],
        out.elements[2],
        out.elements[3],
        out.elements[4],
        out.elements[5],
        out.elements[6],
        out.elements[7],
    ) = deserialize_11_int(&bytes[0..11]);
    (
        out.elements[8],
        out.elements[9],
        out.elements[10],
        out.elements[11],
        out.elements[12],
        out.elements[13],
        out.elements[14],
        out.elements[15],
    ) = deserialize_11_int(&bytes[11..22]);
}

#[hax_lib::requires(v.len() == 2)]
#[inline(always)]
pub(crate) fn serialize_12_int(v: &[I16]) -> (U8, U8, U8) {
    let r0 = (v[0] & 0xFF).as_u8();
    let r1 = ((v[0] >> 8) | ((v[1] & 0x0F) << 4)).as_u8();
    let r2 = ((v[1] >> 4) & 0xFF).as_u8();
    (r0, r1, r2)
}

#[hax_lib::requires(out.len() == 24)]
#[hax_lib::ensures(|_| future(out).len() == 24)]
#[inline(always)]
pub(crate) fn serialize_12(v: &PortableVector, out: &mut [U8]) {
    #[cfg(not(eurydice))]
    debug_assert!(out.len() == 24);
    (out[0], out[1], out[2]) = serialize_12_int(&v.elements[0..2]);
    (out[3], out[4], out[5]) = serialize_12_int(&v.elements[2..4]);
    (out[6], out[7], out[8]) = serialize_12_int(&v.elements[4..6]);
    (out[9], out[10], out[11]) = serialize_12_int(&v.elements[6..8]);
    (out[12], out[13], out[14]) = serialize_12_int(&v.elements[8..10]);
    (out[15], out[16], out[17]) = serialize_12_int(&v.elements[10..12]);
    (out[18], out[19], out[20]) = serialize_12_int(&v.elements[12..14]);
    (out[21], out[22], out[23]) = serialize_12_int(&v.elements[14..16]);
}

#[hax_lib::requires(bytes.len() == 3)]
#[inline(always)]
pub(crate) fn deserialize_12_int(bytes: &[U8]) -> (I16, I16) {
    let byte0 = bytes[0].as_i16();
    let byte1 = bytes[1].as_i16();
    let byte2 = bytes[2].as_i16();
    let r0 = (byte1 & 0x0F) << 8 | (byte0 & 0xFF);
    let r1 = (byte2 << 4) | ((byte1 >> 4) & 0x0F);
    (r0, r1)
}

#[hax_lib::requires(bytes.len() == 24)]
#[inline(always)]
pub(crate) fn deserialize_12(bytes: &[U8], out: &mut PortableVector) {
    (out.elements[0], out.elements[1]) = deserialize_12_int(&bytes[0..3]);
    (out.elements[2], out.elements[3]) = deserialize_12_int(&bytes[3..6]);
    (out.elements[4], out.elements[5]) = deserialize_12_int(&bytes[6..9]);
    (out.elements[6], out.elements[7]) = deserialize_12_int(&bytes[9..12]);
    (out.elements[8], out.elements[9]) = deserialize_12_int(&bytes[12..15]);
    (out.elements[10], out.elements[11]) = deserialize_12_int(&bytes[15..18]);
    (out.elements[12], out.elements[13]) = deserialize_12_int(&bytes[18..21]);
    (out.elements[14], out.elements[15]) = deserialize_12_int(&bytes[21..24]);
}
