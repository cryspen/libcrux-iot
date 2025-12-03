use libcrux_secrets::{CastOps as _, Classify as _, U8};

use crate::{constants::Eta, helper::cloop, simd::portable::vector_type::Coefficients};

#[inline(always)]
fn serialize_when_eta_is_2(simd_unit: &Coefficients, serialized: &mut [U8]) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == 3);

    const ETA: i32 = 2;

    let coefficient0 = (ETA.classify() - simd_unit.values[0]).as_u8();
    let coefficient1 = (ETA.classify() - simd_unit.values[1]).as_u8();
    let coefficient2 = (ETA.classify() - simd_unit.values[2]).as_u8();
    let coefficient3 = (ETA.classify() - simd_unit.values[3]).as_u8();
    let coefficient4 = (ETA.classify() - simd_unit.values[4]).as_u8();
    let coefficient5 = (ETA.classify() - simd_unit.values[5]).as_u8();
    let coefficient6 = (ETA.classify() - simd_unit.values[6]).as_u8();
    let coefficient7 = (ETA.classify() - simd_unit.values[7]).as_u8();

    serialized[0] = (coefficient2 << 6) | (coefficient1 << 3) | coefficient0;
    serialized[1] =
        (coefficient5 << 7) | (coefficient4 << 4) | (coefficient3 << 1) | (coefficient2 >> 2);
    serialized[2] = (coefficient7 << 5) | (coefficient6 << 2) | (coefficient5 >> 1);
}

#[inline(always)]
fn serialize_when_eta_is_4(simd_unit: &Coefficients, serialized: &mut [U8]) {
    const ETA: i32 = 4;

    cloop! {
        for (i, coefficients) in simd_unit.values.chunks_exact(2).enumerate() {
            let coefficient0 = (ETA.classify() - coefficients[0]).as_u8();
            let coefficient1 = (ETA.classify() - coefficients[1]).as_u8();

            serialized[i] = (coefficient1 << 4) | coefficient0;
        }
    }

    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}

#[inline(always)]
pub(crate) fn serialize(eta: Eta, simd_unit: &Coefficients, serialized: &mut [U8]) {
    // [eurydice] injects an unused variable here in the C code for some reason.
    match eta {
        Eta::Two => serialize_when_eta_is_2(simd_unit, serialized),
        Eta::Four => serialize_when_eta_is_4(simd_unit, serialized),
    }
}

#[inline(always)]
fn deserialize_when_eta_is_2(serialized: &[U8], simd_unit: &mut Coefficients) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == 3);

    const ETA: i32 = 2;

    let byte0 = serialized[0].as_i32();
    let byte1 = serialized[1].as_i32();
    let byte2 = serialized[2].as_i32();

    simd_unit.values[0] = ETA.classify() - (byte0 & 7);
    simd_unit.values[1] = ETA.classify() - ((byte0 >> 3) & 7);
    simd_unit.values[2] = ETA.classify() - (((byte0 >> 6) | (byte1 << 2)) & 7);
    simd_unit.values[3] = ETA.classify() - ((byte1 >> 1) & 7);
    simd_unit.values[4] = ETA.classify() - ((byte1 >> 4) & 7);
    simd_unit.values[5] = ETA.classify() - (((byte1 >> 7) | (byte2 << 1)) & 7);
    simd_unit.values[6] = ETA.classify() - ((byte2 >> 2) & 7);
    simd_unit.values[7] = ETA.classify() - ((byte2 >> 5) & 7);
}

#[inline(always)]
fn deserialize_when_eta_is_4(serialized: &[U8], simd_units: &mut Coefficients) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == 4);

    const ETA: i32 = 4;

    cloop! {
        for (i, byte) in serialized.iter().enumerate() {
            simd_units.values[2 * i] = ETA.classify() - ((*byte & 0xF).as_i32());
            simd_units.values[2 * i + 1] = ETA.classify() - ((*byte >> 4).as_i32());
        }
    }

    // [hax] https://github.com/hacspec/hax/issues/720
    ()
}
#[inline(always)]
pub(crate) fn deserialize(eta: Eta, serialized: &[U8], out: &mut Coefficients) {
    // [eurydice] injects an unused variable here in the C code for some reason.
    //            That's why we don't match here.
    match eta {
        Eta::Two => deserialize_when_eta_is_2(serialized, out),
        Eta::Four => deserialize_when_eta_is_4(serialized, out),
    }
}
