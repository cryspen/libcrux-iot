use super::intrinsics::*;

const FIELD_MODULUS: u32 = crate::vector::traits::FIELD_MODULUS as u32;

/// `FIELD_MODULUS` * pow(2, alpha), where alpha = 3.
const FIELD_MODULUS_ALPHA: u32 = 26632;

#[allow(unsafe_code)]
pub fn plantard_double_ct_reference(a: u32, b: u32, zeta: i32) -> (u32, u32) {
    use core::arch::asm;
    
    let mut a_res;
    let mut b_res;

    unsafe{
    asm!(
        "smulwb {t}, {zeta}, {b}",
        "smulwt {b}, {zeta}, {b}",
        "smlabb {t}, {t}, {q}, {qa}",
        "smlabb {b}, {b}, {q}, {qa}",
        "pkhtb {t}, {b}, {t}, asr#16",
        "usub16 {b}, {a}, {t}",
        "uadd16 {a}, {a}, {t}",
        a = inout(reg) a => a_res,
        b = inout(reg) b => b_res,
        zeta = in(reg) zeta,
        t = out(reg) _,
        q = in(reg) FIELD_MODULUS,
        qa = in(reg) FIELD_MODULUS_ALPHA,
        options(pure, nomem, nostack)
    );}

    (a_res, b_res)
}

pub fn plantard_double_ct(a: u32, b: u32, zeta: u32) -> (u32, u32) {
    let mut tmp = smulwb(zeta as u32, b);
    let mut b_res = smulwt(zeta as u32, b);

    tmp = smlabb(tmp, FIELD_MODULUS, FIELD_MODULUS_ALPHA);

    tmp = pkhtb_imm16(b_res, tmp);

    b_res = usub16(a, tmp);
    let a_res = uadd16(a, tmp);
    (a_res, b_res)
}

