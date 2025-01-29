use super::intrinsics::*;
use super::vector::*;

const FIELD_MODULUS: u32 = 3326;
const FIELD_MODULUS_ALPHA: u32 = 26632;

pub fn plantard_double_ct(a: u32, b: u32, zeta: u32) -> (u32, u32) {
    let mut tmp = smulwb(zeta as u32, b);
    let mut b_res = smulwt(zeta as u32, b);

    tmp = smlabb(tmp, FIELD_MODULUS, FIELD_MODULUS_ALPHA);

    tmp = pkhtb_imm16(b_res, tmp);

    b_res = usub16(a, tmp);
    let a_res = uadd16(a, tmp);
    (a_res, b_res)
}

pub fn ntt_layer_1_step(
    mut vec: PackedVector,
    zeta0: u32,
    zeta1: u32,
    zeta2: u32,
    zeta3: u32,
) -> PackedVector {
    let (a, b) = plantard_double_ct(vec.elements[0], vec.elements[1], zeta0);
    vec.elements[0] = a;
    vec.elements[1] = b;
    let (a, b) = plantard_double_ct(vec.elements[2], vec.elements[3], zeta1);
    vec.elements[2] = a;
    vec.elements[3] = b;
    let (a, b) = plantard_double_ct(vec.elements[4], vec.elements[5], zeta2);
    vec.elements[4] = a;
    vec.elements[5] = b;
    let (a, b) = plantard_double_ct(vec.elements[6], vec.elements[7], zeta3);
    vec.elements[6] = a;
    vec.elements[7] = b;
    vec
}


// #[inline(never)]
// /// Unreduced Plantard multiplication
// pub fn plantard_multiply_single_coeffs(coeffs: &mut [i16; FIELD_ELEMENTS_IN_VECTOR], zeta: i32) {
//     let modulus = 3326;
//     let modulus_alpha = 26632;
//     let mut result = [0i16; 16];
//     for i in 0..coeffs.len() {
//             let mut res = smulwb(zeta, coeffs[i]);  
//             res = smlabb(res , modulus, modulus_alpha); 
//             coeffs[i] = ((res as u32) >> 16) as i16
//     }
// }

