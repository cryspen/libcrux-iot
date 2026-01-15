use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;
use libcrux_secrets::*;

/// Values having this type hold a representative 'x' of the ML-KEM field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = I16;

#[derive(Clone, Copy)]
pub struct PortableVector {
    pub(crate) elements: [FieldElement; FIELD_ELEMENTS_IN_VECTOR],
}

#[inline(always)]
pub fn zero() -> PortableVector {
    PortableVector {
        elements: [0i16; FIELD_ELEMENTS_IN_VECTOR].classify(),
    }
}

#[hax_lib::requires(array.len() == 16)]
#[inline(always)]
pub fn from_i16_array(array: &[I16], out: &mut PortableVector) {
    out.elements.copy_from_slice(&array[0..16]);
}

#[hax_lib::requires(out.len() == 16)]
#[hax_lib::ensures(|_| future(out).len() == 16)]
#[cfg(hax)]
#[inline(always)]
pub fn to_i16_array(x: &PortableVector, out: &mut [i16]) {
    #[cfg(not(eurydice))]
    debug_assert!(out.len() >= 16);

    out[0..16].copy_from_slice(&x.elements.declassify());
}
