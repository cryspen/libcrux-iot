use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;

/// Values having this type hold a representative 'x' of the ML-KEM field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i16;

pub(crate) type PackedFieldElements = u32;

pub(crate) type UnpackedFieldElementArray = [FieldElement; FIELD_ELEMENTS_IN_VECTOR];
pub(crate) type PackedFieldElementArray = [PackedFieldElements; FIELD_ELEMENTS_IN_VECTOR / 2];

#[derive(Clone, Copy)]
pub(crate) enum PortableVector {
    Unpacked { elements: UnpackedFieldElementArray },
    Packed { elements: PackedFieldElementArray },
}

#[inline(always)]
#[hax_lib::ensures(|result| fstar!(r#"${result}.f_elements == Seq.create 16 0s"#))]
pub(crate) fn zero() -> PortableVector {
    PortableVector::Unpacked {
        elements: [0i16; FIELD_ELEMENTS_IN_VECTOR],
    }
}

#[inline(always)]
#[hax_lib::ensures(|result| fstar!(r#"${result} == ${x}.f_elements"#))]
pub(crate) fn to_i16_array(x: PortableVector) -> [i16; 16] {
    match x {
        PortableVector::Unpacked { elements } => elements,
        _ => panic!(),
    }
}

#[inline(always)]
#[hax_lib::requires(array.len() == 16)]
#[hax_lib::ensures(|result| fstar!(r#"${result}.f_elements == $array"#))]
pub(crate) fn from_i16_array(array: &[i16]) -> PortableVector {
    PortableVector::Unpacked {
        elements: array[0..16].try_into().unwrap(),
    }
}

#[inline(always)]
pub(crate) fn pack(a: i16, b: i16) -> u32 {
    ((a as u32) << 16) | (b as u32 & 0xffff)
}

#[inline(always)]
pub(crate) fn unpack(val: u32) -> (i16, i16) {
    ((val / (1 << 16)) as i16, (val & 0xffff) as i16)
}

pub(crate) fn pack_array(v: UnpackedFieldElementArray) -> PackedFieldElementArray {
    let mut out: [u32; FIELD_ELEMENTS_IN_VECTOR / 2] = [0; FIELD_ELEMENTS_IN_VECTOR / 2];
    for i in 0..FIELD_ELEMENTS_IN_VECTOR / 2 {
        out[i] = pack(v[2 * i], v[2 * i + 1]);
    }
    out
}

pub(crate) fn unpack_array(v: PackedFieldElementArray) -> UnpackedFieldElementArray {
    let mut out: [i16; FIELD_ELEMENTS_IN_VECTOR] = [0; FIELD_ELEMENTS_IN_VECTOR];
    for i in 0..FIELD_ELEMENTS_IN_VECTOR / 2 {
        let (a, b) = unpack(v[i]);
        out[2 * i] = a;
        out[2 * i + 1] = b;
    }
    out
}
