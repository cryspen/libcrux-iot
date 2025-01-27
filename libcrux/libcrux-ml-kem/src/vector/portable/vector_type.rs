use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;

/// Values having this type hold a representative 'x' of the ML-KEM field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i16;

/// Values having this type hold two packed representatives `x` and
/// `y` of the ML-KEM field.
pub(crate) type PackedFieldElement = u32;

#[derive(Clone, Copy)]
pub struct PortableVector {
    pub(crate) elements: [FieldElement; FIELD_ELEMENTS_IN_VECTOR],
}

#[derive(Clone, Copy, Debug)]
pub struct PackedVector {
    pub(crate) elements: [PackedFieldElement; FIELD_ELEMENTS_IN_VECTOR / 2],
}

#[inline(always)]
#[hax_lib::ensures(|result| fstar!(r#"${result}.f_elements == Seq.create 16 0s"#))]
pub fn zero() -> PortableVector {
    PortableVector {
        elements: [0i16; FIELD_ELEMENTS_IN_VECTOR],
    }
}

#[inline(always)]
#[hax_lib::ensures(|result| fstar!(r#"${result} == ${x}.f_elements"#))]
pub fn to_i16_array(x: PortableVector) -> [i16; 16] {
    x.elements
}

#[inline(always)]
#[hax_lib::requires(array.len() == 16)]
#[hax_lib::ensures(|result| fstar!(r#"${result}.f_elements == $array"#))]
pub fn from_i16_array(array: &[i16]) -> PortableVector {
    PortableVector {
        elements: array[0..16].try_into().unwrap(),
    }
}

impl From<PortableVector> for PackedVector {
    fn from(value: PortableVector) -> Self {
        let mut out: [u32; FIELD_ELEMENTS_IN_VECTOR / 2] = [0; FIELD_ELEMENTS_IN_VECTOR / 2];
        for i in 0..FIELD_ELEMENTS_IN_VECTOR / 2 {
            out[i] = ((value.elements[2 * i] as u32) << 16)
                | (value.elements[2 * i + 1] as u32 & 0xffff);
        }
        Self { elements: out }
    }
}

impl From<PackedVector> for PortableVector {
    fn from(value: PackedVector) -> Self {
        let mut out: [i16; FIELD_ELEMENTS_IN_VECTOR] = [0; FIELD_ELEMENTS_IN_VECTOR];
        for i in 0..FIELD_ELEMENTS_IN_VECTOR / 2 {
            out[2 * i] = (value.elements[i] / (1 << 16)) as i16;
            out[2 * i + 1] = (value.elements[i] & 0xffff) as i16;
        }
        Self { elements: out }
    }
}

#[test]
fn packing_unpacking() {
    let a = [1, -1, 2, -2, 3, -3, 4, -4, -1, 2, -2, 3, -3, 4, -4, 4];
    let vec = from_i16_array(&a);
    let packed = PackedVector::from(vec);
    let unpacked = PortableVector::from(packed);
    assert_eq!(vec.elements, unpacked.elements);
}
