use crate::vector::portable::vector_type::*;
use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;

/// Values having this type hold two packed representatives `x` and
/// `y` of the ML-KEM field.
pub(crate) type PackedFieldElement = u32;

#[derive(Clone, Copy, Debug)]
pub struct PackedVector {
    pub(crate) elements: [PackedFieldElement; crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR / 2],
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
