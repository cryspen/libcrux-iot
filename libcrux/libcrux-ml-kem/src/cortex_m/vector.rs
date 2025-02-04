use crate::vector::portable::vector_type::*;
use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;

use super::{arithmetic::plantard_multiply, intrinsics::{uadd16, usub16}};

/// Values having this type hold two packed representatives `x` and
/// `y` of the ML-KEM field.
pub(crate) type PackedFieldElement = u32;

#[derive(Clone, Copy, Debug)]
pub struct PackedVector {
    pub elements: [PackedFieldElement; crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR / 2],
}

impl From<PortableVector> for PackedVector {
    fn from(value: PortableVector) -> Self {
        let mut out: [u32; FIELD_ELEMENTS_IN_VECTOR / 2] = [0; FIELD_ELEMENTS_IN_VECTOR / 2];
        for i in 0..FIELD_ELEMENTS_IN_VECTOR / 2 {
            out[i] = pack(value.elements[2 * i], value.elements[2 * i + 1]);
        }
        Self { elements: out }
    }
}

impl From<&PortableVector> for PackedVector {
    fn from(value: &PortableVector) -> Self {
        let mut out: [u32; FIELD_ELEMENTS_IN_VECTOR / 2] = [0; FIELD_ELEMENTS_IN_VECTOR / 2];
        for i in 0..FIELD_ELEMENTS_IN_VECTOR / 2 {
            out[i] = pack(value.elements[2 * i], value.elements[2 * i + 1]);
        }
        Self { elements: out }
    }
}

pub(crate) fn pack(a: i16, b: i16) -> u32 {
    ((a as u32) << 16) | (b as u32 & 0xffff)
}

pub(crate) fn unpack(val: u32) -> (i16, i16) {
    ((val / (1 << 16)) as i16, (val & 0xffff) as i16)
}

fn add(a: PackedVector, b: PackedVector) -> PackedVector {
    let mut elements = [0; 8];
    for i in 0..8 {
        elements[i] = uadd16(a.elements[i], b.elements[i]);
    }
    PackedVector{elements}
}

fn sub(a: PackedVector, b: PackedVector) -> PackedVector {
    let mut elements = [0; 8];
    for i in 0..8 {
        elements[i] = usub16(a.elements[i], b.elements[i]);
    }
    PackedVector{elements}
}

fn mul_by_const(a: PackedVector, c: u32) -> PackedVector{
    let mut elements = [0; 8];
    for i in 0..8 {
        elements[i] = plantard_multiply(a.elements[i], c);
    }
    PackedVector{elements}    
}

impl From<PackedVector> for PortableVector {
    fn from(value: PackedVector) -> Self {
        let mut out: [i16; FIELD_ELEMENTS_IN_VECTOR] = [0; FIELD_ELEMENTS_IN_VECTOR];
        for i in 0..FIELD_ELEMENTS_IN_VECTOR / 2 {
            let (a, b) = unpack(value.elements[i]);
            out[2 * i] = a;
            out[2 * i + 1] = b;
        }
        Self { elements: out }
    }
}

pub fn from_u32_array(array: &[u32]) -> PackedVector {
    PackedVector {
        elements: array[0..8].try_into().unwrap(),
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
