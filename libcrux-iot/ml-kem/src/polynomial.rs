use libcrux_secrets::{I16, I32};

use crate::vector::{to_standard_domain, Operations, FIELD_ELEMENTS_IN_VECTOR};

pub(crate) const ZETAS_TIMES_MONTGOMERY_R: [i16; 128] = {
    [
        -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474,
        1468, 573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411,
        -205, -1571, 1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618,
        -1162, 126, 1469, -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725,
        448, -1065, 677, -1275, -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235,
        -291, -460, 1574, 1653, -246, 778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872,
        349, 418, 329, -156, -75, 817, 1097, 603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218,
        -1335, -874, 220, -1187, -1659, -1185, -1530, -1278, 794, -1510, -854, -870, 478, -108,
        -308, 996, 991, 958, -1460, 1522, 1628,
    ]
};

// A function to retrieve zetas so that we can add a post-condition
#[inline(always)]
#[hax_lib::requires(i < 128)]
pub fn zeta(i: usize) -> i16 {
    ZETAS_TIMES_MONTGOMERY_R[i]
}

pub(crate) const VECTORS_IN_RING_ELEMENT: usize =
    super::constants::COEFFICIENTS_IN_RING_ELEMENT / FIELD_ELEMENTS_IN_VECTOR;

// XXX: We don't want to copy this. But for eurydice we have to have this.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct PolynomialRingElement<Vector: Operations> {
    pub(crate) coefficients: [Vector; VECTORS_IN_RING_ELEMENT],
}

#[hax_lib::attributes]
impl<Vector: Operations> PolynomialRingElement<Vector> {
    #[allow(non_snake_case)]
    pub(crate) fn ZERO() -> Self {
        Self {
            coefficients: [Vector::ZERO(); 16],
        }
    }

    #[inline(always)]
    #[requires(VECTORS_IN_RING_ELEMENT * 16 <= a.len())]
    pub(crate) fn from_i16_array(a: &[I16], out: &mut Self) {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            Vector::from_i16_array(&a[i * 16..(i + 1) * 16], &mut out.coefficients[i]);
        }
    }

    #[inline(always)]
    #[requires(VECTORS_IN_RING_ELEMENT * 16 <= a.len())]
    pub(crate) fn reducing_from_i32_array(a: &[I32], out: &mut Self) {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            Vector::reducing_from_i32_array(&a[i * 16..(i + 1) * 16], &mut out.coefficients[i]);
        }
    }

    #[inline(always)]
    pub(crate) fn poly_barrett_reduce(&mut self) {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            Vector::barrett_reduce(&mut self.coefficients[i]);
        }
    }

    #[inline(always)]
    pub(crate) fn subtract_reduce(&self, b: &mut Self) {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            Vector::montgomery_multiply_by_constant(&mut b.coefficients[i], 1441);

            Vector::sub(&mut b.coefficients[i], &self.coefficients[i]);
            Vector::negate(&mut b.coefficients[i]);

            Vector::barrett_reduce(&mut b.coefficients[i]);
        }
    }

    #[inline(always)]
    pub(crate) fn add_message_error_reduce(
        &self,
        message: &Self,
        result: &mut Self,
        scratch: &mut Vector,
    ) {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            Vector::montgomery_multiply_by_constant(&mut result.coefficients[i], 1441);

            *scratch = self.coefficients[i]; // XXX: Need this?
            Vector::add(scratch, &message.coefficients[i]);
            Vector::add(&mut result.coefficients[i], scratch);

            Vector::barrett_reduce(&mut result.coefficients[i]);
        }
    }

    #[inline(always)]
    pub(crate) fn add_error_reduce(&mut self, error: &Self) {
        for j in 0..VECTORS_IN_RING_ELEMENT {
            Vector::montgomery_multiply_by_constant(&mut self.coefficients[j], 1441);

            Vector::add(&mut self.coefficients[j], &error.coefficients[j]);

            Vector::barrett_reduce(&mut self.coefficients[j]);
        }
    }

    #[inline(always)]
    pub(crate) fn add_standard_error_reduce(&mut self, error: &Self) {
        for j in 0..VECTORS_IN_RING_ELEMENT {
            // The coefficients are of the form aR^{-1} mod q, which means
            // calling to_montgomery_domain() on them should return a mod q.
            to_standard_domain::<Vector>(&mut self.coefficients[j]);

            Vector::add(&mut self.coefficients[j], &error.coefficients[j]);

            Vector::barrett_reduce(&mut self.coefficients[j]);
        }
    }

    #[inline(always)]
    pub(crate) fn accumulating_ntt_multiply(&self, rhs: &Self, accumulator: &mut [I32; 256]) {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            Vector::accumulating_ntt_multiply(
                &self.coefficients[i],
                &rhs.coefficients[i],
                &mut accumulator[i * 16..(i + 1) * 16],
                zeta(64 + 4 * i),
                zeta(64 + 4 * i + 1),
                zeta(64 + 4 * i + 2),
                zeta(64 + 4 * i + 3),
            );
        }
    }

    #[inline(always)]
    pub(crate) fn accumulating_ntt_multiply_fill_cache(
        &self,
        rhs: &Self,
        accumulator: &mut [I32; 256],
        cache: &mut Self,
    ) {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            Vector::accumulating_ntt_multiply_fill_cache(
                &self.coefficients[i],
                &rhs.coefficients[i],
                &mut accumulator[i * 16..(i + 1) * 16],
                &mut cache.coefficients[i],
                zeta(64 + 4 * i),
                zeta(64 + 4 * i + 1),
                zeta(64 + 4 * i + 2),
                zeta(64 + 4 * i + 3),
            );
        }
    }

    #[inline(always)]
    pub(crate) fn accumulating_ntt_multiply_use_cache(
        &self,
        rhs: &Self,
        accumulator: &mut [I32; 256],
        cache: &Self,
    ) {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            Vector::accumulating_ntt_multiply_use_cache(
                &self.coefficients[i],
                &rhs.coefficients[i],
                &mut accumulator[i * 16..(i + 1) * 16],
                &cache.coefficients[i],
            );
        }
    }
}
