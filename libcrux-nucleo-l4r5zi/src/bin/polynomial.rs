#![no_main]
#![no_std]

/// A utility to quickly get cycle counts during execution.
///
/// ⚠️ Note, that the hardware must be initialized before the counter
/// can function.
pub(crate) struct CycleCounter {
    start: u32,
}

impl CycleCounter {
    /// Use this to initialize the hardwar, if it hasn't been initialized elsewhere.
    pub(crate) fn init() {
        use cortex_m::peripheral::Peripherals;
        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }

    /// Create a new CycleCounter.
    pub(crate) fn new() -> Self {
        Self { start: 0 }
    }

    /// Signal the start of a measurement section.
    pub(crate) fn start_measurement(msg: &str, file: &str, line: u32) -> u32 {
        cortex_m::peripheral::DWT::cycle_count()
    }

    /// Signal the end of a measurement section.
    pub(crate) fn end_measurement(msg: &str, file: &str, line: u32, start: u32) {
        let current = cortex_m::peripheral::DWT::cycle_count();
        let diff = current - start;
        defmt::println!(
            "[END_SECTION {=str}] ({=str}, {=u32}) : {=u32} (+ {=u32})",
            msg,
            file,
            line,
            current,
            diff
        );
    }
}

use libcrux_nucleo_l4r5zi as board; // global logger + panicking-behavior + memory layout

use libcrux_ml_kem::mlkem512 as mlkem;

extern crate alloc;

use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();
type RE = PolynomialRingElement<PortableVector>;

#[cortex_m_rt::entry]
fn main() -> ! {
    // Init rtt-target defmt support
    // rtt_target::rtt_init_defmt!();

    // Initialize cycle counter
    {
        use cortex_m::peripheral::Peripherals;
        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }

    let mut poly_a = RE::ZERO();
    let mut poly_b = RE::ZERO();
    for v in poly_b.coefficients.iter_mut() {
        v.elements = [23i16; 16];
    }

    let mut a_flat = [0i16; 256];
    let b_flat = [23i16; 256];

    let mut a_32 = [0u32; 128];
    let b_32 = [23u32; 128];

    for i in 0..10 {
        let measurement_count = CycleCounter::start_measurement("flat addition", file!(), line!());
        core::hint::black_box(flat_addition(&mut a_flat, &b_flat));
        CycleCounter::end_measurement("flat addition", file!(), line!(), measurement_count);

        let measurement_count =
            CycleCounter::start_measurement("flat addition (32)", file!(), line!());
        core::hint::black_box(flat_addition(&mut a_flat, &b_flat));
        CycleCounter::end_measurement("flat addition (32)", file!(), line!(), measurement_count);

        let measurement_count = CycleCounter::start_measurement("poly addition", file!(), line!());
        core::hint::black_box(RE::add_to_ring_element::<4>(
            // K should not matter at all here
            &mut poly_a,
            &poly_b,
        ));
        CycleCounter::end_measurement("poly addition", file!(), line!(), measurement_count);
    }
    board::exit()
}

fn flat_addition(a_flat: &mut [i16], b_flat: &[i16]) {
    for i in 0..256 {
        a_flat[i] += b_flat[i];
    }
}

fn flat_addition_32(a: &mut [u32], b: &[u32]) {
    for i in 0..128 {
        a[i] += b[i];
    }
}

pub trait Repr: Copy + Clone {
    fn repr(x: Self) -> [i16; 16];
}

trait Operations: Copy + Clone + Repr {
    fn ZERO() -> Self;
    fn to_i16_array(x: Self, out: &mut [i16; 16]);
    fn add(lhs: &mut Self, rhs: &Self);
}

pub const COEFFICIENTS_IN_RING_ELEMENT: usize = 256;
const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
pub const VECTORS_IN_RING_ELEMENT: usize = COEFFICIENTS_IN_RING_ELEMENT / FIELD_ELEMENTS_IN_VECTOR;

#[derive(Clone, Copy)]
pub struct PortableVector {
    pub elements: [i16; FIELD_ELEMENTS_IN_VECTOR],
}

impl Repr for PortableVector {
    fn repr(x: Self) -> [i16; 16] {
        let mut out = [0i16; 16];
        to_i16_array(x, &mut out);
        out
    }
}

fn zero() -> PortableVector {
    PortableVector {
        elements: [0i16; FIELD_ELEMENTS_IN_VECTOR],
    }
}

#[inline(always)]
pub fn add(lhs: &mut PortableVector, rhs: &PortableVector) {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        lhs.elements[i] += rhs.elements[i];
    }
}

impl Operations for PortableVector {
    fn ZERO() -> Self {
        zero()
    }

    fn to_i16_array(x: Self, out: &mut [i16; 16]) {
        to_i16_array(x, out)
    }
    fn add(lhs: &mut Self, rhs: &Self) {
        add(lhs, rhs)
    }
}

pub fn to_i16_array(x: PortableVector, out: &mut [i16; 16]) {
    *out = x.elements;
}

#[repr(transparent)]
pub(crate) struct PolynomialRingElement<Vector: Operations> {
    pub(crate) coefficients: [Vector; VECTORS_IN_RING_ELEMENT],
}

#[inline(always)]
fn add_to_ring_element<Vector: Operations, const K: usize>(
    myself: &mut PolynomialRingElement<Vector>,
    rhs: &PolynomialRingElement<Vector>,
) {
    for i in 0..myself.coefficients.len() {
        Vector::add(&mut myself.coefficients[i], &rhs.coefficients[i]);
    }
}

impl<Vector: Operations> PolynomialRingElement<Vector> {
    pub fn ZERO() -> PolynomialRingElement<Vector> {
        PolynomialRingElement {
            coefficients: [Vector::ZERO(); 16],
        }
    }
    /// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
    /// sum of their constituent coefficients.
    #[inline(always)]
    pub(crate) fn add_to_ring_element<const K: usize>(&mut self, rhs: &Self) {
        add_to_ring_element::<Vector, K>(self, rhs);
    }
}
