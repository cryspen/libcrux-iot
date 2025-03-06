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
    pub(crate) fn start_measurement() -> u32 {
        let current = cortex_m::peripheral::DWT::cycle_count();
        // defmt::println!("[START_SECTION {=str}] ({=str}, {=u32}) : {=u32}", msg, file, line, current);
        current
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

#[cortex_m_rt::entry]
fn main() -> ! {
    // Init rtt-target defmt support
    // rtt_target::rtt_init_defmt!();

    // Initialize cycle counter
    // {
    //     use cortex_m::peripheral::Peripherals;
    //     let mut peripherals = Peripherals::take().unwrap();
    //     peripherals.DCB.enable_trace();
    //     peripherals.DWT.enable_cycle_counter();
    // }

    let mut a = [1i16; 16 * 16];
    let b = [1i16; 16 * 16];
    for _j in 0..30 {
        // let measurement_count = CycleCounter::start_measurement();
        core::hint::black_box(add_bad(&mut a, &b));
        // CycleCounter::end_measurement("add_bad", file!(), line!(), measurement_count);

        // let measurement_count = CycleCounter::start_measurement();
        core::hint::black_box(add_better(&mut a, &b));
        // CycleCounter::end_measurement("add_better", file!(), line!(), measurement_count);
    }
    board::exit()
}

#[inline(never)]
fn add_bad(a: &mut [i16], b: &[i16]) {
    for i in 0..16 * 16 {
        let a_i = a[i];
        let b_i = b[i];
        let c = a_i + b_i;

        a[i] = c
    }
}

#[inline(never)]
fn add_better(a: &mut [i16], b: &[i16]) {
    for i in 0..256 {
        a[i] = a[i] + b[i];
    }
}
