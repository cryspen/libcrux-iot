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
    pub (crate) fn init() {
        use cortex_m::peripheral::Peripherals;
        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }

    /// Create a new CycleCounter.
    pub (crate) fn new() -> Self {
        Self {
            start: 0
        }
    }

    /// Signal the start of a measurement section.
    pub (crate) fn start_measurement(msg: &str, file: &str, line: u32) -> (u8, u32) {
        let current = cortex_m::peripheral::DWT::cycle_count();
        let lsu = cortex_m::peripheral::DWT::lsu_count();
        // defmt::println!("[START_SECTION {=str}] ({=str}, {=u32}) : {=u32}", msg, file, line, current);
        (lsu, current)
    }

    /// Signal the end of a measurement section.
    pub (crate) fn end_measurement(msg: &str, file: &str, line: u32, start: u32, lsu: u8) {
        let current = cortex_m::peripheral::DWT::cycle_count();
        let lsu_current = cortex_m::peripheral::DWT::lsu_count();
        let diff = current - start;
        let diff_lsu = lsu_current - lsu;
        defmt::println!("[END_SECTION {=str}] ({=str}, {=u32}) : {=u32} (+ {=u32}, {=u8})", msg, file, line, current, diff, diff_lsu);
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
    {
        use cortex_m::peripheral::Peripherals;
        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }
    
    let mut a = [1i16; 16*16];
    let b = [1i16; 16*16];
    let (lsu, measurement_count) = CycleCounter::start_measurement("add", file!(), line!());
    core::hint::black_box(add(&mut a, &b));
    CycleCounter::end_measurement("add", file!(), line!(), measurement_count, lsu);
    board::exit()
}

fn add(a: &mut[i16], b: &[i16]) {
    for i in 0..16*16{
        let (lsu,measurement_count) = CycleCounter::start_measurement("load a", file!(), line!());
        let a_i = a[i];
        CycleCounter::end_measurement("load a", file!(), line!(), measurement_count, lsu);
        let b_i = b[i];
        let (lsu, measurement_count) = CycleCounter::start_measurement("single addition", file!(), line!());
        let c = a_i + b_i;
        CycleCounter::end_measurement("single addition", file!(), line!(), measurement_count, lsu);

        let (lsu,measurement_count) = CycleCounter::start_measurement("write back", file!(), line!());
        a[i] = c;
        CycleCounter::end_measurement("write back", file!(), line!(), measurement_count, lsu);
    }
}
