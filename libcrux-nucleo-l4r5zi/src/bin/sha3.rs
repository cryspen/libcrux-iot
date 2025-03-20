#![no_main]
#![no_std]

use core::hint::black_box;

use libcrux_nucleo_l4r5zi as board; // global logger + panicking-behavior + memory layout

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
    let in1 = [1u8; 128];
    let in2 = [2u8; 1024];
    let in3 = [3u8; 1024 * 20];

    let start = CycleCounter::start_measurement();
    let _d1 = black_box(libcrux_sha3::sha256(&black_box(in1)));
    CycleCounter::end_measurement("128 bytes", start);
    let start = CycleCounter::start_measurement();
    let _d2 = black_box(libcrux_sha3::sha256(&black_box(in2)));
    CycleCounter::end_measurement("1 KB", start);
    let start = CycleCounter::start_measurement();
    let _d3 = black_box(libcrux_sha3::sha256(&black_box(in3)));
    CycleCounter::end_measurement("20 KB", start);

    board::exit()
}

/// A utility to quickly get cycle counts during execution.
///
/// ⚠️ Note, that the hardware must be initialized before the counter
/// can function.
pub(crate) struct CycleCounter {}

impl CycleCounter {
    /// Use this to initialize the hardwar, if it hasn't been initialized elsewhere.
    pub(crate) fn init() {
        use cortex_m::peripheral::Peripherals;
        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }

    /// Signal the start of a measurement section.
    pub(crate) fn start_section(msg: &str, file: &str, line: u32) -> u32 {
        let current = cortex_m::peripheral::DWT::cycle_count();
        current
    }

    /// Signal the end of a measurement section.
    pub(crate) fn end_section(msg: &str, file: &str, line: u32, start: u32) {
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

    /// Start measuring cycles.
    ///
    /// ⚠️ Using this presupposes that the cycle counter has been initialized somewhere.
    #[inline(never)]
    pub(crate) fn start_measurement() -> u32 {
        cortex_m::peripheral::DWT::cycle_count()
    }

    /// Report cycles current cycles (Use this to mark the end of measurement).
    ///
    /// ⚠️ Using this presupposes that the cycle counter has been initialized somewhere.
    #[inline(never)]
    pub(crate) fn end_measurement(msg: &str, start: u32) {
        let diff = cortex_m::peripheral::DWT::cycle_count() - start;
        defmt::println!("[END_MEASUREMENT {=str}] : + {=u32}", msg, diff);
    }
}
