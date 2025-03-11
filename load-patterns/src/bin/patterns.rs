#![no_main]
#![no_std]

use cortex_m_rt::heap_start;
use load_patterns as _; // global logger + panicking-behavior + memory layout

/// A utility to quickly get cycle counts during execution.
///
/// ⚠️ Note, that the hardware must be initialized before the counter
/// can function.
pub(crate) struct CycleCounter;

impl CycleCounter {
    /// Use this to initialize the hardwar, if it hasn't been initialized elsewhere.
    pub(crate) fn init() {
        use cortex_m::peripheral::Peripherals;
        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }

    /// Signal the start of a measurement section.
    #[inline(never)]
    pub(crate) fn start_measurement() -> u32 {
        cortex_m::peripheral::DWT::cycle_count()
    }

    /// Signal the end of a measurement section.
    #[inline(never)]
    pub(crate) fn end_measurement(msg: &str, start: u32) {
        let current = cortex_m::peripheral::DWT::cycle_count();
        let diff = current - start;
        defmt::println!(
            "[END_SECTION {=str}]: {=u32} (+ {=u32})",
            msg,
            current,
            diff
        );
    }
}

#[cortex_m_rt::entry]
fn main() -> ! {
    CycleCounter::init();

    let data = [1, 2, 3, 4, 5, 6, 7, 8];
    let data_4 = [1, 2, 3, 4];
    let data_256 = [1i16; 256];
    let mut s = [[1u64; 5]; 5];
    let out_inner = [0u8; 1500];
    let out = [&out_inner[..]; 1];
    let start = CycleCounter::start_measurement();
    let result = core::hint::black_box(load_patterns::rust_from_little_endian_u8(&mut s, out));
    CycleCounter::end_measurement("rust_from_little_endian_u8", start);

    for i in 0..5 {
        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::rust_load_slice_loop(&data_256));
        CycleCounter::end_measurement("rust_load_slice_loop", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::rust_load_slice_unrolled(&data_256));
        CycleCounter::end_measurement("rust_load_slice_unroll", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::rust_load_4(
            &data[0], &data[1], &data[2], &data[3],
        ));
        CycleCounter::end_measurement("rust_load_4", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::asm_load_4(
            &data[0], &data[1], &data[2], &data[3],
        ));
        CycleCounter::end_measurement("asm_load_4", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::asm_load_bad_4(
            &data[0], &data[1], &data[2], &data[3],
        ));
        CycleCounter::end_measurement("asm_load_bad_4", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::rust_load_slice_4(&data[0..4]));
        CycleCounter::end_measurement("rust_load_slice_4", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::rust_load_arrayref_4(&data_4));
        CycleCounter::end_measurement("rust_load_arrayref_4", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::asm_load_8(
            &data[0], &data[1], &data[2], &data[3], &data[4], &data[5], &data[6], &data[7],
        ));
        CycleCounter::end_measurement("asm_load_8", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::asm_load_bad_8(
            &data[0], &data[1], &data[2], &data[3], &data[4], &data[5], &data[6], &data[7],
        ));
        CycleCounter::end_measurement("asm_load_bad_8", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::rust_load_8(
            &data[0], &data[1], &data[2], &data[3], &data[4], &data[5], &data[6], &data[7],
        ));
        CycleCounter::end_measurement("rust_load_8", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::rust_load_slice_8(&data[0..8]));
        CycleCounter::end_measurement("rust_load_slice_8", start);

        let start = CycleCounter::start_measurement();
        let result = core::hint::black_box(load_patterns::rust_load_arrayref_8(&data));
        CycleCounter::end_measurement("rust_load_arrayref_8", start);
    }
    load_patterns::exit()
}
