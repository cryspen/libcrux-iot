#![no_main]
#![no_std]

use libcrux_nucleo_l4r5zi::{self as board, init::ClockConfig}; // global logger + panicking-behavior + memory layout

extern crate alloc;

use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cortex_m_rt::entry]
fn main() -> ! {
    use libcrux_iot_testutil::*;
    // Initialize the allocator BEFORE you use it
    board::init::initialize_allocator(&HEAP);

    // Set up the system clock.
    let clock_config = ClockConfig::CycleBenchmark;
    board::init::setup_clock(clock_config);

    // set up the test config
    let test_config = TestConfig {
        platform: platform::CortexM,
        core_freq: clock_config.core_freq(),
        only_names: alloc::vec![],
        early_abort: false,
        benchmark_runs: 5,
    };

    libcrux_testbench::mlkem::run_benchmarks(test_config);

    board::exit()
}
