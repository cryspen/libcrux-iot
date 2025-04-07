#![no_main]
#![no_std]

use board::cycle_counter::CycleCounter;
use board::init::setup_cycle_counter;

use libcrux_nucleo_l4r5zi::{self as board, init::ClockConfig}; // global logger + panicking-behavior + memory layout

use core::ptr::{addr_of, addr_of_mut};

#[cortex_m_rt::entry]
fn main() -> ! {
    // Set up the system clock.
    let clock_config = ClockConfig::CycleBenchmark;
    board::init::setup_clock(clock_config);

    setup_cycle_counter();

    let mut sha3_state = libcrux_sha3::portable::incremental::shake128_init();
    let start = CycleCounter::start_measurement();
    unsafe {
        core::hint::black_box(libcrux_sha3::portable::incremental::keccakf1660_4rounds(
            core::hint::black_box(&mut sha3_state),
        ));
    }
    CycleCounter::end_measurement("libcrux: keccakf1600_4rounds", start);

    board::exit()
}
