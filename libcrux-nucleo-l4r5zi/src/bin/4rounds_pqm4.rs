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

    let mut sha3_state = [1u64; 25];
    let start = CycleCounter::start_measurement();
    unsafe {
        core::hint::black_box(libcrux_pqm4::KeccakF1600_StatePermute_4Rounds(
            core::hint::black_box(sha3_state.as_mut_ptr()),
        ));
    }
    CycleCounter::end_measurement("pqm4: KeccakF1600_StatePermute_4Rounds", start);


    board::exit()
}
