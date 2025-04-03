#![no_main]
#![no_std]

use cortex_m_semihosting::debug;

use defmt_rtt as _; // global logger

use embassy_stm32 as _; // memory layout

use panic_probe as _;

pub const COREFREQ: u32 = 4_000_000;

/// A utility to quickly get cycle counts during execution.
///
/// ⚠️ Note, that the hardware must be initialized before the counter
/// can function.
pub struct CycleCounter {}

impl CycleCounter {
    /// Use this to initialize the hardwar, if it hasn't been initialized elsewhere.
    pub fn init() {
        use cortex_m::peripheral::Peripherals;
        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }

    /// Start measuring cycles.
    ///
    /// ⚠️ Using this presupposes that the cycle counter has been initialized somewhere.
    #[inline(never)]
    pub fn start_measurement() -> u32 {
        cortex_m::peripheral::DWT::cycle_count()
    }

    /// Report cycles current cycles (Use this to mark the end of measurement).
    ///
    /// ⚠️ Using this presupposes that the cycle counter has been initialized somewhere.
    #[inline(never)]
    pub fn end_measurement(msg: &str, start: u32) {
        let diff = cortex_m::peripheral::DWT::cycle_count() - start;
        defmt::println!("[END_MEASUREMENT {=str}] : + {=u32}", msg, diff);
    }
}

// same panicking *behavior* as `panic-probe` but doesn't print a panic message
// this prevents the panic message being printed *twice* when `defmt::panic` is invoked
#[defmt::panic_handler]
fn panic() -> ! {
    cortex_m::asm::udf()
}

/// Terminates the application and makes a semihosting-capable debug tool exit
/// with status code 0.
pub fn exit() -> ! {
    loop {
        debug::exit(debug::EXIT_SUCCESS);
    }
}

/// Hardfault handler.
///
/// Terminates the application and makes a semihosting-capable debug tool exit
/// with an error. This seems better than the default, which is to spin in a
/// loop.
#[cortex_m_rt::exception]
unsafe fn HardFault(_frame: &cortex_m_rt::ExceptionFrame) -> ! {
    loop {
        debug::exit(debug::EXIT_FAILURE);
    }
}

// defmt-test 0.3.0 has the limitation that this `#[tests]` attribute can only be used
// once within a crate. the module can be in any file but there can only be at most
// one `#[tests]` module in this library crate
#[cfg(test)]
#[defmt_test::tests]
mod unit_tests {
    use defmt::assert;

    #[test]
    fn it_works() {
        assert!(true)
    }
}
