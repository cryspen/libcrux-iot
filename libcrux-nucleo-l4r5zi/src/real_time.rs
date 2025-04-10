//! This module provides a drop-in real time benchmark utilites.
//!
//! The timer resolution is set via the `tick-hz-*` feature selected
//! on `embassy-time`. Currently the tick rate is set to 80 MHz,
//! the highest system clock frequency configurable at the moment via
//! [`ClockConfig`].

use embassy_time::Instant;

pub struct Timer {}

impl Timer {
    #[inline(never)]
    pub fn start_measurement() -> Instant {
        Instant::now()
    }

    #[inline(never)]
    pub fn end_measurement(msg: &str, start: Instant) {
        let diff = start.elapsed();
        defmt::println!("[REAL_TIME_MEASUREMENT {=str}] : + {=u64} μs", msg, diff.as_micros());
    }
}
