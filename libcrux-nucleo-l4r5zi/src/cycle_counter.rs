//! This module provides a cycle counting utility.

/// A utility to quickly get cycle counts during execution.
///
/// ⚠️ Note, that the hardware must be initialized using
/// [`crate::init::setup_cycle_counter`] before the counter can
/// function.
pub struct CycleCounter {}

impl CycleCounter {
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
