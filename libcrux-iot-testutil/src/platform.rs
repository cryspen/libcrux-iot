/// A trait capturing platform specific details
pub trait Platform {
    /// Initialize cycle counters and other peripherals.
    fn init(&self);

    /// Return a cycle count, assuming the cycle counter has been initialized.
    fn cycle_count(&self) -> u32;
}

/// The Cortex-M specific implementation details.
#[cfg(feature = "cortex-m")]
pub mod cortex_m_platform {
    use super::*;

    pub struct CortexM;

    impl Platform for CortexM {
        fn init(&self) {
            use cortex_m::peripheral::Peripherals;
            let mut peripherals = Peripherals::take().unwrap();
            peripherals.DCB.enable_trace();
            peripherals.DWT.enable_cycle_counter();
        }

        fn cycle_count(&self) -> u32 {
            cortex_m::peripheral::DWT::cycle_count()
        }
    }
}
