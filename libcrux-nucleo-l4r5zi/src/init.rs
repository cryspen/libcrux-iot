//! This module collects setup utilities.

use core::ptr::addr_of_mut;

use embedded_alloc::LlffHeap as Heap;

/// Use this to initialize a heap, if needed.
pub fn initialize_allocator(heap: &'static Heap) {
    use core::mem::MaybeUninit;
    const HEAP_SIZE: usize = 1024;
    static mut HEAP_MEM: [MaybeUninit<u8>; HEAP_SIZE] = [MaybeUninit::uninit(); HEAP_SIZE];
    unsafe { heap.init(addr_of_mut!(HEAP_MEM) as usize, HEAP_SIZE) }
}

/// Use this to set up the hardware cycle counter.
pub fn setup_cycle_counter() {
    use cortex_m::peripheral::Peripherals;
    let mut peripherals = Peripherals::take().unwrap();
    peripherals.DCB.enable_trace();
    peripherals.DWT.enable_cycle_counter();
}

/// The system clock configuration.
pub enum ClockConfig {
    /// A slow clock configuration, which aims to minimize flash wait
    /// states, to measure cycles spent on any function under test in
    /// ideal circumstances.
    ///
    /// Runs the system clock from the 16 MHz HSI16.
    CycleBenchmark,
    /// A fast clock configuration, which aims to minimize real time
    /// spent on any function under test.
    ///
    /// Runs the system clock from PLL, which scales HSI16 to 80 MHz.
    Fast,
}

/// Use this to set up the system clock.
///
/// We basically want replicate the setup used by pqm4.
///
/// For reference:
/// https://github.com/mupq/pqm4/blob/1a04a91573096aa79e6e8f1394bf804c9a89a1a5/common/hal-opencm3.c#L177
pub fn setup_clock(c: ClockConfig) {
    let mut config = embassy_stm32::Config::default();
    use embassy_stm32::rcc::*;

    // No frequency prescaling
    config.rcc.apb1_pre = APBPrescaler::DIV1;
    config.rcc.apb2_pre = APBPrescaler::DIV1;
    config.rcc.ahb_pre = AHBPrescaler::DIV1;
    
    match c {
        ClockConfig::CycleBenchmark => {
            // Drive the system clock from the HSI16 directly, which
            // should run at 16 MHz.
            config.rcc.hsi = true;
            config.rcc.sys = Sysclk::HSI;
        }
        ClockConfig::Fast => {
            config.rcc.pll = Some(Pll {
                // 16 MHz from HSI16 as the source
                source: PllSource::HSI,
                // No Prediv
                prediv: PllPreDiv::DIV1,
                // 16 MHz PLL input * 10 = 160 Mhz PLL VCO
                mul: PllMul::MUL10,

                // XXX: Unsure about the significance of these two.
                divp: Some(PllPDiv::DIV7),
                divq: Some(PllQDiv::DIV2),

                // 160 MHz PLL VCO / 2 = 80 MHz PLL_R Clock
                divr: Some(PllRDiv::DIV2),
            });
            // System clock comes from PLL (= the 120 MHz main PLL output)
            config.rcc.sys = Sysclk::PLL1_R;
        }
    }

    let _p = embassy_stm32::init(config);
}
