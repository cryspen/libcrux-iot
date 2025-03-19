#![no_main]
#![no_std]

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
    // let in_h = [1u8; 128];
    // let in_g = [1u8; 128];
    
    let in_34 = [1u8; 34];

    // let mut out_g = [0u8; 64];
    // let mut out_h = [0u8; 32];
    
    // // These exist for different values of K * ETA1/2
    // let mut out_prf_2_eta1 = [0u8; 3 * 64 * 2];
    // let mut out_prf_2_eta2 = [0u8; 2 * 64 * 2];
    
    // let mut out_prf_3_eta1_eta2 = [0u8; 2 * 64 * 3];

    // let mut out_prf_4_eta1_eta2 = [0u8; 2 * 64 * 4];
    
    let mut out_block = [0u8; 168];
    let mut out_three_blocks = [0u8; 168 * 3];

    for _i in 0..3 {
        // let start = CycleCounter::start_measurement();
        // core::hint::black_box(libcrux_sha3::portable::sha256(&mut out_h, &in_h));
        // core::hint::black_box(CycleCounter::end_measurement("Hasher::H", start, &out_h));
        
        // let start = CycleCounter::start_measurement();
        // core::hint::black_box(libcrux_sha3::portable::sha512(&mut out_g, &in_g));
        // core::hint::black_box(CycleCounter::end_measurement("Hasher::G", start, &out_g));

        // // TODO: Different PRF output sizes
        // let start = CycleCounter::start_measurement();
        // core::hint::black_box(libcrux_sha3::portable::shake256(&mut out_prf, &in_prf));
        // core::hint::black_box(CycleCounter::end_measurement("PRF (in: 32, out: )", start, &out_prf));

        // let start = CycleCounter::start_measurement();
        // core::hint::black_box(libcrux_sha3::portable::shake256(&mut out_prf, &in_prf));
        // core::hint::black_box(CycleCounter::end_measurement("PRF (in: 32, out: )", start, &out_prf));

        // // TODO: Different PRFxN output sizes
        // let start = CycleCounter::start_measurement();
        // core::hint::black_box(libcrux_sha3::portable::shake256(&mut out_prf, &in_prf_xn));
        // core::hint::black_box(CycleCounter::end_measurement("PRFxN (in: 33, out: )", start, &out_prf));

        // let start = CycleCounter::start_measurement();
        // core::hint::black_box(libcrux_sha3::portable::shake256(&mut out_prf, &in_prf_xn));
        // core::hint::black_box(CycleCounter::end_measurement("PRFxN (in: 33, out: )", start, &out_prf));

        let start = CycleCounter::start_measurement();
        let mut shake128_state = core::hint::black_box(libcrux_sha3::portable::incremental::shake128_init());
        core::hint::black_box(CycleCounter::end_measurement("Shake128 init", start, &shake128_state));

        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::incremental::shake128_absorb_final(&mut shake128_state, &in_34));
        core::hint::black_box(CycleCounter::end_measurement("Shake128 absorb final", start, &shake128_state));

        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::incremental::shake128_squeeze_first_three_blocks(&mut shake128_state, &mut out_three_blocks[..]));
        core::hint::black_box(CycleCounter::end_measurement("Shake128 squeeze three blocks", start, &shake128_state));

        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::incremental::shake128_squeeze_next_block(&mut shake128_state, &mut out_block[..]));
        core::hint::black_box(CycleCounter::end_measurement("Shake128 squeeze one block", start, &shake128_state));
    }
    board::exit()
}

/// A utility to quickly get cycle counts during execution.
///
/// ⚠️ Note, that the hardware must be initialized before the counter
/// can function.
pub(crate) struct CycleCounter {}

impl CycleCounter {
    /// Use this to initialize the hardwar, if it hasn't been initialized elsewhere.
    #[allow(dead_code)]
    pub(crate) fn init() {
        use cortex_m::peripheral::Peripherals;
        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
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
    pub(crate) fn end_measurement<T>(msg: &str, start: u32, _input: &T) {
        let diff = cortex_m::peripheral::DWT::cycle_count() - start;
        defmt::println!("[END_MEASUREMENT {=str}] : + {=u32}", msg, diff);
    }
}
