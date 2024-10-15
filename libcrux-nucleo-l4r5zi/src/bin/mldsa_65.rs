#![no_main]
#![no_std]

use libcrux_iot_testutil::DefmtInfoLogger;
use libcrux_iot_testutil::*;
extern crate alloc;
use alloc::string::String;
use alloc::vec;

use cortex_m::peripheral::Peripherals;
use libcrux_ml_dsa::ml_dsa_65;
use libcrux_nucleo_l4r5zi as _; // global logger + panicking-behavior + memory layout

use core::ptr::addr_of_mut;
use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();

struct MLDSABenchState {
    randomness_gen: [u8; 32],
    keypair: ml_dsa_65::MLDSA65KeyPair,
    signing_randomness: [u8; 32],
    message: [u8; 1024],
    signature: ml_dsa_65::MLDSA65Signature,
}

fn bench_keygen<L: EventLogger>(_l: &mut L, state: &MLDSABenchState) -> Result<(), String> {
    let _pair = ml_dsa_65::generate_key_pair(state.randomness_gen);
    Ok(())
}

fn bench_sign<L: EventLogger>(_l: &mut L, state: &MLDSABenchState) -> Result<(), String> {
    let _signature = ml_dsa_65::sign(
        &state.keypair.signing_key,
        &state.message,
        b"",
        state.signing_randomness,
    );
    Ok(())
}

fn bench_verify<L: EventLogger>(_l: &mut L, state: &MLDSABenchState) -> Result<(), String> {
    let _ = ml_dsa_65::verify(
        &state.keypair.verification_key,
        &state.message,
        b"",
        &state.signature,
    );

    Ok(())
}

#[cortex_m_rt::entry]
fn main() -> ! {
    // Initialize the allocator BEFORE you use it
    {
        use core::mem::MaybeUninit;
        const HEAP_SIZE: usize = 1024;
        static mut HEAP_MEM: [MaybeUninit<u8>; HEAP_SIZE] = [MaybeUninit::uninit(); HEAP_SIZE];
        unsafe { HEAP.init(addr_of_mut!(HEAP_MEM) as usize, HEAP_SIZE) }

        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }

    // set up the test suite
    let mut test_suite = TestSuite::new();
    test_suite.register("bench_keygen", bench_keygen);
    test_suite.register("bench_sign", bench_sign);
    test_suite.register("bench_verify", bench_verify);

    // set up the test config
    let test_config = TestConfig {
        core_freq: 4_000_000,
        only_names: vec!["bench_keygen", "bench_sign", "bench_verify"],
        early_abort: false,
        benchmark_runs: 5,
    };

    // prepare the state for the benchmarked functions
    let randomness_gen = [1u8; 32];
    let keypair = ml_dsa_65::generate_key_pair(randomness_gen);
    let signing_randomness = [4u8; 32];
    let message = [5u8; 1024];
    let signature =
        ml_dsa_65::sign(&keypair.signing_key, &message, b"", signing_randomness).unwrap();

    let state = MLDSABenchState {
        randomness_gen,
        keypair,
        signing_randomness,
        message,
        signature,
    };

    // run the benchmark
    let mut logger = DefmtInfoLogger;
    let _ = test_suite.benchmark(&mut logger, &test_config, &state);

    libcrux_nucleo_l4r5zi::exit()
}
