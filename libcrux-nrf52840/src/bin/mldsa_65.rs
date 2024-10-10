#![no_main]
#![no_std]

use libcrux_ml_dsa::ml_dsa_65;
use libcrux_nrf52840 as _; // global logger + panicking-behavior + memory layout

use cortex_m::peripheral::{Peripherals, DWT};

const KEYGEN_ITERATIONS: usize = 10;
const SIGN_ITERATIONS: usize = 10;
const VERIFY_ITERATIONS: usize = 10;

fn init_cycle_counter() -> Peripherals {
    // Enable tracing
    let mut peripherals = Peripherals::take().unwrap();
    peripherals.DCB.enable_trace();
    peripherals.DWT.enable_cycle_counter();

    peripherals
}

fn count_cycles<SetupF, OpF, Input>(
    description: &str,
    setup: SetupF,
    operation: OpF,
    iterations: usize,
) where
    SetupF: FnOnce() -> Input,
    OpF: Fn(&Input) -> (),
{
    defmt::println!("{=str} ({=usize} times)", description, iterations);
    let input = setup();
    let start_measuring = DWT::cycle_count();
    for _ in 0..iterations {
        let _ = operation(&input);
    }
    let end_measuring = DWT::cycle_count();
    let time_avg = (end_measuring - start_measuring) / (iterations as u32);
    defmt::println!("Took {=u32} cycles on average", time_avg);
}

#[cortex_m_rt::entry]
fn main() -> ! {
    let _peripherals = init_cycle_counter();
    defmt::println!("Testing that everything works");
    let randomness_gen = [1u8; 32];
    let keypair = ml_dsa_65::generate_key_pair(randomness_gen);
    defmt::println!("\tKey Generation OK");

    let signing_randomness = [4u8; 32];
    let message = [5u8; 1024];

    let signature = ml_dsa_65::sign(&keypair.signing_key, &message, b"", signing_randomness).unwrap();
    defmt::println!("\tSigning OK");

    let result = ml_dsa_65::verify(&keypair.verification_key, &message, b"", &signature);
    defmt::println!("\tVerification OK");

    assert!(result.is_ok());
    defmt::println!("\tSuccess!");

    defmt::println!("Benchmarking");
    count_cycles(
        "\tKey Generation",
        || {
            let randomness_gen = [1u8; 32];
            randomness_gen
        },
        |randomness| {
            let _pair = ml_dsa_65::generate_key_pair(*randomness);
        },
        KEYGEN_ITERATIONS,
    );

    count_cycles(
        "\tSigning",
        || {
            let randomness_gen = [1u8; 32];
            let signing_randomness = [4u8; 32];
            let message = [5u8; 1024];

            let keypair = ml_dsa_65::generate_key_pair(randomness_gen);
            (message, keypair, signing_randomness)
        },
        |(message, keypair, signing_randomness)| {
            let _ = ml_dsa_65::sign(&keypair.signing_key, message, b"", *signing_randomness);
        },
        SIGN_ITERATIONS,
    );

    count_cycles(
        "\tVerification",
        || {
            let randomness_gen = [1u8; 32];
            let signing_randomness = [4u8; 32];
            let message = [5u8; 1024];

            let keypair = ml_dsa_65::generate_key_pair(randomness_gen);
            let signature = ml_dsa_65::sign(&keypair.signing_key, &message, b"", signing_randomness).unwrap();
            (message, keypair, signature)
        },
        |(message, keypair, signature)| {
            ml_dsa_65::verify(&keypair.verification_key, message, b"", signature).unwrap();
        },
        VERIFY_ITERATIONS,
    );

    libcrux_nrf52840::exit()
}
