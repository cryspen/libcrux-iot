#![no_main]
#![no_std]

use embassy_stm32::Config;
use embassy_time::{self, Instant};
use libcrux_ml_dsa::ml_dsa_65;
use libcrux_nucleo_l4r5zi as _; // global logger + panicking-behavior + memory layout

const KEYGEN_ITERATIONS: usize = 100;
const SIGN_ITERATIONS: usize = 100;
const VERIFY_ITERATIONS: usize = 100;

fn time_operation<SetupF, OpF, Input>(
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
    let start_measuring = Instant::now();
    for _ in 0..iterations {
        let _ = operation(&input);
    }
    let end_measuring = Instant::now();
    let time_avg = (end_measuring.as_micros() - start_measuring.as_micros()) / (iterations as u64);
    defmt::println!("Took {=u64} µs on average", time_avg);
}

#[cortex_m_rt::entry]
fn main() -> ! {
    // Need to initialize this, otherwise we have no timers
    let _peripherals = embassy_stm32::init(Config::default());

    defmt::println!("Testing that everything works");
    let randomness_gen = [1u8; 32];
    let keypair = ml_dsa_65::generate_key_pair(randomness_gen);
    defmt::println!("\tKey Generation OK");

    let signing_randomness = [4u8; 32];
    let message = [5u8; 1024];

    let signature = ml_dsa_65::sign(&keypair.signing_key, &message, signing_randomness);
    defmt::println!("\tSigning OK");

    let result = ml_dsa_65::verify(&keypair.verification_key, &message, &signature);
    defmt::println!("\tVerification OK");

    assert!(result.is_ok());
    defmt::println!("\tSuccess!");

    defmt::println!("Benchmarking");
    time_operation(
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

    time_operation(
        "\tSigning",
        || {
            let randomness_gen = [1u8; 32];
            let signing_randomness = [4u8; 32];
            let message = [5u8; 1024];

            let keypair = ml_dsa_65::generate_key_pair(randomness_gen);
            (message, keypair, signing_randomness)
        },
        |(message, keypair, signing_randomness)| {
            ml_dsa_65::sign(&keypair.signing_key, message, *signing_randomness);
        },
        SIGN_ITERATIONS,
    );

    time_operation(
        "\tVerification",
        || {
            let randomness_gen = [1u8; 32];
            let signing_randomness = [4u8; 32];
            let message = [5u8; 1024];

            let keypair = ml_dsa_65::generate_key_pair(randomness_gen);
            let signature = ml_dsa_65::sign(&keypair.signing_key, &message, signing_randomness);
            (message, keypair, signature)
        },
        |(message, keypair, signature)| {
            ml_dsa_65::verify(&keypair.verification_key, message, signature).unwrap();
        },
        VERIFY_ITERATIONS,
    );

    libcrux_nucleo_l4r5zi::exit()
}
