#![no_main]
#![no_std]

use embassy_stm32::Config;
use embassy_time::{self, Instant};
use libcrux_ml_kem::mlkem1024 as mlkem;
use libcrux_nucleo_l4r5zi as _; // global logger + panicking-behavior + memory layout

const KEYGEN_ITERATIONS: usize = 100;
const ENCAPS_ITERATIONS: usize = 100;
const DECAPS_ITERATIONS: usize = 100;

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
    let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
    let pair = mlkem::generate_key_pair(randomness_gen);
    defmt::println!("\tKey Generation OK");

    let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
    let (ct, ss_enc) = mlkem::encapsulate(pair.public_key(), randomness_encaps);
    defmt::println!("\tEncapsulation OK");

    let ss_dec = mlkem::decapsulate(pair.private_key(), &ct);
    defmt::println!("\tDecapsulation OK");

    assert_eq!(ss_enc, ss_dec);
    defmt::println!("\tSuccess!");

    defmt::println!("Benchmarking");
    time_operation(
        "\tKey Generation",
        || {
            let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
            randomness_gen
        },
        |randomness| {
            let _ = mlkem::generate_key_pair(*randomness);
        },
        KEYGEN_ITERATIONS,
    );

    time_operation(
        "\tEncapsulation",
        || {
            let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
            let pair = mlkem::generate_key_pair(randomness_gen);
            let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
            (randomness_encaps, pair)
        },
        |(randomness, pair)| {
            mlkem::encapsulate(pair.public_key(), *randomness);
        },
        ENCAPS_ITERATIONS,
    );

    time_operation(
        "\tDecapsulation",
        || {
            let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
            let pair = mlkem::generate_key_pair(randomness_gen);
            let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
            let (ct, _ss) = mlkem::encapsulate(pair.public_key(), randomness_encaps);
            (ct, pair)
        },
        |(ct, pair)| {
            mlkem::decapsulate(pair.private_key(), ct);
        },
        DECAPS_ITERATIONS,
    );

    libcrux_nucleo_l4r5zi::exit()
}
