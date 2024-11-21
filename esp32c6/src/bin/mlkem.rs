#![no_std]
#![no_main]

use esp_backtrace as _;
use esp_hal::prelude::*;
use esp_println::println;
use libcrux_ml_kem::mlkem768 as mlkem;

#[entry]
fn main() -> ! {
    esp_hal::init(esp_hal::Config::default());

    println!("Hello world!");
    // prepare the state for the benchmarked functions
    let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
    let pair = mlkem::generate_key_pair(randomness_gen);
    println!("KeyGen OK!");
    let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
    let (ciphertext, shared_secret_encaps) =
        mlkem::encapsulate(pair.public_key(), randomness_encaps);
    println!("Encaps OK!");
    let shared_secret_decaps = mlkem::decapsulate(pair.private_key(), &ciphertext);
    println!("Decaps OK!");

    if shared_secret_encaps == shared_secret_decaps {
        println!("SUCCESS");
    } else {
        println!("FAILURE")
    }
    loop {}
}
