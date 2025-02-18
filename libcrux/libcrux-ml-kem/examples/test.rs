#![no_std]
#![no_main]

use libcrux_ml_kem::{mlkem512, ENCAPS_SEED_SIZE, KEY_GENERATION_SEED_SIZE};

use panic_halt as _;

use cortex_m_rt::entry;

#[entry]
fn main() -> ! {
        let randomness = [1u8; KEY_GENERATION_SEED_SIZE];
        let key_pair = mlkem512::generate_key_pair(randomness);

        let randomness = [2u8; ENCAPS_SEED_SIZE];

    let (ciphertext, shared_secret) = mlkem512::encapsulate(key_pair.public_key(), randomness);
        loop {
    }
}
