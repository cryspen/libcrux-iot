#![no_main]
#![no_std]
#![cfg(feature = "mldsa87")]

use libcrux_ml_dsa::ml_dsa_87 as mldsa;
use libcrux_nrf52810 as board; // global logger + panicking-behavior + memory layout

#[cortex_m_rt::entry]
fn main() -> ! {
    let randomness_gen = [1u8; 32];
    let _keypair = mldsa::generate_key_pair(randomness_gen);

    board::exit()
}
