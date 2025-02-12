#![no_main]
#![no_std]

use libcrux_nucleo_l4r5zi as board; // global logger + panicking-behavior + memory layout

use libcrux_ml_kem::mlkem512 as mlkem;

extern crate alloc;

use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cortex_m_rt::entry]
fn main() -> ! {
    let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
    let pair = mlkem::generate_key_pair(randomness_gen);
    let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
    let (ciphertext, shared_secret) = mlkem::encapsulate(pair.public_key(), randomness_encaps);

    defmt::println!("Public Key:");
    defmt::println!("{=[u8]}", *pair.public_key().as_slice());

    defmt::println!("\nPrivate Key:");
    defmt::println!("{=[u8]}", *pair.private_key().as_slice());

    defmt::println!("\nCiphertext:");
    defmt::println!("{=[u8]}", *ciphertext.as_slice());

    defmt::println!("\nShared Secret:");
    defmt::println!("{=[u8]}", *shared_secret.as_slice());
    defmt::println!("\n Done");
    board::exit()
}
