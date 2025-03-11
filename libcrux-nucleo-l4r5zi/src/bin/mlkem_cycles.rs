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
    // Init rtt-target defmt support
    // rtt_target::rtt_init_defmt!();

    // Initialize cycle counter
    {
        use cortex_m::peripheral::Peripherals;
        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }

    let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
    let pair = core::hint::black_box(mlkem::generate_key_pair(randomness_gen));
    let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
    let (ciphertext, _shared_secret_initiator) =
        core::hint::black_box(mlkem::encapsulate(pair.public_key(), randomness_encaps));
    let _shared_secret_responder =
        core::hint::black_box(mlkem::decapsulate(pair.private_key(), &ciphertext));
    board::exit()
}
