//! ML-KEM Operations driver
//!
//! This binary just runs the ML-KEM top-level operations, which
//! should be instrumented for cycle measurement.

#![no_main]
#![no_std]

use libcrux_nucleo_l4r5zi as board; // global logger + panicking-behavior + memory layout

use libcrux_ml_kem::mlkem768 as mlkem;

extern crate alloc;

use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();

extern "C" {
    static _stack_start: u32;
}

#[cortex_m_rt::entry]
fn main() -> ! {
    let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
    let pair = core::hint::black_box(mlkem::generate_key_pair(randomness_gen));

    let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
    let (_ciphertext, _shared_secret_initiator) =
        core::hint::black_box(mlkem::encapsulate(pair.public_key(), randomness_encaps));
    let stack_start = unsafe { &_stack_start as *const u32 };
    board::stack::measure(
        "ML-KEM 768 Encapsulation",
        core::hint::black_box(stack_start),
    );

    board::exit()
}
