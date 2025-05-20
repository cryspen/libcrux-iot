//! ML-KEM Operations driver
//!
//! This binary just runs the ML-KEM top-level operations, which
//! should be instrumented for cycle measurement.

#![no_main]
#![no_std]

use libcrux_nucleo_l4r5zi as board; // global logger + panicking-behavior + memory layout

use libcrux_ml_dsa::ml_dsa_65 as mldsa;

extern crate alloc;

use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();

extern "C" {
    static _stack_start: u32;
}

#[cortex_m_rt::entry]
fn main() -> ! {
    let randomness_gen = [1u8; 32];
    let randomness_sign = [1u8; 32];
    let message = [0u8; 100];
    let pair = mldsa::generate_key_pair(randomness_gen);

    let _signature = core::hint::black_box(mldsa::sign(
        &pair.signing_key,
        &message,
        b"",
        randomness_sign,
    ));

    let stack_start = unsafe { &_stack_start as *const u32 };
    board::stack::measure("ML-DSA 65 Signing", core::hint::black_box(stack_start));

    board::exit()
}
