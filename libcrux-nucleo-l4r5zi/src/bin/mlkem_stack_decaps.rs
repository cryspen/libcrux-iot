//! ML-KEM Operations driver
//!
//! This binary just runs the ML-KEM top-level operations, which
//! should be instrumented for cycle measurement.

#![no_main]
#![no_std]

use libcrux_nucleo_l4r5zi as board; // global logger + panicking-behavior + memory layout

use board::assets::mlkem::mlkem1024 as assets;
use libcrux_ml_kem::mlkem1024 as mlkem;

extern crate alloc;

use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();

extern "C" {
    static _stack_start: u32;
    static _stack_end: u32;
}

#[cortex_m_rt::entry]
fn main() -> ! {
    let _shared_secret_responder = core::hint::black_box(mlkem::decapsulate(
        &libcrux_ml_kem::MlKemPrivateKey::from(assets::DK),
        &libcrux_ml_kem::MlKemCiphertext::from(assets::CT),
    ));

    let stack_start = core::hint::black_box(unsafe { &_stack_start as *const u32 });
    let stack_end = core::hint::black_box(unsafe { &_stack_end as *const u32 });

    board::stack::measure(
        assets::STR_DECAPS,
        core::hint::black_box(stack_start),
        core::hint::black_box(stack_end),
    );

    board::exit()
}
