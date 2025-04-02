#![no_main]
#![no_std]

use libcrux_nucleo_l4r5zi as board; // global logger + panicking-behavior + memory layout

extern crate alloc;

use core::ptr::{addr_of, addr_of_mut};
use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cortex_m_rt::entry]
fn main() -> ! {
    // Initialize the allocator BEFORE you use it
    {
        use core::mem::MaybeUninit;
        const HEAP_SIZE: usize = 1024;
        static mut HEAP_MEM: [MaybeUninit<u8>; HEAP_SIZE] = [MaybeUninit::uninit(); HEAP_SIZE];
        unsafe { HEAP.init(addr_of_mut!(HEAP_MEM) as usize, HEAP_SIZE) }
    }

    let mut sk = [0u8; libcrux_pqm4::KYBER_SECRETKEYBYTES as usize];
    let mut pk = [0u8; libcrux_pqm4::KYBER_PUBLICKEYBYTES as usize];

    let mut ct = [0u8; libcrux_pqm4::KYBER_CIPHERTEXTBYTES as usize];
    let mut ss_enc = [0u8; libcrux_pqm4::KYBER_SSBYTES as usize];
    let mut ss_dec = [0u8; libcrux_pqm4::KYBER_SSBYTES as usize];

    let start = board::CycleCounter::start_measurement();
    core::hint::black_box(unsafe {
        libcrux_pqm4::crypto_kem_keypair(addr_of_mut!(pk[0]), addr_of_mut!(sk[0]));
    });
    board::CycleCounter::end_measurement("pqm4: Generate Key Pair ML-KEM 1024", start);

    let start = board::CycleCounter::start_measurement();
    core::hint::black_box(unsafe {
        libcrux_pqm4::crypto_kem_enc(
            addr_of_mut!(ct[0]),
            addr_of_mut!(ss_enc[0]),
            addr_of!(pk[0]),
        );
    });
    board::CycleCounter::end_measurement("pqm4: Encapsulate ML-KEM 1024", start);

    let start = board::CycleCounter::start_measurement();
    core::hint::black_box(unsafe {
        libcrux_pqm4::crypto_kem_dec(addr_of_mut!(ss_dec[0]), addr_of!(ct[0]), addr_of!(sk[0]));
    });
    board::CycleCounter::end_measurement("pqm4: Decapsulate ML-KEM 1024", start);

    assert_eq!(ss_enc, ss_dec);

    board::exit()
}
