#![no_main]
#![no_std]

use cortex_m::peripheral::Peripherals;
use libcrux_nucleo_l4r5zi as board; // global logger + panicking-behavior + memory layout

extern crate alloc;

use core::ptr::addr_of_mut;
use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cortex_m_rt::entry]
fn main() -> ! {
    use libcrux_iot_testutil::*;
    // Initialize the allocator BEFORE you use it
    {
        use core::mem::MaybeUninit;
        const HEAP_SIZE: usize = 1024;
        static mut HEAP_MEM: [MaybeUninit<u8>; HEAP_SIZE] = [MaybeUninit::uninit(); HEAP_SIZE];
        unsafe { HEAP.init(addr_of_mut!(HEAP_MEM) as usize, HEAP_SIZE) }

        let mut peripherals = Peripherals::take().unwrap();
        peripherals.DCB.enable_trace();
        peripherals.DWT.enable_cycle_counter();
    }
    // set up the test config
    let test_config = TestConfig {
        core_freq: board::COREFREQ,
        only_names: alloc::vec![],
        early_abort: false,
        benchmark_runs: 5,
    };
    
    libcrux_testbench::mldsa::run_benchmarks(test_config);

    board::exit()
}