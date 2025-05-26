/// This module provides utilites for measuring stack usage.

const STACK_PAINT_VALUE: u32 = 0xcccc_cccc;

#[inline(never)]
/// Measure and print maximal stack usage.
///
/// This assumes a downward growing stack starting at `stack_start`
/// and searches for the lowest occurence in memory of the
/// STACK_PAINT_VALUE, which originates from `cortex-m-rt`'s
/// `paint-stack` feature. It then prints the address right before
/// where the marker was found and the distance in bytes from
/// `stack_start`.
///
/// **SAFETY**: This function relies on inherently unsafe operations:
///  - Reading the stack pointer for the starting point of the search via inline assembly
///  - `read_volatile` to reliably scan memory for the paint marker
pub fn measure(name: &str, stack_start: *const u32) {
    defmt::println!("l,0,0,{}", name);
    // defmt::println!("  Stack begins at: {:?}", stack_start);

    #[allow(unused_assignments)]
    let mut looking_at: u32 = 0;
    // We get the current stack pointer.
    unsafe {
        core::arch::asm!(
            "mov {stack_pointer}, sp",
            stack_pointer = out(reg) looking_at,
            options(nomem, nostack)
        );
    }

    // Now we scan memory for the STACK
    while unsafe { core::ptr::read_volatile(looking_at as *const u32) } != STACK_PAINT_VALUE {
        looking_at -= 4;
    }

    let high_mark = looking_at + 4;

    let usage = stack_start as usize - high_mark as usize;
    defmt::println!("b,r,stack,0");
    defmt::println!("b,d,stack,0,{}", usage);
}
