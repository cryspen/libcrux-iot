//! This module provides utilites for measuring stack usage.

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
pub fn measure(name: &str, stack_start: *const u32, stack_end: *const u32) {
    defmt::println!("l,0,0,{}", name);

    let mut looking_at: *const u32 = stack_end;
    let high_mark;
    unsafe {
        // Now we scan memory for the STACK_PAINT_VALUE
        while core::ptr::read_volatile(looking_at) == STACK_PAINT_VALUE {
            looking_at = looking_at.offset(1);
        }

        high_mark = Some(looking_at.offset(-1) as usize);
    }
    if let Some(high_mark) = high_mark {
        let usage = stack_start as usize - high_mark;
        defmt::println!("b,r,stack,0");
        defmt::println!("b,d,stack,0,{}", usage);
    } else {
        defmt::println!("b,e,stack,0,NOT FOUND");
    }
}
