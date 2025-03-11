#![no_main]
#![no_std]

use core::arch::asm;

use cortex_m_semihosting::debug;

use defmt_rtt as _; // global logger

use embassy_stm32 as _; // memory layout

use panic_probe as _;

// same panicking *behavior* as `panic-probe` but doesn't print a panic message
// this prevents the panic message being printed *twice* when `defmt::panic` is invoked
#[defmt::panic_handler]
fn panic() -> ! {
    cortex_m::asm::udf()
}

/// Terminates the application and makes a semihosting-capable debug tool exit
/// with status code 0.
pub fn exit() -> ! {
    loop {
        debug::exit(debug::EXIT_SUCCESS);
    }
}

/// Hardfault handler.
///
/// Terminates the application and makes a semihosting-capable debug tool exit
/// with an error. This seems better than the default, which is to spin in a
/// loop.
#[cortex_m_rt::exception]
unsafe fn HardFault(_frame: &cortex_m_rt::ExceptionFrame) -> ! {
    loop {
        debug::exit(debug::EXIT_FAILURE);
    }
}

#[inline(never)]
pub fn rust_load_slice_4(data: &[i16]) -> i16 {
    data[0] + data[1] + data[2] + data[3]
}

#[inline(never)]
pub fn rust_load_slice_loop(data: &[i16]) -> i16 {
    let mut x = 0;
    for i in 0..256 {
        x += data[i]
    }
    x
}

#[inline(never)]
pub fn rust_from_little_endian_u8(s: &mut [[u64; 5]; 5], blocks: [&[u8]; 1]) {
    for i in 0.. 168/8 {
        s[i / 5][i % 5] ^= u64::from_le_bytes(blocks[0][8 * i..8 * i + 8].try_into().unwrap());
    }
}

#[inline(never)]
pub fn rust_load_slice_unrolled(data: &[i16]) -> i16 {
    let mut x = 0;
    libcrux_macros::unroll_for!(256, "i", 0u32, 1u32, { x += data[i as usize] });
    x
}


#[inline(never)]
pub fn rust_load_arrayref_4(data: &[i16; 4]) -> i16 {
    data[0] + data[1] + data[2] + data[3]
}

#[inline(never)]
pub fn rust_load_slice_8(data: &[i16]) -> i16 {
    data[0] + data[1] + data[2] + data[3] + data[4] + data[5] + data[6] + data[7]
}

#[inline(never)]
pub fn rust_load_arrayref_8(data: &[i16; 8]) -> i16 {
    data[0] + data[1] + data[2] + data[3] + data[4] + data[5] + data[6] + data[7]
}

#[inline(never)]
pub fn rust_load_4(a: &i16, b: &i16, c: &i16, d: &i16) -> i16 {
    a + b + c + d
}

#[inline(never)]
pub fn rust_load_8(a: &i16, b: &i16, c: &i16, d: &i16, e: &i16, f: &i16, g: &i16, h: &i16) -> i16 {
    a + b + c + d + e + f + g + h
}

#[inline(never)]
pub fn asm_load_4(a: &i16, b: &i16, c: &i16, d: &i16) -> i16 {
    let mut x;
    unsafe {
        asm!(
            "ldr {x}, [r0]",
            "ldr r1, [r1]",
            "ldr r2, [r2]",
            "ldr r3, [r3]",
            "add {x}, r1",
            "add {x}, r2",
            "add {x}, r3",
            x = lateout(reg) x,
            in("r0") a,
            in("r1") b,
            in("r2") c,
            in("r3") d,
            options(nostack)
        )
    }
    x
}

#[inline(never)]
pub fn asm_load_8(a: &i16, b: &i16, c: &i16, d: &i16, e: &i16, f: &i16, g: &i16, h: &i16) -> i16 {
    let mut x;
    unsafe {
        asm!(
            "ldr {x}, [r0]",
            "ldr r1, [r1]",
            "ldr r2, [r2]",
            "ldr r3, [r3]",
            "ldr r4, [r4]",
            "ldr r5, [r5]",
            "ldr r8, [r8]",
            "ldr r9, [r9]",
            "add {x}, r1",
            "add {x}, r2",
            "add {x}, r3",
            "add {x}, r4",
            "add {x}, r5",
            "add {x}, r8",
            "add {x}, r9",
            x = lateout(reg) x,
            in("r0") a,
            in("r1") b,
            in("r2") c,
            in("r3") d,
            in("r4") e,
            in("r5") f,
            in("r8") g, // can't use r6 because it is "used internally by LLVM"
            in("r9") h, // can't use r7 because "the frame pointer (r7) cannot be used as an operand for inline asm"
            options(nostack)
        )
    }
    x
}

pub fn asm_load_slice_8(a: &[i16]) -> i16 {
    todo!();
    // let mut x;
    // unsafe {
    //     asm!(
    //         "ldr {x}, [r0]",
    //         "ldr r1, [r1]",
    //         "ldr r2, [r2]",
    //         "ldr r3, [r3]",
    //         "ldr r4, [r4]",
    //         "ldr r5, [r5]",
    //         "ldr r8, [r8]",
    //         "ldr r9, [r9]",
    //         "add {x}, r1",
    //         "add {x}, r2",
    //         "add {x}, r3",
    //         "add {x}, r4",
    //         "add {x}, r5",
    //         "add {x}, r8",
    //         "add {x}, r9",
    //         x = lateout(reg) x,
    //         in("r0") a,
    //         in("r1") b,
    //         in("r2") c,
    //         in("r3") d,
    //         in("r4") e,
    //         in("r5") f,
    //         in("r8") g, // can't use r6 because it is "used internally by LLVM"
    //         in("r9") h, // can't use r7 because "the frame pointer (r7) cannot be used as an operand for inline asm"
    //         options(nostack)
    //     )
    // }
    // x
}

#[inline(never)]
pub fn asm_load_bad_8(
    a: &i16,
    b: &i16,
    c: &i16,
    d: &i16,
    e: &i16,
    f: &i16,
    g: &i16,
    h: &i16,
) -> i16 {
    let mut x;
    unsafe {
        asm!(
            "ldr {x}, [r0]",
            "ldr r1, [r1]",
            "add {x}, r1",
            "ldr r2, [r2]",
            "add {x}, r2",
            "ldr r3, [r3]",
            "add {x}, r3",
            "ldr r4, [r4]",
            "add {x}, r4",
            "ldr r5, [r5]",
            "add {x}, r5",
            "ldr r8, [r8]",
            "add {x}, r8",
            "ldr r9, [r9]",
            "add {x}, r9",
            x = lateout(reg) x,
            in("r0") a,
            in("r1") b,
            in("r2") c,
            in("r3") d,
            in("r4") e,
            in("r5") f,
            in("r8") g, // can't use r6 because it is "used internally by LLVM"
            in("r9") h, // can't use r7 because "the frame pointer (r7) cannot be used as an operand for inline asm"
            options(nostack)
        )
    }
    x
}

#[inline(never)]
pub fn asm_load_bad_4(a: &i16, b: &i16, c: &i16, d: &i16) -> i16 {
    let mut x;
    unsafe {
        asm!(
            "ldr {x}, [r0]",
            "ldr r1, [r1]",
            "add {x}, r1",
            "ldr r2, [r2]",
            "add {x}, r2",
            "ldr r3, [r3]",
            "add {x}, r3",
            x = lateout(reg) x,
            in("r0") a,
            in("r1") b,
            in("r2") c,
            in("r3") d,
            options(nostack)
        )
    }
    x
}

// defmt-test 0.3.0 has the limitation that this `#[tests]` attribute can only be used
// once within a crate. the module can be in any file but there can only be at most
// one `#[tests]` module in this library crate
#[cfg(test)]
#[defmt_test::tests]
mod unit_tests {
    use defmt::assert;

    use super::*;

    #[test]
    fn self_test() {
        let data = [1, 2, 3, 4, 5, 6, 7, 8];

        assert_eq!(
            core::hint::black_box(asm_load_4(&data[0], &data[1], &data[2], &data[3],)),
            core::hint::black_box(rust_load_4(&data[0], &data[1], &data[2], &data[3],))
        );

        assert_eq!(
            core::hint::black_box(asm_load_bad_4(&data[0], &data[1], &data[2], &data[3],)),
            core::hint::black_box(rust_load_4(&data[0], &data[1], &data[2], &data[3],))
        );

        assert_eq!(
            core::hint::black_box(asm_load_8(
                &data[0], &data[1], &data[2], &data[3], &data[4], &data[5], &data[6], &data[7],
            )),
            core::hint::black_box(rust_load_8(
                &data[0], &data[1], &data[2], &data[3], &data[4], &data[5], &data[6], &data[7],
            ))
        );

        assert_eq!(
            core::hint::black_box(asm_load_bad_8(
                &data[0], &data[1], &data[2], &data[3], &data[4], &data[5], &data[6], &data[7],
            )),
            core::hint::black_box(rust_load_8(
                &data[0], &data[1], &data[2], &data[3], &data[4], &data[5], &data[6], &data[7],
            ))
        );
    }
}
