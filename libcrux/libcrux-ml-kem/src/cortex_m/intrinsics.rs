use core::arch::asm;

#[inline(always)]
#[allow(unsafe_code)]
pub fn smulwb(word_a: u32, word_b: u32) -> u32 {
    let mut res: u32;
    unsafe{
        asm!(
            "smulwb {dest}, {w}, {hw}",
            w    = in(reg) word_a,
            hw   = in(reg) word_b,
            dest = out(reg) res,
            options(pure, nomem, nostack)
        )
    }
    res
}

#[inline(always)]
#[allow(unsafe_code)]
pub fn smulwt(word_a: u32, word_b: u32) -> u32 {
    let mut res: u32;
    unsafe{
        asm!(
            "smulwt {dest}, {w}, {hw}",
            w    = in(reg) word_a,
            hw   = in(reg) word_b,
            dest = out(reg) res,
            options(pure, nomem, nostack)
        )
    }
    res
}

#[inline(always)]
#[allow(unsafe_code)]
pub fn smlabb(left: u32, right: u32, accumulator: u32) -> u32 {
    let mut res: u32;
    unsafe{
        asm!(
            "smlabb {dest}, {l}, {r}, {acc}",
            l    = in(reg) left,
            r    = in(reg) right,
            acc  = in(reg) accumulator,
            dest = out(reg) res,
            options(pure, nomem, nostack)
        )
    }
    res
}

#[inline(always)]
#[allow(unsafe_code)]
pub fn pkhtb_imm16(word_a: u32, word_b: u32) -> u32 {
    let mut res: u32;
    unsafe{
        asm!(
            "pkhtb {dest}, {a}, {b}, asr#16",
            a    = in(reg) word_a,
            b    = in(reg) word_b,
            dest = out(reg) res,
            options(pure, nomem, nostack)
        )
    }
    res
}


#[inline(always)]
#[allow(unsafe_code)]
pub fn usub16(word_a: u32, word_b: u32) -> u32 {
        let mut res: u32;
    unsafe{
        asm!(
            "usub16 {dest}, {a}, {b}",
            a    = in(reg) word_a,
            b    = in(reg) word_b,
            dest = out(reg) res,
            options(pure, nomem, nostack)
        )
    }
    res
}

#[inline(always)]
#[allow(unsafe_code)]
pub fn uadd16(word_a: u32, word_b: u32) -> u32 {
        let mut res: u32;
    unsafe{
        asm!(
            "uadd16 {dest}, {a}, {b}",
            a    = in(reg) word_a,
            b    = in(reg) word_b,
            dest = out(reg) res,
            options(pure, nomem, nostack)
        )
    }
    res
}


