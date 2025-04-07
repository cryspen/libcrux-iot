.section .text.libcrux_sha3::portable::incremental::keccakf1660_4rounds,"ax",%progbits
	.p2align	1
	.type	libcrux_sha3::portable::incremental::keccakf1660_4rounds,%function
	.code	16
	.thumb_func
libcrux_sha3::portable::incremental::keccakf1660_4rounds:
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/lib.rs : 360
		pub fn keccakf1660_4rounds(s: &mut KeccakState) {
	.fnstart
	.cfi_startproc
	.save	{r4, r5, r6, r7, lr}
	push {r4, r5, r6, r7, lr}
	.cfi_def_cfa_offset 20
	.cfi_offset lr, -4
	.cfi_offset r7, -8
	.cfi_offset r6, -12
	.cfi_offset r5, -16
	.cfi_offset r4, -20
	.setfp	r7, sp, #12
	add r7, sp, #12
	.cfi_def_cfa r7, 8
	.save	{r8, r9, r10, r11}
	push.w {r8, r9, r10, r11}
	.cfi_offset r11, -24
	.cfi_offset r10, -28
	.cfi_offset r9, -32
	.cfi_offset r8, -36
	.pad	#368
	sub sp, #368
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r4, [r0, #40]
	ldr r1, [r0, #48]
	ldr r2, [r0, #56]
	str r1, [sp, #336]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r1, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r3, [r0, #64]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r6, [r0, #72]
	ldr.w r12, [r0, #44]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r5, [r0, #52]
	str r2, [sp, #240]
	ldr r2, [r0, #60]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #272]
	eor.w r3, r1, r6
	eor.w r1, r5, r12
	str r2, [sp, #232]
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r2, [r0, #68]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #224]
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r2, [r0, #76]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #324]
	eors r2, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r2, [sp, #344]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r6, [sp, #328]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #1
	mov r11, r2
	orr.w r9, r1, r3, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w r1, [r0, #164]
	ldr.w r2, [r0, #172]
	ldr.w r6, [r0, #180]
	str r4, [sp, #348]
	str.w r12, [sp, #360]
	mov r12, r3
	str r3, [sp, #312]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r3, r2, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w r4, [r0, #188]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r3, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w lr, [r0, #160]
	str r1, [sp, #300]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r3, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w r10, [r0, #168]
	ldr.w r1, [r0, #196]
	ldr.w r8, [r0, #176]
	str r5, [sp, #320]
	ldr.w r5, [r0, #184]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #340]
	eors r1, r3
	eor.w r3, r10, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r2, [sp, #332]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r3, r3, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w r2, [r0, #192]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r4, [sp, #276]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r4, r1, r9
	str r1, [sp, #264]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r1, r12, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r3, r5
	str r2, [sp, #356]
	eors r2, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str.w r10, [sp, #280]
	ldrd r3, r10, [r0, #32]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r1, r11, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	str r2, [sp, #200]
	eors r2, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r3, [sp, #316]
	eor.w r1, r4, r10
	eors r3, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r6, [sp, #228]
	str r2, [sp, #260]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r6, r3, #18
	str r3, [sp, #308]
	orr.w r2, r6, r1, lsr #14
	str r1, [sp, #304]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r1, [r0, #80]
	ldr r3, [r0, #88]
	str r2, [sp, #364]
	ldr r2, [r0, #96]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r6, r3, r1
	str r2, [sp, #244]
	eors r6, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r2, [r0, #104]
	str r1, [sp, #296]
	ldr r1, [r0, #112]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r6, r2
	str r1, [sp, #180]
	eor.w r12, r6, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r1, [r0, #84]
	ldr r6, [r0, #92]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #216]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r2, [r0, #100]
	str r6, [sp, #204]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r6, r1
	str r2, [sp, #172]
	eors r6, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r2, [r0, #108]
	str r1, [sp, #284]
	ldr r1, [r0, #116]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r6, r2
	str r1, [sp, #148]
	eors r1, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r4, [sp, #352]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #212]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r4, [r0, #4]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r1, #1
	mov r11, r1
	str r1, [sp, #140]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r1, [r0, #12]
	str r3, [sp, #236]
	ldr r3, [r0, #20]
	str r4, [sp, #288]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r4, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r6, [r0, #28]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r4, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str.w r8, [sp, #220]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r8, r2, r12, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r4, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r1, [sp, #196]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r1, r4, r10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r3, [sp, #168]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #360]
	mov r4, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str.w lr, [sp, #292]
	ldr.w lr, [r0]
	ldr.w r9, [r0, #8]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	str r1, [sp, #104]
	eor.w r1, r1, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r2, [r0, #16]
	str r6, [sp, #160]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r6, r1, r3
	str r1, [sp, #268]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r1, r12, #1
	orr.w r3, r1, r11, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r1, r9, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r5, [sp, #248]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r5, [r0, #24]
	str r2, [sp, #144]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	ldr r2, [sp, #316]
	eors r1, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str.w r9, [sp, #188]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r8, r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #348]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r2, r3, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r2, [sp, #360]
	eor.w r3, r2, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr r1, [r0, #120]
	ldr.w r9, [r0, #132]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r3, #1
	orr.w r10, r2, r6, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w r2, [r0, #128]
	str r3, [sp, #256]
	str r2, [sp, #184]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r2, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w r3, [r0, #136]
	str r1, [sp, #88]
	ldr r1, [r4, #124]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r2, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r5, [sp, #156]
	ldr.w r5, [r0, #144]
	ldr.w r11, [r0, #140]
	str.w lr, [sp, #176]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r2, r5
	str r6, [sp, #192]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str.w r9, [sp, #152]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r9, r9, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w lr, [r0, #148]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r4, r9, r11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w r6, [r0, #152]
	str.w r12, [sp, #116]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r4, r4, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	ldr.w r12, [r0, #156]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #208]
	eor.w r0, r2, r6
	eor.w r4, r4, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r5, [sp, #136]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r5, r0, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #72]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #312]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r5, r5, r4, lsr #31
	str.w r12, [sp, #76]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r12, r5, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r5, r4, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r2, [sp, #344]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r5, r5, r0, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #236]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eors r5, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r2, [sp, #204]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r3, [sp, #252]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r1, r1, r12
	eor.w r3, r5, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str r6, [sp, #120]
	mov r2, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r5, [sp, #348]
	lsls r5, r1, #6
	orr.w r6, r5, r3, lsr #26
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r6, [sp, #164]
	bic.w r5, r6, r10
	ldr r6, [sp, #364]
	str r1, [sp, #124]
	eor.w r1, r5, r6
	ldr r6, [sp, #104]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r5, r8, #1
	str r1, [sp, #344]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #356]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r5, r5, r6, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str.w r11, [sp, #128]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r11, r0, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r6, #1
	orr.w r0, r0, r8, lsr #31
	str r3, [sp, #112]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r3, r1, r11
	ldr r1, [sp, #340]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r0, [sp, #356]
	eors r1, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r3, #14
	str r3, [sp, #108]
	str r1, [sp, #104]
	orr.w r1, r0, r1, lsr #18
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #336]
	ldr r3, [sp, #360]
	ldr r6, [sp, #268]
	eors r3, r0
	ldr r0, [sp, #320]
	str r3, [sp, #96]
	eors r0, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r0, [sp, #100]
	ldr.w r9, [sp, #260]
	lsls r0, r0, #12
	orr.w r3, r0, r3, lsr #20
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	ldr r0, [sp, #176]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 13
		arr[5 * j + i]
	str.w lr, [sp, #132]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	eor.w r0, r0, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #176]
	bic.w r0, r3, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r1, [sp, #340]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w lr, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #148]
	str.w r10, [sp, #316]
	mov r10, r12
	eor.w r1, r2, r0
	ldr r0, [sp, #180]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w r12, [sp, #92]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r2, r12, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #29
	str r2, [sp, #80]
	orr.w r12, r0, r2, lsr #3
	ldr r2, [sp, #200]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r1, [sp, #84]
	ldr r1, [sp, #264]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r2, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r4, [sp, #116]
	str r3, [sp, #312]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r1, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #88]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eors r4, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #140]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r2, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r5, r4, r3
	str r5, [sp, #88]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r8, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #72]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r5, #28
	ldr r5, [sp, #356]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r1, r1, r8
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r1, [sp, #68]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str.w lr, [sp, #204]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r3, r0, r1, lsr #4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #280]
	str r3, [sp, #320]
	eor.w r2, r0, r11
	ldr r0, [sp, #332]
	str r2, [sp, #64]
	eor.w r1, r0, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r2, #20
	str r1, [sp, #60]
	orr.w r0, r0, r1, lsr #12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #148]
	bics r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	ldr r1, [sp, #344]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r0, r0, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #200]
	eor.w r0, r0, lr
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w r12, [sp, #336]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w lr, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #76]
	str.w r11, [sp, #236]
	eor.w r2, r8, r1
	ldr r1, [sp, #120]
	str r2, [sp, #76]
	eors r1, r4
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r2, #24
	str r1, [sp, #56]
	orr.w r3, r2, r1, lsr #8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #292]
	ldr.w r12, [sp, #352]
	eor.w r0, r11, r1
	ldr r1, [sp, #300]
	str r0, [sp, #292]
	eors r1, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r0, #27
	str r1, [sp, #52]
	orr.w r11, r2, r1, lsr #5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #196]
	str r3, [sp, #332]
	eor.w r0, r12, r1
	ldr r1, [sp, #188]
	str r0, [sp, #44]
	eor.w r1, r1, r9
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r0, #4
	str r1, [sp, #40]
	orr.w r1, r2, r1, lsr #28
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r1, [sp, #280]
	bic.w r2, r1, r11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #328]
	ldr r1, [sp, #360]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r2, r3
	str r2, [sp, #180]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r3, lr, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r1, r0
	ldr r0, [sp, #324]
	str r1, [sp, #32]
	eors r0, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r1, #2
	str r0, [sp, #28]
	orr.w r1, r2, r0, lsr #30
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #284]
	ldr r2, [sp, #348]
	str.w r11, [sp, #140]
	eor.w r6, r2, r0
	ldr r0, [sp, #296]
	str r1, [sp, #324]
	eor.w lr, r10, r0
	ldr r0, [sp, #152]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r6, #30
	str r4, [sp, #36]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r9, r8, r0
	ldr r0, [sp, #184]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r5, r2, lr, lsr #2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r5, [sp, #328]
	eor.w r2, r4, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r11, r9, #23
	orr.w r0, r11, r2, lsr #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #120]
	bic.w r5, r0, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #304]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r5, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #308]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r10, r3, r5
	str r5, [sp, #196]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #18
	ldr r5, [sp, #124]
	orr.w r3, r0, r1, lsr #14
	ldr r0, [sp, #192]
	ldr r1, [sp, #256]
	lsls r2, r2, #23
	str r3, [sp, #116]
	orr.w r2, r2, r9, lsr #9
	lsls r0, r0, #1
	ldr.w r9, [sp, #92]
	orr.w r1, r0, r1, lsr #31
	ldr r0, [sp, #112]
	str r1, [sp, #304]
	str.w r10, [sp, #48]
	lsls r0, r0, #6
	orr.w r0, r0, r5, lsr #26
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #72]
	bics r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #108]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r5, r0, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #104]
	str r5, [sp, #184]
	lsls r0, r0, #14
	orr.w r11, r0, r1, lsr #18
	ldr r0, [sp, #96]
	ldr r1, [sp, #100]
	str.w r11, [sp, #308]
	lsls r0, r0, #12
	orr.w r1, r0, r1, lsr #20
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	ldr r0, [sp, #288]
	str r1, [sp, #264]
	eor.w r0, r0, r12
	str r0, [sp, #108]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r1, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #84]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r11, r11, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #80]
	str.w r11, [sp, #192]
	lsls r0, r0, #29
	orr.w r12, r0, r1, lsr #3
	ldr r0, [sp, #68]
	ldr r1, [sp, #88]
	str.w r12, [sp, #300]
	lsls r0, r0, #28
	orr.w r3, r0, r1, lsr #4
	ldr r0, [sp, #60]
	ldr r1, [sp, #64]
	str r3, [sp, #104]
	lsls r0, r0, #20
	orr.w r0, r0, r1, lsr #12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #64]
	bics r0, r3
	eor.w r0, r0, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #188]
	eor.w r0, r0, r11
	mov r11, r10
	eor.w r12, r0, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #56]
	lsls r5, r0, #24
	ldr r0, [sp, #76]
	orr.w r3, r5, r0, lsr #8
	ldr r0, [sp, #52]
	str r3, [sp, #296]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r2, [sp, #52]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r5, r0, #27
	ldr r0, [sp, #292]
	orr.w r1, r5, r0, lsr #5
	ldr r0, [sp, #40]
	str r1, [sp, #96]
	lsls r5, r0, #4
	ldr r0, [sp, #44]
	orr.w r0, r5, r0, lsr #28
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #284]
	bic.w r5, r0, r1
	eor.w r1, r5, r3
	str r1, [sp, #124]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r0, r12, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #28]
	lsl.w r5, lr, #30
	ldr.w lr, [sp, #352]
	lsls r4, r1, #2
	ldr r1, [sp, #32]
	orr.w r3, r4, r1, lsr #30
	orr.w r1, r5, r6, lsr #2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r2, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r1, [sp, #292]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r1, r2, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #152]
	eors r1, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r0, r10, #1
	ldr r4, [sp, #36]
	mov r6, r8
	orr.w r0, r0, r1, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r0, [sp, #60]
	ldr r0, [sp, #252]
	str r1, [sp, #256]
	eor.w r1, r4, r0
	ldr r0, [sp, #128]
	str r1, [sp, #100]
	eor.w r2, r8, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #25
	str r2, [sp, #84]
	orr.w r1, r0, r2, lsr #7
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #248]
	ldr r2, [sp, #236]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r3, [sp, #288]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r3, r0, r2
	ldr r0, [sp, #276]
	ldr r2, [sp, #356]
	ldr.w r8, [sp, #348]
	eors r2, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r3, #8
	str r2, [sp, #56]
	orr.w r2, r0, r2, lsr #24
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #364]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r1, [sp, #252]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r0, r2
	str r2, [sp, #80]
	eor.w r12, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #172]
	str r3, [sp, #76]
	eor.w r1, r8, r0
	ldr r0, [sp, #244]
	str r1, [sp, #44]
	eor.w r2, r9, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #11
	str r2, [sp, #40]
	orr.w r5, r0, r2, lsr #21
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #136]
	ldr.w r10, [sp, #260]
	eor.w r1, r4, r0
	ldr r0, [sp, #132]
	str r1, [sp, #136]
	eor.w r2, r6, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #21
	str r2, [sp, #132]
	orr.w r1, r0, r2, lsr #11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #340]
	ldr r6, [sp, #268]
	bics r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r5, [sp, #248]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r3, r0, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #144]
	ldr r5, [sp, #360]
	eor.w r2, r10, r0
	ldr r0, [sp, #168]
	str r2, [sp, #144]
	eor.w r4, lr, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r2, #3
	str r4, [sp, #36]
	orr.w r2, r0, r4, lsr #29
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #224]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r1, [sp, #276]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r4, r6, r0
	ldr r0, [sp, #272]
	str r4, [sp, #32]
	eor.w r1, r5, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r4, #13
	str r1, [sp, #28]
	orr.w r4, r0, r1, lsr #19
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #336]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #240]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r2, [sp, #244]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r2, r5, r1
	ldr r1, [sp, #232]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #168]
	eors r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r6, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r3, [sp, #172]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r0, r0, r12
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r3, r1, r6, lsr #22
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #216]
	str r2, [sp, #360]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r6, r6, #10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r2, r9, r1
	ldr r1, [sp, #212]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r4, [sp, #272]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r4, r8, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #15
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r2, [sp, #92]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r2, r1, r4, lsr #17
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #332]
	str r2, [sp, #268]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r4, r4, #15
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r3, [sp, #240]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #128]
	eor.w r8, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #228]
	ldr r0, [sp, #356]
	str.w r12, [sp, #112]
	eor.w r2, r1, r0
	ldr r1, [sp, #220]
	ldr r0, [sp, #236]
	str r2, [sp, #24]
	eors r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #7
	str r0, [sp, #348]
	orr.w r5, r1, r0, lsr #25
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #160]
	str r5, [sp, #356]
	eor.w r0, lr, r1
	ldr r1, [sp, #156]
	str r0, [sp, #236]
	eor.w r3, r10, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #324]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r0, #9
	ldr.w lr, [sp, #116]
	orr.w r0, r2, r3, lsr #23
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #260]
	bic.w r2, r1, r0
	eor.w r1, r2, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #88]
	eor.w r0, r8, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #60]
	str r0, [sp, #68]
	eors r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r0, [sp, #352]
	ldr r0, [sp, #256]
	ldr r1, [sp, #100]
	ldr r2, [sp, #76]
	lsls r0, r0, #1
	orr.w r11, r0, r11, lsr #31
	ldr r0, [sp, #84]
	lsls r0, r0, #25
	orr.w r1, r0, r1, lsr #7
	ldr r0, [sp, #56]
	mov r10, r1
	str r1, [sp]
	lsls r0, r0, #8
	orr.w r9, r0, r2, lsr #24
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, lr, r9
	eor.w r12, r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #40]
	ldr r1, [sp, #44]
	str.w r12, [sp, #76]
	lsls r0, r0, #11
	orr.w r5, r0, r1, lsr #21
	ldr r0, [sp, #132]
	ldr r1, [sp, #136]
	str r5, [sp, #224]
	lsls r0, r0, #21
	orr.w r1, r0, r1, lsr #11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #308]
	str r1, [sp, #232]
	bics r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #144]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r2, r0, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #36]
	ldr r5, [sp, #32]
	str r2, [sp, #160]
	lsls r0, r0, #3
	orr.w r1, r0, r1, lsr #29
	ldr r0, [sp, #28]
	str r1, [sp, #216]
	lsls r0, r0, #13
	orr.w r5, r0, r5, lsr #19
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #300]
	str r5, [sp, #228]
	bics r0, r5
	eors r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #360]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #156]
	eors r0, r2
	eor.w r0, r0, r12
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r2, r6, r1, lsr #22
	ldr r1, [sp, #92]
	str r2, [sp, #212]
	orr.w r6, r4, r1, lsr #17
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #296]
	str r6, [sp, #220]
	bic.w r4, r1, r6
	ldr r6, [sp, #80]
	eor.w r1, r4, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #84]
	eors r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #348]
	ldr r2, [sp, #236]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #216]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r5, r1, #7
	ldr r1, [sp, #24]
	orr.w r8, r5, r1, lsr #25
	lsls r1, r3, #9
	orr.w r12, r1, r2, lsr #23
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #288]
	ldr r2, [sp, #316]
	bic.w r1, r1, r12
	ldr r5, [sp, #120]
	eor.w r1, r1, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #44]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	str r0, [sp, #36]
	eor.w r1, r11, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #364]
	ldr.w r11, [sp, #164]
	bic.w r0, r2, r0
	str r1, [sp, #236]
	eor.w r3, r0, r6
	ldr r0, [sp, #304]
	str r3, [sp, #28]
	bic.w r0, r0, lr
	ldr.w lr, [sp, #356]
	eor.w r2, r0, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #352]
	str r2, [sp, #12]
	eors r3, r0
	eor.w r0, r1, r2
	str r0, [sp, #100]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #25
	str r3, [sp, #92]
	orr.w r0, r0, r3, lsr #7
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #360]
	ldr r0, [sp, #252]
	ldr r1, [sp, #248]
	bic.w r0, r6, r0
	ldr r2, [sp, #244]
	eor.w r3, r0, r11
	ldr r0, [sp, #276]
	ldr r6, [sp, #148]
	bics r0, r1
	ldr r1, [sp, #312]
	str r3, [sp, #56]
	eors r1, r0
	ldr r0, [sp, #272]
	str r1, [sp, #136]
	bics r0, r2
	ldr r2, [sp, #240]
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #144]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #268]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str.w r12, [sp, #4]
	bics r1, r2
	ldr r2, [sp, #280]
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #32]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #260]
	bic.w r1, r1, lr
	eors r1, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #80]
	eor.w r3, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r9, r10
	ldr.w r10, [sp, #72]
	ldr r1, [sp, #224]
	eor.w r2, r0, r10
	ldr r0, [sp, #232]
	ldr.w r9, [sp, #64]
	bics r0, r1
	ldr r1, [sp, #264]
	str r2, [sp, #40]
	eors r1, r0
	ldr r0, [sp, #228]
	str r1, [sp, #116]
	bics r0, r4
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r3, [sp, #24]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r0, r0, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #132]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #220]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r2, [sp, #212]
	bics r1, r2
	ldr r2, [sp, #284]
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #16]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r1, r12, r8
	ldr.w r12, [sp, #52]
	eor.w r1, r1, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #60]
	eor.w r2, r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r3, #1
	mov r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	str r2, [sp, #20]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r2, lsr #31
	mov r3, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r2, [sp, #48]
	eors r2, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r3, #1
	orr.w r0, r0, r1, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #256]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r2, [sp, #348]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r3, r1, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #328]
	bic.w r0, lr, r5
	ldr r5, [sp, #292]
	eor.w lr, r0, r1
	bic.w r1, r8, r12
	eors r1, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r5, r2, lr
	eor.w r0, r3, r1
	str r0, [sp, #52]
	str r5, [sp, #48]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r0, #18
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #252]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r2, r2, r5, lsr #14
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r2, [sp, #356]
	bic.w r2, r0, r11
	ldr r0, [sp, #316]
	str r3, [sp, #364]
	eor.w r5, r2, r0
	ldr r0, [sp, #244]
	ldr r2, [sp, #312]
	bic.w r3, r0, r6
	ldr r0, [sp, #320]
	ldr r6, [sp, #280]
	eor.w r4, r3, r0
	ldr r0, [sp, #248]
	ldr.w r12, [sp, #140]
	bic.w r3, r0, r2
	ldr r2, [sp, #176]
	ldr r0, [sp, #240]
	eors r3, r2
	str r4, [sp, #120]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 33
		a ^ c
	eor r3, r3, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #148]
	eors r3, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r4, r0, r6
	eor.w r0, r4, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r3, r5
	eors r3, r0
	str r0, [sp, #316]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r11, r3, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #304]
	bic.w r0, r0, r10
	ldr r6, [sp, #104]
	eor.w r10, r0, r3
	ldr r0, [sp, #224]
	ldr r3, [sp, #264]
	str r5, [sp, #8]
	bics r0, r3
	ldr r3, [sp, #108]
	ldr r5, [sp, #212]
	eor.w r4, r0, r3
	ldr r0, [sp, #216]
	str r4, [sp, #256]
	bic.w r0, r0, r9
	ldr.w lr, [sp, #96]
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #240]
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #284]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r0, r0, r10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r4, r5, r4
	ldr r5, [sp, #320]
	eor.w r4, r4, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r4, [sp, #304]
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #308]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r1, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r4, r3, r4
	ldr r3, [sp, #300]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #1
	orr.w r8, r0, r11, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #232]
	eors r0, r4
	bic.w r4, r6, r3
	ldr r3, [sp, #228]
	str r0, [sp, #232]
	eors r3, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #228]
	eor.w r4, r3, r0
	ldr r0, [sp, #12]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #296]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r4, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #220]
	bic.w r6, lr, r3
	eors r0, r6
	ldrd r6, r3, [sp, #288]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #312]
	eors r4, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #4]
	bic.w r6, r3, r6
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #300]
	eor.w r9, r4, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #340]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #124]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r3, r9, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r4, r2, r4
	ldr r2, [sp, #276]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r6, r0, r3
	str r3, [sp, #248]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r3, r4, r2
	ldr r2, [sp, #336]
	str r3, [sp, #104]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r0, r11, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r4, r5, r2
	ldr r2, [sp, #272]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r1, lsr #31
	str r6, [sp, #296]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r2, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #224]
	eor.w r4, r2, r3
	ldr r2, [sp, #28]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #268]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r4, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r2, [sp, #332]
	bic.w r2, r12, r2
	eors r2, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #288]
	eors r2, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldrd r3, r4, [sp, #324]
	bics r4, r3
	ldr r3, [sp, #260]
	eors r3, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #336]
	eors r2, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #360]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r3, r2, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #180]
	str r3, [sp, #252]
	eor.w r5, r0, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r6, #8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #356]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r5, lsr #24
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #220]
	bic.w r0, r3, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #8]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r8, r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #364]
	ldr r6, [sp, #348]
	str r5, [sp, #320]
	eor.w r0, r0, r10
	ldr r5, [sp, #68]
	eors r3, r6
	ldr r6, [sp, #36]
	str r0, [sp, #308]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #3
	orr.w lr, r0, r3, lsr #29
	lsls r0, r5, #1
	orr.w r0, r0, r6, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r4, [sp, #32]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r0, r0, r11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r0, [sp, #8]
	eors r4, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r6, #1
	orr.w r0, r0, r5, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r6, [sp, #24]
	eors r1, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #16]
	str r1, [sp, #12]
	eors r1, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r4, #13
	str r1, [sp, #276]
	orr.w r1, r0, r1, lsr #19
	lsls r0, r2, #1
	orr.w r0, r0, r9, lsr #31
	str r4, [sp, #280]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eors r6, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #88]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r3, [sp, #292]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r4, r6, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r0, r9, #1
	orr.w r0, r0, r2, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r2, [sp, #20]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r1, [sp, #124]
	mov r11, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r10, r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #44]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w lr, [sp, #332]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r3, r10, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r4, #29
	str r3, [sp, #268]
	orr.w r0, r0, r3, lsr #3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #340]
	bics r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r6, [sp, #72]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r9, r0, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #112]
	ldr.w lr, [sp, #236]
	eor.w r1, r6, r0
	ldr r0, [sp, #76]
	str r1, [sp, #264]
	eor.w r3, r10, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #11
	str r3, [sp, #260]
	orr.w r12, r0, r3, lsr #21
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #312]
	ldr r3, [sp, #352]
	ldr r1, [sp, #288]
	eor.w r0, r0, lr
	str r0, [sp, #180]
	eor.w r6, r3, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #21
	str r6, [sp, #76]
	orr.w r6, r0, r6, lsr #11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #152]
	ldr r5, [sp, #248]
	str r4, [sp, #272]
	eor.w r2, r0, r5
	ldr r0, [sp, #196]
	ldr r4, [sp, #252]
	str.w r9, [sp, #216]
	eor.w r1, r0, r4
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r2, #14
	str.w r12, [sp, #284]
	orr.w r0, r0, r1, lsr #18
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #312]
	bics r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str.w r8, [sp, #164]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r0, r0, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #176]
	eor.w r0, r0, r9
	ldr.w r12, [sp, #12]
	eor.w r9, r0, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #40]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r1, [sp, #68]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r1, r12, r0
	ldr r0, [sp, #56]
	ldr.w r8, [sp, #8]
	str r1, [sp, #64]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r1, #10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r0, r0, r8
	str r6, [sp, #108]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r0, [sp, #56]
	orr.w r6, r1, r0, lsr #22
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #84]
	ldr r1, [sp, #128]
	eor.w r0, r0, r10
	str r2, [sp, #152]
	eor.w r2, r11, r1
	str r0, [sp, #44]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r0, #15
	str r2, [sp, #40]
	orr.w r0, r1, r2, lsr #17
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #336]
	str r0, [sp, #112]
	eor.w r2, r3, r1
	ldr r1, [sp, #300]
	str r2, [sp, #36]
	eor.w r3, lr, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #24
	str r3, [sp, #32]
	orr.w r1, r1, r3, lsr #8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r1, [sp, #336]
	bics r1, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w r10, [sp, #88]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r1, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #212]
	eor.w r0, r9, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #344]
	mov r10, r12
	str r6, [sp, #324]
	eor.w r2, r1, r4
	ldr r1, [sp, #184]
	str r2, [sp, #28]
	eor.w r3, r1, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #7
	str r3, [sp, #24]
	orr.w r2, r1, r3, lsr #25
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #316]
	ldr r3, [sp, #348]
	str r2, [sp, #300]
	eor.w r9, r3, r1
	ldr r1, [sp, #304]
	ldr r3, [sp, #364]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r5, [sp, #152]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r3, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r1, r9, #9
	orr.w r4, r1, r3, lsr #23
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #60]
	str r4, [sp, #96]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r3, #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w lr, r12, r1
	ldr r1, [sp, #80]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r3, r3, r9, lsr #23
	ldr.w r9, [sp, #88]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r12, r8, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r11, lr, #2
	ldr r1, [sp, #52]
	orr.w r6, r11, r12, lsr #30
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r6, [sp, #344]
	bics r6, r4
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r3, [sp, #60]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r6, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r2, [sp, #100]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r11, r0, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #92]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r6, [sp, #196]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w r11, [sp, #316]
	lsls r0, r0, #25
	orr.w r4, r0, r2, lsr #7
	ldr r0, [sp, #48]
	str r4, [sp, #304]
	ldr r2, [sp, #272]
	lsls r0, r0, #18
	orr.w r6, r0, r1, lsr #14
	ldr r0, [sp, #320]
	ldr r1, [sp, #296]
	str r6, [sp, #328]
	lsls r0, r0, #8
	orr.w r0, r0, r1, lsr #24
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #244]
	bic.w r0, r6, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #308]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r6, r0, r4
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #292]
	str r6, [sp, #140]
	lsls r0, r0, #3
	orr.w r4, r0, r1, lsr #29
	ldr r0, [sp, #276]
	ldr r1, [sp, #280]
	str r4, [sp, #288]
	lsls r0, r0, #13
	orr.w r1, r0, r1, lsr #19
	ldr r0, [sp, #268]
	str r1, [sp, #92]
	lsls r0, r0, #29
	orr.w r0, r0, r2, lsr #3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #320]
	bics r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #264]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r2, r0, r4
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #260]
	str r2, [sp, #100]
	lsls r0, r0, #11
	orr.w r4, r0, r1, lsr #21
	ldr r0, [sp, #76]
	ldr r1, [sp, #180]
	str r4, [sp, #84]
	lsls r0, r0, #21
	orr.w r1, r0, r1, lsr #11
	ldr r0, [sp, #68]
	str r1, [sp, #128]
	lsls r0, r0, #14
	orr.w r0, r0, r5, lsr #18
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #264]
	bics r0, r1
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #152]
	eors r0, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r2, [sp, #32]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r1, r0, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #56]
	lsls r6, r0, #10
	ldr r0, [sp, #64]
	orr.w r4, r6, r0, lsr #22
	ldr r0, [sp, #40]
	str r4, [sp, #276]
	lsls r6, r0, #15
	ldr r0, [sp, #44]
	orr.w r0, r6, r0, lsr #17
	lsls r6, r2, #24
	ldr r2, [sp, #36]
	str r0, [sp, #76]
	orr.w r2, r6, r2, lsr #8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r2, [sp, #296]
	bic.w r6, r2, r0
	eors r6, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r6, [sp, #184]
	eor.w r0, r1, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #24]
	lsls r6, r1, #7
	ldr r1, [sp, #28]
	orr.w r2, r6, r1, lsr #25
	lsl.w r1, r12, #2
	orr.w r1, r1, lr, lsr #30
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r1, [sp, #292]
	bics r1, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r2, [sp, #260]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #180]
	eors r1, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r0, r11, #1
	str r1, [sp, #308]
	mov r6, r10
	orr.w r0, r0, r1, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r0, [sp, #68]
	ldr r0, [sp, #116]
	ldr.w r12, [sp, #364]
	eor.w r1, r10, r0
	ldr r0, [sp, #136]
	str r1, [sp, #80]
	eor.w r2, r8, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #1
	str r2, [sp, #136]
	orr.w r1, r0, r2, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #156]
	ldr.w r10, [sp, #72]
	eor.w r2, r9, r0
	ldr r0, [sp, #168]
	str r2, [sp, #156]
	eor.w r5, r10, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r2, #6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r1, [sp, #280]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r2, r0, r5, lsr #26
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #360]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r5, [sp, #56]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r0, r2
	str r2, [sp, #64]
	eor.w r11, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #144]
	str.w r11, [sp, #116]
	eor.w r1, r8, r0
	ldr r0, [sp, #132]
	str r1, [sp, #52]
	eor.w r3, r6, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #12
	str r3, [sp, #48]
	orr.w r1, r0, r3, lsr #20
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	ldr r0, [sp, #256]
	str r1, [sp, #272]
	eor.w r6, r12, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #284]
	ldr.w r8, [sp, #352]
	bics r0, r1
	str r6, [sp, #268]
	eor.w r1, r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldrd r0, lr, [sp, #232]
	ldr r6, [sp, #248]
	eor.w r3, lr, r0
	ldr r0, [sp, #104]
	str r3, [sp, #132]
	eor.w r4, r8, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r3, #28
	str r4, [sp, #104]
	orr.w r5, r0, r4, lsr #4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #188]
	ldr r3, [sp, #252]
	eor.w r4, r0, r6
	ldr r0, [sp, #200]
	str r4, [sp, #188]
	eor.w r2, r0, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r4, #20
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r1, [sp, #144]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r4, r0, r2, lsr #12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #332]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r2, [sp, #44]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r5, [sp, #256]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #200]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #192]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r4, [sp, #232]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r0, r0, r11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r2, r6, r1
	ldr r1, [sp, #204]
	str r2, [sp, #40]
	eor.w r5, r3, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #27
	ldr r2, [sp, #348]
	orr.w r3, r1, r5, lsr #5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #120]
	str r3, [sp, #248]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r5, r5, #27
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r6, r2, r1
	ldr r1, [sp, #240]
	str r6, [sp, #120]
	eor.w r4, r12, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r6, #4
	orr.w r6, r1, r4, lsr #28
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #324]
	str r6, [sp, #252]
	bics r1, r6
	ldr r6, [sp, #300]
	eors r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #168]
	eor.w r12, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #172]
	eor.w r0, r10, r1
	ldr r1, [sp, #160]
	str r0, [sp, #172]
	eor.w r3, r9, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r0, #30
	orr.w r0, r1, r3, lsr #2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #224]
	str r0, [sp, #240]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r3, #30
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r11, r8, r1
	ldr r1, [sp, #228]
	ldr.w r8, [sp, #84]
	eor.w r10, lr, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r9, r11, #23
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #68]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r9, r9, r10, lsr #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str.w r9, [sp, #352]
	bic.w r6, r6, r9
	eors r6, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r6, [sp, #204]
	eor.w r0, r12, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	str r0, [sp, #160]
	eors r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r0, [sp, #364]
	ldr r0, [sp, #308]
	ldr r6, [sp, #316]
	ldr r1, [sp, #80]
	lsls r0, r0, #1
	orr.w r0, r0, r6, lsr #31
	str r0, [sp, #236]
	ldr r0, [sp, #136]
	lsls r0, r0, #1
	orr.w r6, r0, r1, lsr #31
	ldr r0, [sp, #56]
	ldr r1, [sp, #156]
	str r6, [sp, #228]
	lsls r0, r0, #6
	orr.w r1, r0, r1, lsr #26
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #304]
	str r1, [sp, #192]
	bics r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #52]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r9, r0, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #48]
	movw r6, #32898
	str.w r9, [sp, #72]
	lsls r0, r0, #12
	orr.w lr, r0, r1, lsr #20
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	ldr r0, [sp, #148]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #132]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	eors r2, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r8, lr
	eors r0, r2
	str r2, [sp, #224]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 33
		a ^ c
	eor.w r2, r0, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #104]
	ldr r6, [sp, #188]
	str r2, [sp, #88]
	lsls r0, r0, #28
	orr.w r12, r0, r1, lsr #4
	ldr r0, [sp, #44]
	ldr r1, [sp, #40]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str.w r12, [sp, #8]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #20
	orr.w r6, r0, r6, lsr #12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #288]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r5, r1, lsr #5
	lsls r5, r4, #4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #4]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r0, r6
	str r6, [sp, #28]
	eor.w r0, r0, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #188]
	eors r0, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r2, [sp, #120]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r0, r0, r9
	mov r9, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str.w lr, [sp, #20]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r4, r5, r2, lsr #28
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r2, [sp, #276]
	str r4, [sp, #24]
	bic.w r4, r2, r4
	eors r4, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #172]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r0, r4
	str r4, [sp, #156]
	ldr r4, [sp, #128]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r2, r3, r1, lsr #2
	lsl.w r1, r10, #23
	orr.w r3, r1, r11, lsr #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #260]
	str r3, [sp, #40]
	mov r6, r2
	bics r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #132]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #236]
	str r0, [sp, #68]
	eor.w r3, r1, r0
	ldr r2, [sp, #108]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #284]
	ldr r1, [sp, #272]
	bic.w r0, r2, r0
	ldr.w r10, [sp, #92]
	eor.w r11, r0, r1
	bic.w r0, r4, r8
	eor.w r5, r0, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #364]
	str r5, [sp, #148]
	eor.w r1, r0, r11
	eor.w r0, r3, r5
	str r0, [sp, #284]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #1
	str r1, [sp, #172]
	orr.w r0, r0, r1, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #348]
	ldr r0, [sp, #328]
	ldr r1, [sp, #228]
	str r3, [sp, #236]
	bic.w r0, r1, r0
	ldr r1, [sp, #244]
	ldr r3, [sp, #224]
	eor.w r5, r0, r1
	ldr r0, [sp, #320]
	ldr.w r8, [sp, #76]
	bic.w r0, r12, r0
	str r5, [sp, #44]
	eor.w r1, r0, r10
	ldr r0, [sp, #264]
	str r1, [sp, #84]
	bic.w r0, r3, r0
	ldr r3, [sp, #220]
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #52]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #296]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r0, r5
	ldr r5, [sp, #124]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r4, r9, r1
	ldr.w r9, [sp, #60]
	eor.w r1, r4, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #120]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #292]
	bic.w r4, r6, r1
	eor.w r1, r4, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #136]
	eor.w r12, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #280]
	ldr r1, [sp, #356]
	str.w r12, [sp, #12]
	bics r0, r1
	ldr r1, [sp, #256]
	eor.w r6, r0, r3
	ldr r0, [sp, #340]
	str r6, [sp, #32]
	bic.w r0, r1, r0
	ldr r1, [sp, #268]
	eor.w r4, r0, r5
	ldr r0, [sp, #312]
	str r4, [sp, #80]
	bic.w r0, r1, r0
	ldr r1, [sp, #248]
	eors r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #36]
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #336]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r2, [sp, #240]
	bic.w r4, r1, r4
	ldr r1, [sp, #112]
	mov r6, r12
	eors r4, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r4, [sp, #108]
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #344]
	bic.w r4, r2, r4
	ldr r2, [sp, #96]
	eors r4, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r4, [sp, #128]
	eor.w lr, r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #332]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w lr, [sp, #16]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r5, r4
	ldr r4, [sp, #232]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r0, lr, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r5, r4
	ldr r4, [sp, #360]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r12, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r12, r5, r11
	ldr.w r11, [sp, #64]
	str r5, [sp, #48]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r5, r3, r4
	eor.w r3, r5, r11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #332]
	eor.w r4, r12, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #324]
	ldr.w r12, [sp, #28]
	bic.w r5, r1, r3
	ldr r1, [sp, #252]
	eors r1, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #104]
	eor.w r3, r4, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #300]
	bic.w r5, r2, r1
	ldr r1, [sp, #352]
	eors r1, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #124]
	eor.w r2, r3, r1
	ldr r3, [sp, #148]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r1, r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #216]
	str r1, [sp, #220]
	eor.w r4, r1, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #288]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r6, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r6, [sp, #244]
	bic.w r5, r10, r1
	ldr.w r10, [sp, #24]
	eor.w r1, r5, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #96]
	eors r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #304]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, lr, lsr #31
	ldr.w lr, [sp, #40]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r5, r6, r3
	ldr r6, [sp, #192]
	str r4, [sp, #56]
	eor.w r3, r5, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #300]
	eors r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #276]
	bic.w r5, r8, r3
	eor.w r3, r5, r10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #92]
	eors r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #260]
	bic.w r5, r9, r3
	eor.w r3, r5, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #112]
	eor.w r9, r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #100]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r0, r0, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r0, [sp, #216]
	eor.w r1, r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #328]
	str r1, [sp, #288]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #6
	orr.w r8, r0, r4, lsr #26
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #228]
	ldr r1, [sp, #20]
	bic.w r0, r6, r0
	str.w r8, [sp, #148]
	eor.w r6, r0, r3
	ldr r0, [sp, #224]
	ldr r3, [sp, #320]
	bic.w r0, r1, r0
	ldr r1, [sp, #264]
	str r6, [sp, #276]
	eors r1, r0
	ldr r0, [sp, #8]
	str r1, [sp, #304]
	bic.w r0, r12, r0
	eors r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #328]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #4]
	ldr r3, [sp, #296]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r6, r10, r1
	eor.w r1, r6, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #76]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp]
	ldr r6, [sp, #292]
	bic.w r3, lr, r1
	eor.w r1, r3, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #264]
	eor.w r10, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #280]
	ldr r1, [sp, #356]
	bic.w r0, r11, r0
	eor.w r6, r0, r1
	ldrd r3, r0, [sp, #268]
	ldr r1, [sp, #232]
	bics r0, r3
	ldr r3, [sp, #312]
	str r6, [sp, #296]
	eor.w r5, r0, r3
	ldr r0, [sp, #256]
	ldr r3, [sp, #340]
	bic.w r0, r1, r0
	str r5, [sp, #320]
	eor.w r12, r0, r3
	ldrd r3, r1, [sp, #248]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r0, r12, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r4, r1, r3
	ldr r3, [sp, #336]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r1, r4, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #256]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #352]
	ldr r3, [sp, #240]
	bic.w r4, r1, r3
	ldr r3, [sp, #344]
	eor.w r1, r4, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r4, r10, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r11, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r3, [sp, #308]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #280]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r4, r4, r11, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #44]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r5, r4, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r4, r11, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r3, [sp, #316]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r4, r4, r10, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r6, r5, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r6, [sp, #356]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r1, r4, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #32]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r4, r6, #25
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r1, [sp, #360]
	eor.w r0, r1, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r0, [sp, #316]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r5, [sp, #352]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r3, r4, r0, lsr #7
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r3, [sp, #344]
	bic.w r4, r3, r8
	ldr r3, [sp, #348]
	eor.w lr, r4, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #52]
	str.w lr, [sp, #192]
	eor.w r0, r5, r3
	ldr r3, [sp, #36]
	str r0, [sp, #308]
	eors r1, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r4, r0, #28
	str r1, [sp, #292]
	orr.w r3, r4, r1, lsr #4
	lsl.w r4, r9, #1
	orr.w r4, r4, r2, lsr #31
	lsls r2, r2, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r1, r10, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r4, [sp, #72]
	ldr r0, [sp, #116]
	eors r4, r1
	mov r6, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r2, r9, lsr #31
	ldr r2, [sp, #68]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r1, r1, r11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r1, [sp, #240]
	eors r1, r0
	str r4, [sp, #272]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r4, #3
	str r1, [sp, #268]
	orr.w r4, r0, r1, lsr #29
	ldr r1, [sp, #160]
	lsls r0, r2, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r5, [sp, #12]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r4, [sp, #116]
	orr.w r0, r0, r1, lsr #31
	str r3, [sp, #340]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eors r0, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r5, [sp, #328]
	str r0, [sp, #24]
	eors r5, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #16]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r2, lsr #31
	ldr.w r10, [sp, #220]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r9, r1, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r5, #20
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r1, r12, r9
	ldr.w r12, [sp, #364]
	str r1, [sp, #252]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r1, lsr #12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #328]
	bic.w r0, r4, r0
	ldr r4, [sp, #236]
	eor.w r8, r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #48]
	ldr.w r11, [sp, #216]
	eor.w r1, r12, r0
	ldr r0, [sp, #96]
	str r1, [sp, #248]
	eor.w r2, r4, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #12
	str r2, [sp, #228]
	orr.w r3, r0, r2, lsr #20
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #164]
	str r5, [sp, #260]
	eor.w r1, r10, r0
	ldr r0, [sp, #140]
	str r3, [sp, #312]
	eor.w r2, r11, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #11
	str r2, [sp, #68]
	orr.w r0, r0, r2, lsr #21
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	ldr r2, [sp, #88]
	str r0, [sp, #140]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	eor.w r5, r6, r2
	movw r3, #32906
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r2, [sp, #304]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 33
		a ^ c
	eors r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #160]
	eor.w r0, r0, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r1, [sp, #72]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r0, r0, lr
	ldr.w lr, [sp, #24]
	mov r1, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r6, [sp, #324]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r3, lr, r2
	ldr r2, [sp, #320]
	str r3, [sp, #64]
	eor.w r2, r2, r9
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r3, #27
	str r2, [sp, #60]
	orr.w r6, r3, r2, lsr #5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #200]
	ldr r2, [sp, #240]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r5, [sp, #336]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r3, r2
	ldr r2, [sp, #188]
	str r3, [sp, #52]
	eors r1, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r3, #4
	str r1, [sp, #48]
	orr.w r5, r3, r1, lsr #28
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #300]
	str r5, [sp, #304]
	eor.w r2, r4, r1
	ldr r1, [sp, #332]
	str r2, [sp, #44]
	eor.w r1, r1, r12
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r2, #10
	str r1, [sp, #40]
	orr.w r2, r3, r1, lsr #22
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r2, [sp, #96]
	bic.w r3, r2, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #80]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r3, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #232]
	eor.w r12, r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #176]
	ldr r2, [sp, #360]
	eor.w r0, r10, r3
	ldr r3, [sp, #152]
	str r0, [sp, #176]
	eor.w r5, r11, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r0, #30
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str.w r8, [sp, #224]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r3, r5, lsr #2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r3, r2, r1
	ldr r1, [sp, #84]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r5, r5, #30
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r2, [sp, #352]
	str r3, [sp, #152]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r3, #23
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r8, r2, r1
	ldr r2, [sp, #296]
	str r6, [sp, #320]
	eor.w r10, r2, r9
	ldr r2, [sp, #276]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r3, r8, lsr #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r0, [sp, #244]
	eor.w r4, r2, lr
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r11, r10, #7
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r1, [sp, #300]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r2, r11, r4, lsr #25
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r2, [sp, #84]
	bic.w r6, r2, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #284]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r6, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #172]
	ldr r2, [sp, #356]
	ldr r3, [sp, #260]
	lsls r0, r0, #1
	orr.w r11, r0, r1, lsr #31
	ldr r0, [sp, #56]
	ldr r1, [sp, #288]
	str.w r11, [sp, #332]
	lsls r0, r0, #6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str.w r9, [sp, #32]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r0, r1, lsr #26
	ldr r0, [sp, #316]
	str r1, [sp, #100]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r9, r12, r6
	str r6, [sp, #188]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #25
	ldr.w r12, [sp, #240]
	orr.w r0, r0, r2, lsr #7
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #296]
	bics r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #308]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r11, r11, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #292]
	ldr r2, [sp, #272]
	str.w r11, [sp, #164]
	lsls r0, r0, #28
	orr.w r1, r0, r1, lsr #4
	ldr r0, [sp, #268]
	str r1, [sp, #308]
	str.w r9, [sp, #36]
	lsls r0, r0, #3
	orr.w r2, r0, r2, lsr #29
	ldr r0, [sp, #252]
	str r2, [sp, #316]
	lsls r0, r0, #20
	orr.w r0, r0, r3, lsr #12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #260]
	bic.w r0, r2, r0
	eor.w r6, r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #228]
	ldr r1, [sp, #248]
	str r6, [sp, #200]
	lsls r0, r0, #12
	orr.w r3, r0, r1, lsr #20
	ldr r0, [sp, #68]
	ldr r1, [sp, #72]
	str r3, [sp, #88]
	lsls r0, r0, #11
	orr.w r1, r0, r1, lsr #21
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	ldr r0, [sp, #144]
	str r1, [sp, #252]
	eor.w r2, r12, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r1, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #60]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 33
		a ^ c
	eor r0, r0, #-2147483648
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r2, [sp, #292]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #144]
	eors r0, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r6, r1, #27
	ldr r1, [sp, #64]
	ldr r2, [sp, #48]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r0, r0, r11
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r3, [sp, #40]
	mov r11, r12
	orr.w r1, r6, r1, lsr #5
	str r1, [sp, #288]
	lsls r6, r2, #4
	ldr r2, [sp, #52]
	orr.w r2, r6, r2, lsr #28
	lsls r6, r3, #10
	ldr r3, [sp, #44]
	str r2, [sp, #80]
	orr.w r3, r6, r3, lsr #22
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r3, [sp, #276]
	bic.w r6, r3, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r4, #7
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r6, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #176]
	orr.w r2, r3, r10, lsr #25
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r6, [sp, #228]
	eors r0, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r6, r8, #23
	orr.w r5, r5, r1, lsr #2
	ldr r1, [sp, #152]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r2, [sp, #268]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r5, [sp, #72]
	orr.w r1, r6, r1, lsr #9
	str r1, [sp, #272]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r3, r2, r1
	ldr r4, [sp, #352]
	eors r3, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #172]
	eor.w r1, r0, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r0, r9, #1
	str r1, [sp, #356]
	orr.w r0, r0, r1, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r0, [sp, #64]
	ldr r0, [sp, #76]
	ldr r3, [sp, #32]
	eor.w r1, r0, lr
	ldr r0, [sp, #256]
	str r1, [sp, #76]
	eor.w r2, r0, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #8
	str r2, [sp, #68]
	orr.w r2, r0, r2, lsr #24
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #132]
	ldr r1, [sp, #324]
	ldr.w r8, [sp, #360]
	eors r1, r0
	ldr r0, [sp, #204]
	str r1, [sp, #132]
	eor.w r5, r12, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #18
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r2, [sp, #248]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r0, r5, lsr #14
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #348]
	str r1, [sp, #284]
	bics r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r5, [sp, #28]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r10, r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #120]
	ldr r6, [sp, #216]
	eor.w r1, r4, r0
	ldr r0, [sp, #108]
	str r1, [sp, #60]
	eor.w r2, r8, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #21
	str r2, [sp, #108]
	orr.w r2, r0, r2, lsr #11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #264]
	str r2, [sp, #120]
	eor.w r1, r0, lr
	ldr r0, [sp, #280]
	str r1, [sp, #52]
	eors r3, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r1, #14
	ldr.w lr, [sp, #236]
	orr.w r1, r0, r3, lsr #18
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #336]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r3, [sp, #48]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r0, r1
	str r1, [sp, #280]
	eor.w r12, r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #104]
	ldr r2, [sp, #364]
	str.w r10, [sp, #176]
	eors r2, r0
	ldr r0, [sp, #92]
	str r2, [sp, #104]
	eor.w r3, lr, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r2, #13
	str r3, [sp, #92]
	orr.w r3, r0, r3, lsr #19
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #196]
	ldr r2, [sp, #220]
	str r3, [sp, #56]
	eor.w r5, r2, r0
	ldr r0, [sp, #180]
	str r5, [sp, #32]
	eor.w r1, r6, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r5, #29
	str r1, [sp, #180]
	orr.w r5, r0, r1, lsr #3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #340]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #184]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r0, r5
	str r5, [sp, #264]
	eors r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r3, r6, r1
	ldr r1, [sp, #212]
	str r3, [sp, #184]
	eors r2, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r3, #15
	str r2, [sp, #212]
	orr.w r3, r1, r2, lsr #17
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #128]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #204]
	eor.w r0, r0, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r2, r8, r1
	ldr r1, [sp, #136]
	str r2, [sp, #360]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r0, r0, r10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r5, r4, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #24
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r3, [sp, #44]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r2, r1, r5, lsr #8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #320]
	str r2, [sp, #256]
	bics r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r6, [sp, #364]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r1, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #136]
	eor.w r4, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #168]
	ldr r0, [sp, #324]
	eor.w r2, r11, r1
	ldr r1, [sp, #156]
	str r2, [sp, #220]
	eor.w r3, r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str.w r12, [sp, #152]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r8, r1, r3, lsr #23
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #112]
	str.w r8, [sp, #40]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r3, #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r0, lr, r1
	ldr r1, [sp, #124]
	str r0, [sp, #324]
	eor.w r2, r6, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r6, [sp, #244]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r11, r0, #2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #64]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r11, r2, lsr #30
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #352]
	bics r6, r0
	eor.w r6, r6, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r6, [sp, #216]
	eor.w r0, r4, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	str r0, [sp, #128]
	eors r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r0, [sp, #364]
	ldr r0, [sp, #356]
	ldr r1, [sp, #76]
	lsls r0, r0, #1
	orr.w r0, r0, r9, lsr #31
	str r0, [sp, #168]
	ldr r0, [sp, #68]
	lsls r0, r0, #8
	orr.w r9, r0, r1, lsr #24
	ldr r0, [sp, #28]
	ldr r1, [sp, #132]
	str.w r9, [sp, #16]
	lsls r0, r0, #18
	orr.w r10, r0, r1, lsr #14
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #332]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #60]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r0, r10
	str.w r10, [sp, #20]
	eor.w r12, r0, r9
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #108]
	str.w r12, [sp, #196]
	lsls r0, r0, #21
	orr.w lr, r0, r1, lsr #11
	ldr r0, [sp, #48]
	ldr r1, [sp, #52]
	str.w lr, [sp, #4]
	lsls r0, r0, #14
	orr.w r4, r0, r1, lsr #18
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #292]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #104]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bics r0, r4
	mov r11, r4
	eor.w r6, r0, lr
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #92]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r4, [sp, #28]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r4, [sp, #32]
	lsls r0, r0, #13
	orr.w r1, r0, r1, lsr #19
	ldr r0, [sp, #180]
	str r1, [sp, #240]
	str r6, [sp, #132]
	lsls r0, r0, #29
	orr.w r8, r0, r4, lsr #3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #308]
	str.w r8, [sp, #24]
	bic.w r0, r0, r8
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #236]
	eors r0, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #360]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r12, r12, r0
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #212]
	lsls r4, r0, #15
	ldr r0, [sp, #184]
	orr.w r0, r4, r0, lsr #17
	lsls r4, r5, #24
	orr.w r6, r4, r1, lsr #8
	ldr r1, [sp, #220]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #288]
	str r6, [sp, #32]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r3, r3, r1, lsr #23
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r5, r4, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r2, #2
	ldr r2, [sp, #324]
	mov r4, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r6, r5, r0
	mov r5, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #12]
	eor.w r0, r12, r6
	str r6, [sp, #124]
	ldr r6, [sp, #72]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r1, r2, lsr #30
	mov r12, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r3, [sp, #8]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r2, r6, r1
	eors r2, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #212]
	eors r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r2, [sp, #168]
	str r0, [sp, #108]
	eors r2, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #300]
	ldr r3, [sp, #244]
	str r2, [sp, #360]
	bics r0, r3
	ldr r3, [sp, #352]
	eors r3, r0
	ldr r0, [sp, #272]
	str r3, [sp, #76]
	bics r0, r6
	eor.w r6, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #364]
	str r6, [sp, #48]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r1, r1, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r3, r0
	eor.w r0, r6, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r0, [sp, #60]
	lsls r0, r0, #14
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r2, [sp, #296]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r3, lsr #18
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #324]
	bic.w r0, r10, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	str r3, [sp, #64]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r3, r0, r2
	ldr r2, [sp, #252]
	bic.w r0, r11, lr
	ldr r6, [sp, #316]
	eors r2, r0
	ldr r0, [sp, #240]
	str r3, [sp, #92]
	bic.w r0, r8, r0
	str r2, [sp, #244]
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #168]
	eors r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r2, r4, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #276]
	ldr.w r11, [sp, #120]
	eors r2, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #184]
	eors r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r2, [sp, #268]
	ldr.w r8, [sp, #140]
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #112]
	eor.w r4, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #284]
	ldr r1, [sp, #248]
	ldr.w r12, [sp, #56]
	bics r0, r1
	ldr r1, [sp, #344]
	ldr r5, [sp, #116]
	eor.w r2, r0, r1
	ldr r0, [sp, #280]
	ldr.w r10, [sp, #44]
	bic.w r0, r0, r11
	ldr.w r9, [sp, #96]
	eor.w r1, r0, r8
	ldr r0, [sp, #264]
	str r1, [sp, #220]
	bic.w r0, r0, r12
	ldr.w lr, [sp, #40]
	eors r0, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #156]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #256]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r0, r2
	ldr r6, [sp, #84]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r1, r1, r10
	str r2, [sp, #72]
	eor.w r1, r1, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #180]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #352]
	str r4, [sp, #52]
	bic.w r1, r1, lr
	eors r1, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #104]
	eor.w r2, r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r4, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #356]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r2, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	str r2, [sp, #68]
	eor.w r3, r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r2, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r1, [sp, #36]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r4, lsr #31
	str r3, [sp, #352]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r4, r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #316]
	ldr r1, [sp, #240]
	str r4, [sp, #356]
	bic.w r0, r1, r0
	ldr r1, [sp, #260]
	eors r0, r1
	bic.w r1, r12, r5
	ldr r5, [sp, #328]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r2, r3, r0
	str r2, [sp, #36]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r1, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r3, r4, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r3, [sp]
	lsls r5, r3, #12
	orr.w r2, r5, r2, lsr #20
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r2, [sp, #316]
	bic.w r5, r11, r8
	ldr r2, [sp, #312]
	ldr r3, [sp, #344]
	eors r2, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #140]
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r2, [sp, #248]
	ldr.w r11, [sp, #148]
	bic.w r5, r2, r3
	ldr r3, [sp, #304]
	eor.w r2, r5, r11
	bic.w r5, r10, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #240]
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r2, r5, r3
	ldr r3, [sp, #300]
	bic.w r5, lr, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r1, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r4, r5, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #56]
	eor.w lr, r1, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #252]
	ldr r2, [sp, #4]
	ldr r3, [sp, #16]
	bic.w r5, r2, r1
	ldr r2, [sp, #88]
	ldr r6, [sp, #12]
	eor.w r1, r5, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #120]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #296]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r4, [sp, #248]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r5, r3, r1
	ldr r3, [sp, #100]
	ldr.w r8, [sp, #316]
	eor.w r1, r5, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r1, [sp, #252]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r1, [sp, #276]
	ldr r5, [sp, #8]
	bics r6, r1
	ldr r1, [sp, #80]
	ldr.w r9, [sp, #208]
	eors r6, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r6, [sp, #84]
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r6, [sp, #268]
	bic.w r6, r5, r6
	ldr r5, [sp, #272]
	eor.w r4, r6, r5
	ldr r6, [sp, #332]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eor.w r5, r0, r4
	str r4, [sp, #272]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r6, r3, r6
	ldr r3, [sp, #308]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r5, #1
	orr.w r12, r0, lr, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #20]
	eor.w r4, r6, r0
	ldr r0, [sp, #292]
	str r4, [sp, #276]
	bic.w r6, r2, r0
	ldr r0, [sp, #28]
	ldr r2, [sp, #260]
	eors r0, r6
	str r0, [sp, #268]
	bic.w r6, r2, r3
	ldr r2, [sp, #24]
	ldr r3, [sp, #348]
	eors r2, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #96]
	eor.w r6, r2, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #288]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r6, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r2, r11, r3
	bic.w r4, r1, r0
	ldr r0, [sp, #32]
	ldr r3, [sp, #284]
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #116]
	eor.w r4, r6, r0
	ldr r0, [sp, #48]
	eor.w r6, r4, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	ldr r0, [sp, #144]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r1, r6, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #324]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	eors r0, r1
	str r0, [sp, #332]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r8, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	str r1, [sp, #344]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r9, #164]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r0, [sp, #64]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r4, r2, r3
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	ldr r1, [sp, #60]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r2, [sp, #336]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #14
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r3, [sp, #312]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r12, r0, r1, lsr #18
	ldr r0, [sp, #36]
	ldr r1, [sp]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r2, r3, r2
	ldr r3, [sp, #328]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r4, [sp, #292]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r0, r1, lsr #20
	lsl.w r0, lr, #1
	orr.w r10, r0, r5, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #280]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r1, [sp, #308]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r2
	ldr r2, [sp, #340]
	str r0, [sp, #284]
	bic.w r2, r3, r2
	ldr r3, [sp, #264]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w r12, [sp, #288]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r2, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r2, [sp, #148]
	eor.w r3, r2, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r2, [sp, #320]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	eors r3, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r4, [sp, #304]
	ldr r0, [sp, #256]
	bics r4, r2
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 13
		a ^ b ^ c ^ d ^ e
	str r0, [sp, #100]
	eors r3, r0
	ldr r0, [sp, #76]
	ldr r4, [sp, #108]
	eors r3, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	ldr r0, [sp, #160]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r2, r3, r10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 107
		a ^ b
	str r2, [sp, #340]
	eors r0, r2
	ldr r2, [sp, #128]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #328]
	bic.w r0, r1, r0
	eor.w r0, r0, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r9, #160]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r2, #1
	orr.w r0, r0, r4, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r1, r0, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #72]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r1, [sp, #336]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r0, r1
	mov r10, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r4, #1
	orr.w r1, r1, r2, lsr #31
	lsls r4, r0, #11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w lr, r1, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #92]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r5, [sp, #52]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r1, r1, lr
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w lr, [sp, #348]
	orr.w r2, r4, r1, lsr #21
	lsls r4, r6, #1
	orr.w r4, r4, r3, lsr #31
	lsls r3, r3, #1
	orr.w r3, r3, r6, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	ldr r6, [sp, #68]
	eor.w r11, r4, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r4, [sp, #124]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 18
		a ^ rotate_left::<1, 63>(b)
	eor.w r12, r3, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #136]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r1, #11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r4, r4, r11
	eor.w r3, r3, r12
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r1, r0, lsr #21
	str r1, [sp, #312]
	lsls r6, r4, #21
	lsls r0, r3, #21
	orr.w r5, r6, r3, lsr #11
	orr.w r0, r0, r4, lsr #11
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #264]
	bics r0, r1
	ldr r1, [sp, #308]
	bic.w r6, r5, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str r2, [sp, #320]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r9, #40]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #356]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r6, r6, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #56]
	ldr r2, [sp, #352]
	eors r0, r1
	ldr r1, [sp, #84]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r6, [r9, #44]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r3, r2, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r0, #13
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r5, [sp, #280]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r8, r1, r3, lsr #19
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #104]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w r12, [sp, #300]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r6, r10, r1
	ldr r1, [sp, #112]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	str.w r11, [sp, #296]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r10, lr, r1
	ldr r1, [sp, #132]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r4, r6, #29
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w lr, r11, r1
	ldr r1, [sp, #152]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r5, r4, r10, lsr #3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r5, [sp, #160]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r2, r12, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r1, lr, #28
	mov r12, r5
	ldr.w r11, [sp, #364]
	orr.w r1, r1, r2, lsr #4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r1, [sp, #260]
	bics r1, r5
	ldr r5, [sp, #344]
	eor.w r1, r1, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r1, [r9, #132]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r3, #13
	orr.w r3, r1, r0, lsr #19
	lsl.w r0, r10, #29
	orr.w r4, r0, r6, lsr #3
	lsls r0, r2, #28
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #164]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, lr, lsr #4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #256]
	bics r0, r4
	ldr.w lr, [sp, #340]
	eors r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r9, #128]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #192]
	eors r1, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r4, [sp, #152]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r0, r0, lr
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r1, #3
	orr.w r6, r2, r0, lsr #29
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r2, r12, r8
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r0, #3
	orr.w r1, r0, r1, lsr #29
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r4, r3
	eors r2, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r2, [r9, #92]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r1
	mov r4, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str r1, [sp, #164]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #96]
	mov r12, r9
	ldr r2, [sp, #360]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r9, #88]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r8, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r1, r2
	ldr r2, [sp, #148]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r6, [sp, #192]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r2, r2, r11
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r6, r1, #20
	orr.w r6, r6, r2, lsr #12
	lsls r2, r2, #20
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r9, #52]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r3, r4
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r2, r1, lsr #12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r9, #48]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #172]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r1, [sp, #144]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #188]
	eor.w r9, r5, r0
	ldr r0, [sp, #352]
	eor.w lr, lr, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r1, r9, #18
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r6, [sp, #148]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r8, r1, lr, lsr #14
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #120]
	ldr r4, [sp, #168]
	eor.w r3, r0, r1
	ldr r1, [sp, #140]
	ldr r0, [sp, #356]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r8, [sp, #188]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r6, r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r3, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #336]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r10, r1, r6, lsr #31
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #348]
	eor.w r5, r1, r4
	ldr r1, [sp, #156]
	eor.w r4, r0, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r5, #6
	orr.w r0, r1, r4, lsr #26
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #304]
	bic.w r1, r0, r10
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r0, r6, #1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r1, r1, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r1, [r12, #180]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r1, lr, #18
	orr.w r2, r1, r9, lsr #14
	orr.w r6, r0, r3, lsr #31
	lsls r0, r4, #6
	orr.w r1, r0, r5, lsr #26
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r1, [sp, #168]
	bic.w r0, r1, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #360]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r2
	mov r4, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #116]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r12, #176]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #100]
	eors r1, r3
	ldr.w r9, [sp, #296]
	eor.w r0, r0, r11
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r1, #8
	str r2, [sp, #172]
	orr.w r5, r3, r0, lsr #24
	lsls r0, r0, #8
	orr.w r1, r0, r1, lsr #24
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r6, r2
	bic.w r3, r10, r8
	eors r0, r1
	eors r3, r5
	str r5, [sp, #156]
	str r1, [sp, #140]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r12, #136]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #196]
	ldr r1, [sp, #176]
	ldr r5, [sp, #300]
	eor.w r0, r0, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r3, [r12, #140]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r1, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r0, #25
	orr.w r2, r3, r1, lsr #7
	lsls r1, r1, #25
	orr.w r0, r1, r0, lsr #7
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r0, [sp, #176]
	bics r0, r4
	ldr r3, [sp, #304]
	eors r0, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r12, #16]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #252]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r3, r2, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #352]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r3, r3, r10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r3, [r12, #20]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r8, r1, r0
	ldr r0, [sp, #240]
	ldr r1, [sp, #356]
	ldr r3, [sp, #348]
	eors r1, r0
	ldr r0, [sp, #184]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str r2, [sp, #196]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsl.w r2, r8, #10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w lr, r3, r0
	ldr r0, [sp, #180]
	ldr r3, [sp, #336]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r2, r2, r1, lsr #22
	lsl.w r6, lr, #15
	lsls r1, r1, #10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r4, r3, r0
	ldr r0, [sp, #216]
	ldr r3, [sp, #212]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r1, r1, r8, lsr #22
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r0, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r10, r6, r4, lsr #17
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r3, r3, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	str.w r10, [sp, #240]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r5, r0, #24
	orr.w r6, r5, r3, lsr #8
	str r6, [sp, #252]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r11, r6, r10
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r3, #24
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r6, r11, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r6, [r12, #108]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r6, r4, #15
	mov r5, r10
	orr.w r10, r6, lr, lsr #17
	orr.w r9, r3, r0, lsr #8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r9, r10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #344]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r12, #104]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #200]
	mov r11, r12
	ldr r6, [sp, #340]
	eors r0, r3
	ldr r3, [sp, #224]
	ldr r4, [sp, #360]
	eors r3, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r6, r3, #4
	orr.w r8, r6, r0, lsr #28
	lsls r0, r0, #4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r6, r5, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r5, r0, r3, lsr #28
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r10, r1
	eors r0, r5
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r12, #64]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r2, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r2, [sp, #268]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r6, r6, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r6, [r12, #68]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r6, r4, r2
	ldr r2, [sp, #284]
	ldr r4, [sp, #364]
	ldr r3, [sp, #260]
	eors r4, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r6, #27
	orr.w lr, r2, r4, lsr #5
	ldr r2, [sp, #264]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r0, r0, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r12, #28]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r1, r5
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r4, #27
	orr.w r12, r1, r6, lsr #5
	ldr r6, [sp, #324]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r0, r0, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #24]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #332]
	ldr r1, [sp, #280]
	bics r0, r6
	ldr r4, [sp, #288]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #124]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #328]
	bics r0, r4
	eors r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #120]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r6, r1
	ldr r6, [sp, #320]
	ldr r1, [sp, #144]
	eors r0, r6
	ldr r6, [sp, #312]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #84]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r4, r2
	eors r0, r6
	ldr r6, [sp, #148]
	ldr r2, [sp, #160]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #80]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r6, r3
	eors r0, r2
	ldr r2, [sp, #256]
	ldr r4, [sp, #152]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #172]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r1, r2
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #168]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #192]
	ldr r4, [sp, #176]
	bics r0, r6
	eors r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #12]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #164]
	ldr r3, [sp, #196]
	bics r0, r1
	ldr r1, [sp, #156]
	eors r0, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #8]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #188]
	ldr r2, [sp, #140]
	bics r0, r1
	eors r0, r3
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #100]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldr r0, [sp, #172]
	bics r0, r2
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #96]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r1, r3
	ldr r1, [sp, #304]
	eors r0, r1
	ldr r1, [sp, #168]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #60]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r2, r4
	eors r0, r1
	ldr r1, [sp, #252]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #56]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r8, lr
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #188]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r5, r12
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r2, [sp, #356]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r0, r0, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #184]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, lr, r1
	ldr r1, [sp, #240]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r5, [sp, #300]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #148]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r12, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #352]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r0, r0, r10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #144]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #272]
	ldr r4, [sp, #296]
	eors r0, r1
	ldr r1, [sp, #248]
	eor.w r3, r2, r1
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r1, r0, #2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r2, [sp, #336]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r8, r1, r3, lsr #30
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #220]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r3, r3, #2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eor.w r6, r2, r1
	ldr r1, [sp, #244]
	ldr r2, [sp, #348]
	eors r1, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r6, #30
	orr.w r12, r2, r1, lsr #2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r2, [sp, #204]
	eors r2, r5
	ldr r5, [sp, #236]
	eors r5, r4
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r4, r2, #23
	orr.w lr, r4, r5, lsr #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r4, lr, r12
	eor.w r4, r4, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r4, [r11, #196]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r4, r3, r0, lsr #30
	lsls r0, r1, #30
	orr.w r9, r0, r6, lsr #2
	lsls r0, r5, #23
	orr.w r10, r0, r2, lsr #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r1, [sp, #344]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r10, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r2, [sp, #340]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r0, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #192]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r0, [sp, #228]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r5, r12, r8
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r3, [sp, #292]
	eors r0, r1
	ldr r1, [sp, #232]
	ldr r6, [sp, #360]
	eors r1, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r2, r1, #9
	orr.w r2, r2, r0, lsr #23
	lsls r0, r0, #9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r5, r2
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r5, [r11, #156]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	ldr r5, [sp, #364]
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r0, r0, r1, lsr #23
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r1, r9, r4
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r5, r3
	ldr r3, [sp, #276]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r1, r0
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r1, [r11, #152]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 23
		rotate_left::<LEFT, RIGHT>(a ^ b)
	eors r3, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	lsls r6, r5, #7
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r1, r8, r2
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r6, r6, r3, lsr #25
	lsls r3, r3, #7
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eors r1, r6
		// /home/keks/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs : 261
		return intrinsics::rotate_left(self, n);
	orr.w r3, r3, r5, lsr #25
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r1, [r11, #116]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r1, r4, r0
	bics r0, r3
	eors r1, r3
	eor.w r0, r0, r10
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #72]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r6, lr
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r1, [r11, #112]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	eor.w r0, r0, r12
	bic.w r1, r2, r6
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #36]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	bic.w r0, r3, r10
	eor.w r1, r1, lr
	eor.w r0, r0, r9
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r1, [r11, #76]
	str.w r0, [r11, #32]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldrd r1, r0, [sp, #308]
	bics r0, r1
	ldr r1, [sp, #328]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 33
		a ^ c
	eor r0, r0, #-2147450880
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 28
		a ^ (b & !c)
	ldrd r1, r0, [sp, #316]
	bics r0, r1
	ldr r1, [sp, #332]
	eors r0, r1
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/portable_keccak.rs : 33
		a ^ c
	eor r0, r0, #-2147483648
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/traits.rs : 22
		arr[5 * j + i] = v;
	str.w r0, [r11, #4]
		// /home/keks/code/github.com/cryspen/libcrux-iot/libcrux/libcrux-sha3/src/lib.rs : 362
		}
	add sp, #368
	pop.w {r8, r9, r10, r11}
	pop {r4, r5, r6, r7, pc}
