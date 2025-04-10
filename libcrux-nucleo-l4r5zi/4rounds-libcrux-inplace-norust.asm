.section .text.libcrux_sha3::portable::incremental::keccakf1660_4rounds,"ax",%progbits
	.p2align	1
	.type	libcrux_sha3::portable::incremental::keccakf1660_4rounds,%function
	.code	16
	.thumb_func
libcrux_sha3::portable::incremental::keccakf1660_4rounds:
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
	.pad	#344
	sub sp, #344
	mov r2, r0
	ldr r0, [r0, #44]
	ldr r4, [r2, #124]
	ldrd r5, r1, [r2, #80]
	eors r0, r1
	ldr r6, [r2, #40]
	eors r0, r4
	ldr r1, [r2, #120]
	ldrd r12, r3, [r2, #160]
	eor.w r4, r0, r3
	eor.w r0, r5, r6
	ldr r5, [r2, #24]
	eors r0, r1
	ldm.w r2, {r1, r3, r6}
	eor.w r0, r0, r12
	str r6, [sp, #336]
	eor.w r8, r0, r1
	ldr r6, [r2, #12]
	ldr r1, [r2, #64]
	str r6, [sp, #316]
	eor.w r6, r4, r3
	str r4, [sp, #264]
	ldr r4, [r2, #104]
	str r1, [sp, #308]
	eors r1, r5
	str r5, [sp, #236]
	eors r1, r4
	ldr.w r5, [r2, #144]
	str r5, [sp, #248]
	eors r1, r5
	ldr.w r5, [r2, #184]
	str r0, [sp, #332]
	lsl.w r0, r8, #1
	eors r1, r5
	orr.w r0, r0, r6, lsr #31
	str r5, [sp, #280]
	eor.w r9, r1, r0
	str r1, [sp, #160]
	lsls r0, r6, #1
	ldr r5, [r2, #28]
	orr.w r0, r0, r8, lsr #31
	ldr r1, [r2, #68]
	str r4, [sp, #312]
	ldr r4, [r2, #108]
	str r1, [sp, #284]
	eors r1, r5
	str r5, [sp, #228]
	eors r1, r4
	ldr.w r5, [r2, #148]
	str r5, [sp, #232]
	eors r1, r5
	ldr.w r5, [r2, #188]
	str r5, [sp, #244]
	eors r1, r5
	str r1, [sp, #144]
	eor.w r12, r1, r0
	ldr r0, [r2, #116]
	ldr r1, [r2, #112]
	str r0, [sp, #192]
	eor.w r0, r0, r12
	eor.w r3, r1, r9
	str r1, [sp, #180]
	lsls r1, r0, #7
	str r3, [sp, #260]
	orr.w lr, r1, r3, lsr #25
	ldr r1, [r2, #20]
	ldr r3, [r2, #60]
	str r0, [sp, #272]
	ldr r0, [r2, #100]
	str r1, [sp, #240]
	eors r1, r3
	str r0, [sp, #212]
	eors r1, r0
	ldr.w r0, [r2, #140]
	str r0, [sp, #220]
	eors r1, r0
	ldr.w r0, [r2, #180]
	str r0, [sp, #196]
	eor.w r5, r1, r0
	ldr r0, [r2, #16]
	ldr r1, [r2, #56]
	str r4, [sp, #268]
	ldr r4, [r2, #96]
	str r1, [sp, #104]
	eors r1, r0
	str r0, [sp, #224]
	eors r1, r4
	ldr.w r0, [r2, #136]
	str r0, [sp, #216]
	eors r1, r0
	ldr.w r0, [r2, #176]
	str r0, [sp, #168]
	eors r0, r1
	lsls r1, r5, #1
	strd r0, r5, [sp, #152]
	orr.w r1, r1, r0, lsr #31
	str r1, [sp, #164]
	eors r6, r1
	lsls r1, r0, #1
	orr.w r0, r1, r5, lsr #31
	str r0, [sp, #292]
	eor.w r10, r0, r8
	ldr.w r0, [r2, #168]
	str r3, [sp, #132]
	ldr.w r3, [r2, #172]
	str r0, [sp, #96]
	eor.w r0, r0, r10
	str r4, [sp, #200]
	eor.w r4, r6, r3
	str r3, [sp, #88]
	lsls r3, r0, #2
	str r4, [sp, #252]
	orr.w r4, r3, r4, lsr #30
	str r0, [sp, #256]
	ldr r3, [r2, #52]
	ldr r0, [r2, #48]
	str r3, [sp, #76]
	eors r3, r6
	str r0, [sp, #84]
	eor.w r0, r0, r10
	str r3, [sp, #176]
	lsls r3, r3, #12
	orr.w r5, r3, r0, lsr #20
	str.w lr, [sp, #320]
	bic.w r3, r5, r4
	str r0, [sp, #148]
	eor.w lr, lr, r3
	ldr r3, [r2, #72]
	ldr r0, [r2, #76]
	str r3, [sp, #80]
	eor.w r3, r3, r9
	str r0, [sp, #92]
	eor.w r0, r0, r12
	str r3, [sp, #140]
	lsls r3, r3, #20
	str r4, [sp, #324]
	orr.w r4, r3, r0, lsr #12
	ldr.w r3, [r2, #132]
	str r0, [sp, #136]
	ldr.w r0, [r2, #128]
	str r3, [sp, #56]
	eors r3, r6
	str r0, [sp, #64]
	eor.w r0, r0, r10
	str r3, [sp, #120]
	lsls r3, r3, #13
	orr.w r3, r3, r0, lsr #19
	str r3, [sp, #276]
	bic.w r3, r5, r3
	str r0, [sp, #116]
	eor.w r8, r4, r3
	ldr r0, [r2, #36]
	ldr r3, [r2, #32]
	str r0, [sp, #68]
	eor.w r0, r0, r12
	str r3, [sp, #60]
	eor.w r3, r3, r9
	str r3, [sp, #112]
	str r4, [sp, #304]
	lsls r3, r3, #27
	orr.w r4, r3, r0, lsr #5
	str r0, [sp, #108]
	ldr r0, [r2, #88]
	ldr r3, [r2, #92]
	str r0, [sp, #40]
	eor.w r0, r0, r10
	eor.w r11, r6, r3
	str r3, [sp, #28]
	lsls r3, r0, #10
	str r4, [sp, #296]
	orr.w r3, r3, r11, lsr #22
	str r3, [sp, #300]
	bic.w r3, r5, r3
	str.w lr, [sp, #188]
	eors r3, r4
	ldr.w r4, [r2, #152]
	str r3, [sp, #172]
	eor.w r3, r3, r8
	eor.w lr, lr, r3
	ldr.w r3, [r2, #156]
	eor.w r1, r4, r9
	str r4, [sp, #32]
	eor.w r4, r3, r12
	str r0, [sp, #72]
	mov r0, r5
	lsls r5, r1, #9
	str r3, [sp, #44]
	orr.w r3, r5, r4, lsr #23
	str r1, [sp, #48]
	lsls r4, r4, #9
	ldr r5, [sp, #336]
	ldr r1, [sp, #316]
	eor.w r10, r10, r5
	str.w r8, [sp, #208]
	eor.w r8, r6, r1
	str r2, [sp, #100]
	lsl.w r5, r10, #1
	str r3, [sp, #328]
	orr.w r1, r5, r8, lsr #31
	str r1, [sp, #124]
	bic.w r5, r0, r1
	ldrd r2, r1, [r2, #192]
	eors r5, r3
	strd r2, r1, [sp, #20]
	eor.w r3, lr, r5
	eor.w lr, r1, r12
	eor.w r9, r9, r2
	ldr r1, [sp, #332]
	ldr r2, [sp, #292]
	str r5, [sp, #204]
	lsl.w r5, r9, #14
	eors r1, r2
	orr.w r6, r5, lr, lsr #18
	bic.w r5, r0, r1
	str r0, [sp, #340]
	ldr r0, [sp, #260]
	eors r5, r6
	str r6, [sp, #288]
	eor.w r6, r3, r5
	str r1, [sp, #292]
	lsls r3, r0, #7
	ldr r0, [sp, #272]
	ldr r1, [sp, #252]
	ldr r2, [sp, #148]
	orr.w r0, r3, r0, lsr #25
	str r5, [sp, #184]
	lsls r3, r1, #2
	ldr r1, [sp, #256]
	str r0, [sp, #272]
	str r6, [sp, #52]
	orr.w r1, r3, r1, lsr #30
	lsls r3, r2, #12
	ldr r2, [sp, #176]
	str r1, [sp, #128]
	orr.w r5, r3, r2, lsr #20
	ldr r2, [sp, #72]
	bic.w r3, r5, r1
	ldr r1, [sp, #116]
	eor.w r12, r0, r3
	ldr r0, [sp, #136]
	str r5, [sp, #332]
	str.w r12, [sp, #148]
	lsls r3, r0, #20
	ldr r0, [sp, #140]
	orr.w r0, r3, r0, lsr #12
	lsls r3, r1, #13
	ldr r1, [sp, #120]
	str r0, [sp, #260]
	orr.w r1, r3, r1, lsr #19
	str r1, [sp, #120]
	bic.w r3, r5, r1
	eor.w r1, r0, r3
	ldr r0, [sp, #108]
	str r1, [sp, #140]
	lsls r3, r0, #27
	ldr r0, [sp, #112]
	orr.w r0, r3, r0, lsr #5
	lsl.w r3, r11, #10
	orr.w r2, r3, r2, lsr #22
	str r0, [sp, #256]
	bic.w r3, r5, r2
	str r2, [sp, #116]
	eors r3, r0
	ldr r0, [sp, #48]
	str r3, [sp, #136]
	eors r3, r1
	lsl.w r1, r8, #1
	eor.w r3, r3, r12
	orr.w r2, r4, r0, lsr #23
	orr.w r0, r1, r10, lsr #31
	bic.w r1, r5, r0
	str r0, [sp, #112]
	eors r1, r2
	lsl.w r0, lr, #14
	str r2, [sp, #72]
	orr.w r2, r0, r9, lsr #18
	str r1, [sp, #176]
	eors r1, r3
	ldr r0, [sp, #264]
	ldr r3, [sp, #164]
	str r2, [sp, #252]
	eors r0, r3
	str r0, [sp, #108]
	bic.w r0, r5, r0
	ldr r3, [sp, #144]
	eors r0, r2
	str r0, [sp, #164]
	eors r1, r0
	lsls r0, r6, #1
	ldr r2, [sp, #160]
	orr.w r0, r0, r1, lsr #31
	str r1, [sp, #36]
	str r0, [sp, #48]
	lsls r0, r3, #1
	ldr r1, [sp, #316]
	orr.w r0, r0, r2, lsr #31
	ldr r5, [sp, #312]
	eors r0, r1
	ldr r1, [sp, #76]
	eors r0, r1
	ldr r1, [sp, #28]
	eors r0, r1
	ldr r1, [sp, #56]
	eors r0, r1
	ldr r1, [sp, #88]
	eor.w r8, r0, r1
	ldr r0, [sp, #132]
	ldr r1, [sp, #336]
	eor.w r6, r8, r0
	lsls r0, r2, #1
	orr.w r0, r0, r3, lsr #31
	ldr r2, [sp, #68]
	eors r0, r1
	ldr r1, [sp, #84]
	str r6, [sp, #132]
	eors r0, r1
	ldr r1, [sp, #40]
	eors r0, r1
	ldr r1, [sp, #64]
	eors r0, r1
	ldr r1, [sp, #96]
	eor.w r4, r0, r1
	ldr r0, [sp, #104]
	ldr r1, [sp, #60]
	eors r0, r4
	str r0, [sp, #336]
	lsls r0, r0, #6
	orr.w r3, r0, r6, lsr #26
	ldr r0, [sp, #80]
	str r3, [sp, #264]
	eors r0, r1
	ldr r1, [sp, #180]
	eors r0, r1
	ldr r1, [sp, #32]
	eors r0, r1
	ldr r1, [sp, #20]
	eors r0, r1
	ldr r1, [sp, #92]
	eors r1, r2
	ldr r2, [sp, #192]
	eors r1, r2
	ldr r2, [sp, #44]
	eors r1, r2
	ldr r2, [sp, #24]
	eor.w r6, r1, r2
	lsls r1, r0, #1
	ldr r2, [sp, #152]
	orr.w r1, r1, r6, lsr #31
	lsls r6, r6, #1
	eors r1, r2
	ldr r2, [sp, #156]
	orr.w r0, r6, r0, lsr #31
	eors r5, r1
	eors r0, r2
	ldr r2, [sp, #268]
	lsls r6, r5, #25
	str r5, [sp, #152]
	eors r2, r0
	str r2, [sp, #156]
	orr.w r6, r6, r2, lsr #7
	ldr r2, [sp, #328]
	str r6, [sp, #268]
	bic.w r6, r2, r6
	ldr r2, [sp, #196]
	eor.w lr, r6, r3
	str.w lr, [sp, #180]
	eor.w r3, r8, r2
	ldr r2, [sp, #168]
	str r3, [sp, #104]
	eors r2, r4
	lsls r6, r3, #29
	ldr r3, [sp, #236]
	orr.w r5, r6, r2, lsr #3
	str r2, [sp, #168]
	eor.w r2, r1, r3
	ldr r3, [sp, #228]
	str r2, [sp, #236]
	eors r3, r0
	lsls r6, r2, #28
	str r3, [sp, #96]
	orr.w r6, r6, r3, lsr #4
	ldr r3, [sp, #304]
	ldr r2, [sp, #212]
	str r6, [sp, #316]
	bic.w r6, r3, r6
	eor.w r3, r8, r2
	ldr r2, [sp, #200]
	eor.w r12, r6, r5
	str r3, [sp, #92]
	eors r2, r4
	lsls r6, r3, #11
	ldr r3, [sp, #248]
	str r5, [sp, #312]
	orr.w r5, r6, r2, lsr #21
	str r2, [sp, #88]
	eor.w r2, r1, r3
	ldr r3, [sp, #232]
	str r2, [sp, #84]
	lsls r6, r2, #21
	eors r3, r0
	str r3, [sp, #76]
	str.w r12, [sp, #196]
	orr.w r2, r6, r3, lsr #11
	ldr r3, [sp, #288]
	str r2, [sp, #228]
	bic.w r6, r3, r2
	ldr r2, [sp, #216]
	eors r6, r5
	ldr r3, [sp, #220]
	str r6, [sp, #200]
	eor.w r6, r6, r12
	eor.w r12, r6, lr
	eor.w r6, r4, r2
	eor.w r2, r8, r3
	ldr r3, [sp, #244]
	str r5, [sp, #212]
	lsls r5, r6, #15
	str r6, [sp, #216]
	eor.w r6, r0, r3
	ldr r3, [sp, #280]
	str r6, [sp, #60]
	lsls r6, r6, #24
	eor.w r11, r1, r3
	ldr r3, [sp, #296]
	str r2, [sp, #220]
	orr.w r2, r5, r2, lsr #17
	orr.w r6, r6, r11, lsr #8
	str r6, [sp, #80]
	bic.w r6, r3, r6
	ldr r3, [sp, #240]
	eors r6, r2
	str r6, [sp, #192]
	eor.w r9, r8, r3
	ldr r3, [sp, #224]
	eor.w r6, r6, r12
	str r2, [sp, #232]
	eor.w r10, r4, r3
	ldr r3, [sp, #284]
	lsl.w r4, r9, #30
	ldr r2, [sp, #152]
	eor.w r8, r0, r3
	ldr r0, [sp, #308]
	orr.w r4, r4, r10, lsr #2
	ldr.w lr, [sp, #72]
	eor.w r12, r1, r0
	lsl.w r1, r8, #23
	str r4, [sp, #244]
	orr.w r0, r1, r12, lsr #9
	ldr r1, [sp, #320]
	str r0, [sp, #240]
	bics r1, r0
	eor.w r0, r1, r4
	str r0, [sp, #160]
	eor.w r1, r6, r0
	ldr r0, [sp, #48]
	str r1, [sp, #64]
	eors r0, r1
	str r0, [sp, #224]
	ldr r0, [sp, #36]
	lsls r1, r0, #1
	ldr r0, [sp, #52]
	orr.w r0, r1, r0, lsr #31
	str r0, [sp, #56]
	ldr r0, [sp, #132]
	lsls r1, r0, #6
	ldr r0, [sp, #336]
	orr.w r0, r1, r0, lsr #26
	ldr r1, [sp, #156]
	str r0, [sp, #248]
	lsls r1, r1, #25
	orr.w r5, r1, r2, lsr #7
	bic.w r1, lr, r5
	str r5, [sp, #68]
	eor.w r3, r1, r0
	ldr r0, [sp, #168]
	str r3, [sp, #144]
	lsls r1, r0, #29
	ldr r0, [sp, #104]
	orr.w r4, r1, r0, lsr #3
	ldr r0, [sp, #96]
	str r4, [sp, #280]
	lsls r1, r0, #28
	ldr r0, [sp, #236]
	orr.w r0, r1, r0, lsr #4
	ldr r1, [sp, #260]
	str r0, [sp, #284]
	bics r1, r0
	ldr r0, [sp, #88]
	eor.w r2, r1, r4
	str r2, [sp, #156]
	lsls r1, r0, #11
	ldr r0, [sp, #92]
	orr.w r0, r1, r0, lsr #21
	ldr r1, [sp, #76]
	str r0, [sp, #308]
	lsls r6, r1, #21
	ldr r1, [sp, #84]
	orr.w r4, r6, r1, lsr #11
	ldr r1, [sp, #252]
	str r4, [sp, #84]
	bic.w r6, r1, r4
	eor.w r4, r6, r0
	ldr r0, [sp, #220]
	eor.w r6, r4, r2
	str r4, [sp, #168]
	eors r6, r3
	lsls r4, r0, #15
	ldr r0, [sp, #216]
	orr.w r1, r4, r0, lsr #17
	ldr r0, [sp, #60]
	lsl.w r4, r11, #24
	str r1, [sp, #216]
	ldr.w r11, [sp, #112]
	orr.w r3, r4, r0, lsr #8
	ldr r0, [sp, #256]
	str r3, [sp, #220]
	bic.w r4, r0, r3
	lsl.w r3, r10, #30
	eor.w r0, r4, r1
	str r0, [sp, #152]
	eor.w r4, r6, r0
	lsl.w r0, r12, #23
	orr.w r9, r3, r9, lsr #2
	orr.w r3, r0, r8, lsr #9
	ldr r0, [sp, #272]
	str r3, [sp, #236]
	bics r0, r3
	ldr r1, [sp, #124]
	ldr r3, [sp, #328]
	eor.w r0, r0, r9
	str r0, [sp, #132]
	eor.w r12, r4, r0
	ldr r0, [sp, #56]
	bic.w r6, r1, r3
	ldr r3, [sp, #268]
	eor.w r4, r12, r0
	ldr r0, [sp, #224]
	eors r3, r6
	bic.w r6, r11, lr
	eor.w r2, r5, r6
	str r2, [sp, #72]
	eors r0, r3
	eors r2, r4
	ldr.w lr, [sp, #64]
	str r4, [sp, #40]
	lsls r4, r2, #25
	str r3, [sp, #76]
	orr.w r3, r4, r0, lsr #7
	str r0, [sp, #88]
	lsl.w r4, lr, #1
	str r3, [sp, #336]
	orr.w r8, r4, r12, lsr #31
	ldr r3, [sp, #340]
	ldr r0, [sp, #212]
	ldr r6, [sp, #292]
	bic.w r4, r0, r3
	ldr r5, [sp, #264]
	eor.w r10, r4, r6
	ldr r6, [sp, #312]
	str r2, [sp, #92]
	mov r4, r3
	ldr r2, [sp, #232]
	eors r5, r6
	str.w r9, [sp, #52]
	eors r5, r2
	ldr r2, [sp, #244]
	str.w r8, [sp, #96]
	eors r5, r2
	ldr r2, [sp, #276]
	bics r5, r3
	ldr r3, [sp, #324]
	eors r5, r3
	ldr r3, [sp, #300]
	eors r5, r3
	ldr r3, [sp, #332]
	eors r5, r2
	eors r1, r5
	str r1, [sp, #104]
	eor.w r10, r10, r1
	ldr r1, [sp, #228]
	ldr r5, [sp, #120]
	bics r1, r0
	eor r0, r10, #1
	str r0, [sp, #36]
	eor.w r0, r0, r8
	eor.w r6, r1, r4
	str r1, [sp, #124]
	eor.w r4, r0, r6
	ldr r6, [sp, #280]
	ldr r1, [sp, #248]
	str r0, [sp, #212]
	lsl.w r0, r12, #1
	eors r6, r1
	ldr r1, [sp, #216]
	ldr.w r12, [sp, #116]
	orr.w r2, r0, lr, lsr #31
	eors r6, r1
	ldr.w lr, [sp, #308]
	eor.w r6, r6, r9
	ldr.w r9, [sp, #128]
	bics r6, r3
	ldr.w r8, [sp, #108]
	eor.w r6, r6, r9
	bic.w r0, lr, r3
	eor.w r6, r6, r12
	eor.w r0, r0, r8
	eors r6, r5
	str r2, [sp, #44]
	eor.w r1, r6, r11
	ldr.w r11, [sp, #84]
	eor.w r6, r0, r1
	str r1, [sp, #48]
	bic.w r0, r11, lr
	eor.w r1, r2, r6
	str r0, [sp, #112]
	eors r0, r3
	eors r0, r1
	str r1, [sp, #328]
	ldr r1, [sp, #260]
	ldr r3, [sp, #284]
	bic.w r1, r5, r1
	str r0, [sp, #60]
	eors r3, r1
	ldr r1, [sp, #252]
	lsls r0, r0, #1
	orr.w lr, r0, r4, lsr #31
	lsls r0, r6, #1
	bic.w r1, r8, r1
	orr.w r0, r0, r10, lsr #31
	eor.w r10, r11, r1
	ldr r2, [sp, #72]
	eor.w r1, r10, r3
	str r3, [sp, #260]
	ldr r3, [sp, #256]
	eors r1, r2
	ldr r2, [sp, #220]
	bic.w r3, r12, r3
	str r4, [sp, #56]
	eors r2, r3
	ldr r3, [sp, #272]
	str r2, [sp, #32]
	eors r1, r2
	ldr r2, [sp, #236]
	bic.w r3, r9, r3
	ldr.w r8, [sp, #40]
	eors r2, r3
	str r2, [sp, #108]
	eors r1, r2
	str r1, [sp, #84]
	eors r1, r0
	ldr r0, [sp, #136]
	str r1, [sp]
	eor.w r12, r1, r0
	ldr r0, [sp, #36]
	str.w lr, [sp, #308]
	str.w r12, [sp, #252]
	lsls r1, r0, #1
	orr.w r11, r1, r6, lsr #31
	ldr r1, [sp, #304]
	ldr r0, [sp, #276]
	bic.w r3, r0, r1
	ldr r1, [sp, #316]
	ldr r0, [sp, #228]
	eor.w r2, r1, r3
	ldrd r3, r1, [sp, #288]
	str r2, [sp, #272]
	bic.w r3, r1, r3
	ldrd r4, r1, [sp, #296]
	eors r3, r0
	ldr r0, [sp, #76]
	eor.w r5, r3, r2
	ldr r2, [sp, #80]
	bic.w r6, r1, r4
	ldrd r4, r1, [sp, #320]
	eors r5, r0
	eor.w r0, r2, r6
	str r0, [sp, #296]
	eors r5, r0
	ldr r0, [sp, #240]
	bics r1, r4
	ldr r4, [sp, #172]
	eors r0, r1
	str r0, [sp, #300]
	eors r0, r5
	str r0, [sp, #76]
	eor.w r9, r11, r0
	lsl.w r5, r12, #9
	eor.w r0, r9, r4
	str r0, [sp, #256]
	ldr r4, [sp, #336]
	eor.w r1, r8, r10
	orr.w r0, r5, r0, lsr #23
	ldr r6, [sp, #224]
	bic.w r5, lr, r0
	str r0, [sp, #276]
	eor.w r0, r5, r4
	str r0, [sp, #304]
	eor.w r0, r6, r3
	lsls r3, r1, #28
	str r0, [sp, #228]
	orr.w r4, r3, r0, lsr #4
	str r1, [sp, #136]
	ldrd r1, r0, [sp, #216]
	ldr.w lr, [sp, #332]
	bic.w r3, r0, r1
	ldr r1, [sp, #232]
	ldr.w r11, [sp, #340]
	eor.w r5, r3, lr
	bic.w r3, r2, r1
	ldr.w r10, [sp, #212]
	ldr r0, [sp, #328]
	eor.w r1, r3, r11
	str r1, [sp, #72]
	eor.w r1, r1, r10
	eors r0, r5
	str r5, [sp, #64]
	lsls r3, r1, #13
	ldr.w r12, [sp]
	orr.w r5, r3, r0, lsr #19
	ldr r3, [sp, #140]
	str r0, [sp, #232]
	mov r2, r8
	eor.w r0, r12, r3
	ldr r3, [sp, #208]
	str r1, [sp, #220]
	eor.w r1, r9, r3
	str r0, [sp, #140]
	lsls r3, r0, #20
	ldr r0, [sp, #32]
	str r1, [sp, #36]
	orr.w r1, r3, r1, lsr #12
	str r1, [sp, #120]
	bic.w r3, r5, r1
	ldr r1, [sp, #296]
	eor.w r0, r0, r8
	str r5, [sp, #324]
	eor.w r5, r3, r4
	eors r1, r6
	lsls r3, r0, #21
	str r4, [sp, #116]
	mov r4, r6
	orr.w r6, r3, r1, lsr #11
	ldr r3, [sp, #188]
	str r0, [sp, #32]
	mov r8, r12
	eor.w r0, r9, r3
	ldr r3, [sp, #148]
	str r1, [sp, #28]
	eor.w r1, r12, r3
	str r0, [sp, #24]
	str r1, [sp, #148]
	mov r12, r4
	lsls r3, r1, #14
	orr.w r1, r3, r0, lsr #18
	ldrd r3, r0, [sp, #44]
	str r1, [sp, #128]
	eors r3, r0
	str r3, [sp, #320]
	bics r3, r1
	ldr r1, [sp, #304]
	eors r3, r6
	str r3, [sp, #188]
	eors r3, r5
	str r5, [sp, #208]
	eor.w r0, r3, r1
	ldr r1, [sp, #300]
	str r0, [sp, #292]
	ldr r0, [sp, #108]
	eors r1, r4
	ldr r4, [sp, #248]
	eors r0, r2
	ldr r5, [sp, #68]
	str r6, [sp, #296]
	lsls r6, r1, #24
	orr.w r3, r6, r0, lsr #8
	bic.w r6, r5, r4
	str r0, [sp, #20]
	eor.w r0, r6, lr
	ldrd r5, r6, [sp, #264]
	str r1, [sp, #16]
	ldr r1, [sp, #328]
	bics r6, r5
	eor.w r4, r6, r11
	str r0, [sp, #44]
	eors r0, r1
	ldr r6, [sp, #164]
	str r0, [sp, #12]
	lsls r5, r0, #10
	eor.w r0, r8, r6
	ldr r6, [sp, #184]
	str r4, [sp, #48]
	eor.w r4, r4, r10
	eor.w r6, r6, r9
	str r4, [sp, #8]
	orr.w r5, r5, r4, lsr #22
	lsls r4, r0, #27
	orr.w r4, r4, r6, lsr #5
	str r0, [sp, #4]
	str r4, [sp, #248]
	bic.w r4, r5, r4
	ldr r0, [sp, #292]
	str r6, [sp, #184]
	eor.w r6, r4, r3
	str r3, [sp, #288]
	eor.w r3, r0, r6
	ldr r0, [sp, #272]
	ldr r4, [sp, #260]
	eor.w r0, r0, r12
	str r5, [sp, #300]
	eor.w r5, r2, r4
	str r6, [sp, #172]
	lsls r6, r0, #23
	ldr r2, [sp, #236]
	orr.w r12, r6, r5, lsr #9
	ldr r6, [sp, #52]
	str r0, [sp, #40]
	lsls r5, r5, #23
	bic.w r6, r2, r6
	ldrd r2, r4, [sp, #240]
	eor.w lr, lr, r6
	str.w lr, [sp, #224]
	bic.w r6, r2, r4
	eor.w r1, r1, lr
	eor.w r0, r6, r11
	str r0, [sp, #236]
	eor.w lr, r10, r0
	lsls r6, r1, #2
	mov r10, r1
	ldr r1, [sp, #256]
	orr.w r4, r6, lr, lsr #30
	ldr r6, [sp, #176]
	str r4, [sp, #272]
	eor.w r11, r8, r6
	ldr r6, [sp, #204]
	str.w r12, [sp, #264]
	eor.w r8, r9, r6
	lsl.w r6, r8, #7
	orr.w r0, r6, r11, lsr #25
	bic.w r6, r4, r0
	str r0, [sp, #244]
	ldr r0, [sp, #88]
	eor.w r6, r6, r12
	eor.w r4, r3, r6
	str r6, [sp, #176]
	str r4, [sp, #80]
	lsls r3, r0, #25
	ldr r0, [sp, #92]
	orr.w r2, r3, r0, lsr #7
	ldr r0, [sp, #56]
	str r2, [sp, #240]
	lsls r3, r0, #1
	ldr r0, [sp, #60]
	orr.w r0, r3, r0, lsr #31
	lsls r3, r1, #9
	ldr r1, [sp, #252]
	str r0, [sp, #292]
	orr.w r1, r3, r1, lsr #23
	str r1, [sp, #92]
	bic.w r3, r0, r1
	ldr r0, [sp, #228]
	eor.w r12, r3, r2
	ldr r1, [sp, #36]
	str.w r12, [sp, #108]
	lsls r3, r0, #28
	ldr r0, [sp, #136]
	orr.w r2, r3, r0, lsr #4
	ldr r0, [sp, #232]
	str r2, [sp, #216]
	lsls r3, r0, #13
	ldr r0, [sp, #220]
	orr.w r0, r3, r0, lsr #19
	lsls r3, r1, #20
	ldr r1, [sp, #140]
	str r0, [sp, #268]
	orr.w r1, r3, r1, lsr #12
	str r1, [sp, #68]
	bic.w r3, r0, r1
	ldr r0, [sp, #28]
	eor.w r6, r3, r2
	str r6, [sp, #164]
	ldr r2, [sp, #184]
	lsls r3, r0, #21
	ldr r0, [sp, #32]
	orr.w r9, r3, r0, lsr #11
	ldr r0, [sp, #24]
	str.w r9, [sp, #60]
	lsls r3, r0, #14
	ldr r0, [sp, #148]
	orr.w r1, r3, r0, lsr #18
	ldr r0, [sp, #104]
	ldr r3, [sp, #96]
	str r1, [sp, #88]
	eors r0, r3
	str r0, [sp, #260]
	bic.w r3, r0, r1
	eor.w r0, r3, r9
	str r0, [sp, #136]
	eor.w r3, r0, r6
	ldr r0, [sp, #20]
	eor.w r3, r3, r12
	mov r12, r4
	lsls r6, r0, #24
	ldr r0, [sp, #16]
	orr.w r1, r6, r0, lsr #8
	ldr r0, [sp, #8]
	str r1, [sp, #232]
	lsls r6, r0, #10
	ldr r0, [sp, #12]
	orr.w r0, r6, r0, lsr #22
	lsls r6, r2, #27
	ldr r2, [sp, #4]
	str r0, [sp, #256]
	orr.w r2, r6, r2, lsr #5
	str r2, [sp, #104]
	bic.w r6, r0, r2
	ldr r0, [sp, #40]
	eors r6, r1
	str r6, [sp, #140]
	eors r3, r6
	lsl.w r6, lr, #2
	orr.w r2, r5, r0, lsr #9
	lsl.w r0, r11, #7
	orr.w r1, r6, r10, lsr #30
	orr.w r0, r0, r8, lsr #25
	str r0, [sp, #96]
	bic.w r0, r1, r0
	eors r0, r2
	str r0, [sp, #148]
	eors r0, r3
	str r2, [sp, #228]
	ldr r2, [sp, #84]
	str r0, [sp, #252]
	lsls r0, r0, #1
	orr.w lr, r0, r4, lsr #31
	ldr r4, [sp, #76]
	ldrd r6, r3, [sp, #280]
	lsls r0, r2, #1
	ldr r5, [sp, #64]
	bic.w r8, r3, r6
	orr.w r0, r0, r4, lsr #31
	ldr r6, [sp, #112]
	eor.w r0, r0, r8
	str r1, [sp, #220]
	eors r0, r6
	ldr r6, [sp, #44]
	eors r0, r6
	ldr r6, [sp, #224]
	eors r0, r5
	eors r0, r6
	ldr r6, [sp, #132]
	eor.w r1, r0, r6
	lsls r6, r4, #1
	ldrd r4, r5, [sp, #312]
	orr.w r6, r6, r2, lsr #31
	ldr r2, [sp, #48]
	bics r5, r4
	ldr r4, [sp, #124]
	eors r6, r5
	str r1, [sp, #280]
	eors r6, r4
	ldr r4, [sp, #160]
	eors r6, r2
	ldr r2, [sp, #72]
	eors r6, r2
	ldr r2, [sp, #236]
	eors r6, r2
	eor.w r2, r6, r4
	lsls r4, r1, #29
	str r2, [sp, #236]
	orr.w r2, r4, r2, lsr #3
	ldr r4, [sp, #216]
	str r2, [sp, #316]
	bics r4, r2
	str r4, [sp, #184]
	eor.w r1, r4, lr
	ldr r4, [sp, #144]
	eor.w r2, r0, r4
	ldr r4, [sp, #180]
	str r2, [sp, #160]
	eor.w r3, r6, r4
	lsls r4, r2, #11
	str r3, [sp, #144]
	orr.w r2, r4, r3, lsr #21
	str r2, [sp, #312]
	bic.w r4, r9, r2
	ldr r2, [sp, #332]
	str r4, [sp, #204]
	eors r1, r4
	eor.w r3, r8, r2
	ldr r2, [sp, #328]
	eor.w r4, r2, r3
	ldr r2, [sp, #340]
	str r4, [sp, #328]
	eor.w r3, r5, r2
	ldr r2, [sp, #212]
	eors r2, r3
	lsls r3, r4, #12
	str r2, [sp, #340]
	orr.w r9, r3, r2, lsr #20
	ldr r3, [sp, #196]
	ldr r2, [sp, #240]
	eor.w r11, r6, r3
	ldr r3, [sp, #156]
	eor.w r5, r0, r3
	lsl.w r4, r11, #6
	orr.w r3, r4, r5, lsr #26
	str r3, [sp, #332]
	bic.w r4, r2, r3
	ldr r2, [sp, #232]
	eor.w r3, r4, r9
	str r3, [sp, #212]
	eor.w r4, r1, r3
	ldr r1, [sp, #192]
	lsls r5, r5, #6
	eor.w lr, r6, r1
	ldr r1, [sp, #152]
	eors r1, r0
	lsl.w r10, lr, #15
	orr.w r3, r10, r1, lsr #17
	str r3, [sp, #124]
	bic.w r3, r2, r3
	ldr r2, [sp, #228]
	eor.w r3, r3, r9
	str r3, [sp, #196]
	eor.w r10, r4, r3
	ldr r3, [sp, #168]
	ldr r4, [sp, #200]
	lsls r1, r1, #15
	eors r0, r3
	eors r6, r4
	lsls r4, r0, #30
	orr.w r3, r4, r6, lsr #2
	str r3, [sp, #52]
	bic.w r4, r2, r3
	ldr r2, [sp, #236]
	eor.w r3, r4, r9
	ldr r4, [sp, #252]
	eor.w r8, r10, r3
	str r3, [sp, #180]
	lsl.w r3, r12, #1
	ldr.w r12, [sp, #116]
	orr.w r10, r3, r4, lsr #31
	lsls r4, r2, #29
	ldr r2, [sp, #280]
	ldr r3, [sp, #144]
	str.w r8, [sp, #284]
	orr.w r2, r4, r2, lsr #3
	str r2, [sp, #36]
	bic.w r4, r12, r2
	str r4, [sp, #152]
	eor.w r10, r10, r4
	lsls r4, r3, #11
	ldr r3, [sp, #160]
	orr.w r3, r4, r3, lsr #21
	ldr r4, [sp, #296]
	str r3, [sp, #44]
	bics r4, r3
	ldr r3, [sp, #340]
	str r4, [sp, #192]
	eor.w r10, r10, r4
	lsls r4, r3, #12
	ldr r3, [sp, #328]
	orr.w r3, r4, r3, lsr #20
	orr.w r4, r5, r11, lsr #26
	ldr r5, [sp, #336]
	str r4, [sp, #56]
	bic.w r4, r5, r4
	mov r5, r3
	eors r4, r3
	str r3, [sp, #236]
	eor.w r3, r10, r4
	str r4, [sp, #160]
	orr.w r4, r1, lr, lsr #17
	ldr r1, [sp, #288]
	str r4, [sp, #48]
	bics r1, r4
	ldr.w lr, [sp, #68]
	eors r1, r5
	str r1, [sp, #168]
	eors r3, r1
	lsls r1, r6, #30
	orr.w r1, r1, r0, lsr #2
	ldr r0, [sp, #264]
	str r1, [sp, #40]
	bics r0, r1
	ldr r1, [sp, #316]
	eors r0, r5
	str r0, [sp, #144]
	eor.w r4, r3, r0
	ldr r0, [sp, #216]
	ldr.w r10, [sp, #128]
	bic.w r0, lr, r0
	str r4, [sp, #76]
	eor.w r11, r1, r0
	ldr r1, [sp, #120]
	eor.w r3, r8, r11
	str r3, [sp, #200]
	bic.w r0, r1, r12
	eors r0, r2
	str r0, [sp, #156]
	eors r0, r4
	str r0, [sp, #280]
	ldr r2, [sp, #276]
	lsls r0, r0, #6
	orr.w r0, r0, r3, lsr #26
	str r0, [sp, #340]
	ldr r0, [sp, #308]
	ldr r3, [sp, #300]
	bic.w r0, r5, r0
	eors r2, r0
	ldr r0, [sp, #324]
	bic.w r4, r5, r3
	str r2, [sp, #132]
	bic.w r0, r5, r0
	eors r1, r0
	ldr r0, [sp, #320]
	str r1, [sp, #328]
	bic.w r0, r5, r0
	eor.w r0, r0, r10
	str r0, [sp, #112]
	eors r0, r1
	ldr r1, [sp, #248]
	eors r0, r2
	eors r1, r4
	str r1, [sp, #64]
	ldr r3, [sp, #272]
	eors r0, r1
	ldr r1, [sp, #244]
	bic.w r4, r5, r3
	ldr r6, [sp, #92]
	eors r1, r4
	str r1, [sp, #116]
	eor.w r4, r0, r1
	ldr r0, [sp, #292]
	ldr r2, [sp, #88]
	bic.w r0, r9, r0
	str.w r9, [sp, #224]
	eor.w r1, r0, r6
	ldr r0, [sp, #268]
	str r1, [sp, #120]
	bic.w r0, r9, r0
	eor.w r3, r0, lr
	ldr r0, [sp, #260]
	str r3, [sp, #216]
	bic.w r0, r9, r0
	eors r0, r2
	str r0, [sp, #84]
	eors r0, r3
	ldr r3, [sp, #256]
	eor.w lr, r0, r1
	ldr r1, [sp, #104]
	bic.w r5, r9, r3
	eor.w r0, r5, r1
	str r0, [sp, #68]
	eor.w r3, lr, r0
	ldr r0, [sp, #220]
	ldr.w lr, [sp, #56]
	bic.w r5, r9, r0
	ldr r0, [sp, #96]
	ldr.w r9, [sp, #52]
	eors r5, r0
	str r5, [sp, #72]
	eor.w r12, r3, r5
	ldr r3, [sp, #60]
	bic.w r3, r2, r3
	ldr r2, [sp, #312]
	lsl.w r5, r12, #1
	eors r2, r3
	str r2, [sp, #88]
	eor.w r3, r2, r11
	ldr r2, [sp, #240]
	ldr.w r11, [sp, #124]
	orr.w r5, r5, r4, lsr #31
	bics r6, r2
	ldr r2, [sp, #332]
	eors r2, r6
	str r2, [sp, #92]
	eors r3, r2
	ldr r2, [sp, #232]
	bic.w r6, r1, r2
	eor.w r1, r11, r6
	str r1, [sp, #232]
	eors r3, r1
	ldr r1, [sp, #228]
	bic.w r6, r0, r1
	eor.w r0, r9, r6
	str r0, [sp, #96]
	eors r3, r0
	str r3, [sp, #240]
	eor.w r0, r3, r5
	ldr r3, [sp, #108]
	ldr r5, [sp, #44]
	eor.w r6, r0, r3
	lsls r3, r4, #1
	orr.w r8, r3, r12, lsr #31
	ldr r3, [sp, #296]
	str r0, [sp, #60]
	bic.w r3, r10, r3
	ldr r0, [sp, #156]
	eor.w r1, r5, r3
	str r1, [sp, #296]
	eor.w r2, r1, r0
	ldr r4, [sp, #336]
	ldr r1, [sp, #276]
	ldr.w r12, [sp, #48]
	bic.w r4, r1, r4
	ldr r1, [sp, #288]
	eor.w r0, lr, r4
	str r0, [sp, #104]
	eors r0, r2
	ldr r2, [sp, #248]
	ldr r3, [sp, #40]
	bic.w r4, r2, r1
	ldr r2, [sp, #244]
	eor.w r1, r12, r4
	str r1, [sp, #288]
	eors r0, r1
	ldr r1, [sp, #264]
	str r6, [sp, #108]
	bic.w r4, r2, r1
	ldr r2, [sp, #236]
	eors r4, r3
	eor.w r1, r0, r4
	ldr r0, [sp, #304]
	eor.w r10, r1, r8
	str r1, [sp, #264]
	eor.w r0, r0, r10
	str r0, [sp, #336]
	ldr r1, [sp, #320]
	lsls r0, r0, #25
	orr.w r8, r0, r6, lsr #7
	bic.w r0, r5, r2
	str.w r8, [sp, #156]
	eors r0, r1
	ldr r1, [sp, #36]
	str.w r10, [sp, #32]
	eor.w r5, r1, lr
	eor.w r5, r5, r12
	eor.w r1, r3, r5
	ldr r3, [sp, #272]
	bics r1, r2
	ldr r5, [sp, #324]
	eors r1, r3
	ldr r3, [sp, #300]
	eors r1, r3
	ldr r3, [sp, #224]
	eors r1, r5
	ldr r5, [sp, #308]
	eors r1, r5
	str r1, [sp, #272]
	eor.w r2, r0, r1
	ldr r0, [sp, #312]
	ldr r1, [sp, #260]
	bics r0, r3
	ldr r5, [sp, #332]
	eors r0, r1
	ldr r1, [sp, #316]
	str r2, [sp, #244]
	eors r1, r5
	movw r5, #32898
	eor.w r1, r1, r11
	ldr.w r11, [sp, #60]
	eor.w r1, r1, r9
	bics r1, r3
	ldr r3, [sp, #220]
	eors r1, r3
	ldr r3, [sp, #256]
	eors r1, r3
	ldr r3, [sp, #268]
	eors r1, r3
	ldr r3, [sp, #292]
	eors r1, r3
	str r1, [sp, #248]
	eors r1, r0
	lsls r0, r2, #1
	ldr r3, [sp, #80]
	orr.w r0, r0, r1, lsr #31
	eor.w r12, r0, r3
	ldr r0, [sp, #64]
	eor.w r6, r12, r0
	eor.w r0, r1, r5
	str r0, [sp, #268]
	lsls r1, r0, #1
	ldr r0, [sp, #252]
	orr.w r1, r1, r2, lsr #31
	lsls r5, r6, #9
	eor.w r3, r1, r0
	ldr r0, [sp, #68]
	ldr r2, [sp, #284]
	eors r0, r3
	str r0, [sp, #276]
	str r6, [sp, #332]
	orr.w r0, r5, r0, lsr #23
	str r0, [sp, #312]
	bic.w r5, r0, r8
	ldr r0, [sp, #96]
	ldr.w r8, [sp, #76]
	ldr r6, [sp, #340]
	eors r0, r2
	eor.w r1, r8, r4
	str r1, [sp, #256]
	eor.w lr, r5, r6
	lsls r6, r0, #29
	orr.w r9, r6, r1, lsr #3
	ldr r6, [sp, #188]
	str r0, [sp, #260]
	eor.w r1, r10, r6
	str r1, [sp, #252]
	ldr r0, [sp, #136]
	lsls r6, r1, #28
	ldr r1, [sp, #328]
	eor.w r0, r0, r11
	str r0, [sp, #136]
	eor.w r5, r12, r1
	ldr r1, [sp, #216]
	orr.w r0, r6, r0, lsr #4
	str r0, [sp, #316]
	eors r1, r3
	str r1, [sp, #80]
	lsls r6, r5, #20
	str.w r9, [sp, #220]
	orr.w r1, r6, r1, lsr #12
	str r1, [sp, #300]
	bic.w r6, r1, r0
	ldr r0, [sp, #92]
	eor.w r9, r9, r6
	str r5, [sp, #128]
	eor.w r1, r2, r0
	ldr r0, [sp, #104]
	str r1, [sp, #68]
	eor.w r0, r0, r8
	lsls r6, r1, #11
	str r0, [sp, #104]
	orr.w r4, r6, r0, lsr #21
	ldr r0, [sp, #140]
	ldr r6, [sp, #172]
	eor.w r0, r0, r11
	str r0, [sp, #140]
	eor.w r1, r10, r6
	str r1, [sp, #64]
	ldr.w r10, [sp, #284]
	lsls r6, r1, #21
	orr.w r2, r6, r0, lsr #11
	ldr r0, [sp, #116]
	str.w lr, [sp, #228]
	eor.w r5, r12, r0
	ldr r0, [sp, #72]
	str r5, [sp, #56]
	eors r0, r3
	str r0, [sp, #72]
	lsls r6, r5, #14
	str r2, [sp, #124]
	orr.w r0, r6, r0, lsr #18
	str r0, [sp, #292]
	bic.w r6, r0, r2
	ldr r0, [sp, #288]
	eor.w r5, r6, r4
	str r5, [sp, #172]
	eor.w r1, r8, r0
	ldr r0, [sp, #232]
	eor.w r6, r5, r9
	ldr r2, [sp, #32]
	eor.w r0, r0, r10
	eor.w lr, lr, r6
	lsls r6, r1, #15
	str r0, [sp, #48]
	orr.w r5, r6, r0, lsr #17
	ldr r0, [sp, #148]
	ldr r6, [sp, #176]
	eor.w r0, r0, r11
	str r1, [sp, #52]
	eor.w r1, r2, r6
	str r0, [sp, #44]
	lsls r6, r0, #24
	ldr r0, [sp, #112]
	str r4, [sp, #328]
	eor.w r4, r12, r0
	ldr r0, [sp, #84]
	str.w r9, [sp, #216]
	eor.w r9, r3, r0
	str r1, [sp, #40]
	orr.w r1, r6, r1, lsr #8
	lsls r6, r4, #27
	orr.w r0, r6, r9, lsr #5
	str r0, [sp, #288]
	bic.w r6, r0, r1
	ldr r0, [sp, #88]
	eors r6, r5
	str r5, [sp, #324]
	eor.w r5, lr, r6
	str r6, [sp, #176]
	eor.w lr, r10, r0
	ldr r6, [sp, #164]
	ldr r0, [sp, #296]
	str r4, [sp, #36]
	eor.w r11, r11, r6
	eor.w r4, r8, r0
	ldr r6, [sp, #208]
	lsl.w r8, lr, #30
	str r1, [sp, #116]
	orr.w r1, r8, r4, lsr #2
	eor.w r8, r2, r6
	ldr r2, [sp, #132]
	lsl.w r6, r11, #23
	orr.w r0, r6, r8, lsr #9
	str r0, [sp, #112]
	eor.w r12, r12, r2
	ldr r2, [sp, #120]
	str r1, [sp, #320]
	lsls r4, r4, #30
	eor.w r10, r3, r2
	ldr r2, [sp, #276]
	lsl.w r6, r10, #7
	orr.w r3, r6, r12, lsr #25
	bic.w r6, r3, r0
	str r3, [sp, #308]
	eors r6, r1
	ldr r1, [sp, #108]
	eor.w r0, r5, r6
	str r0, [sp, #232]
	ldr r0, [sp, #200]
	str r6, [sp, #208]
	lsls r5, r0, #6
	ldr r0, [sp, #280]
	orr.w r0, r5, r0, lsr #26
	lsls r5, r1, #25
	ldr r1, [sp, #336]
	str r0, [sp, #304]
	orr.w r1, r5, r1, lsr #7
	lsls r5, r2, #9
	ldr r2, [sp, #332]
	str r1, [sp, #96]
	orr.w r2, r5, r2, lsr #23
	str r2, [sp, #92]
	bic.w r5, r2, r1
	ldr r1, [sp, #80]
	eor.w r6, r5, r0
	ldr r0, [sp, #256]
	str r6, [sp, #200]
	lsls r5, r0, #29
	ldr r0, [sp, #260]
	orr.w r2, r5, r0, lsr #3
	ldr r0, [sp, #136]
	str r2, [sp, #188]
	lsls r5, r0, #28
	ldr r0, [sp, #252]
	orr.w r0, r5, r0, lsr #4
	lsls r5, r1, #20
	ldr r1, [sp, #128]
	str r0, [sp, #276]
	orr.w r1, r5, r1, lsr #12
	str r1, [sp, #88]
	bic.w r5, r1, r0
	ldr r0, [sp, #104]
	eor.w r3, r5, r2
	ldr r2, [sp, #72]
	str r3, [sp, #148]
	lsls r5, r0, #11
	ldr r0, [sp, #68]
	orr.w r1, r5, r0, lsr #21
	ldr r0, [sp, #140]
	str r1, [sp, #296]
	lsls r5, r0, #21
	ldr r0, [sp, #64]
	orr.w r0, r5, r0, lsr #11
	lsls r5, r2, #14
	ldr r2, [sp, #56]
	str r0, [sp, #84]
	orr.w r2, r5, r2, lsr #18
	str r2, [sp, #72]
	bic.w r5, r2, r0
	ldr r2, [sp, #36]
	eor.w r0, r5, r1
	str r0, [sp, #104]
	eor.w r5, r0, r3
	ldr r0, [sp, #48]
	eors r5, r6
	lsl.w r3, r8, #23
	orr.w r3, r3, r11, lsr #9
	ldr.w r8, [sp, #232]
	lsls r6, r0, #15
	ldr r0, [sp, #52]
	str r3, [sp, #76]
	ldr.w r11, [sp, #224]
	orr.w r1, r6, r0, lsr #17
	ldr r0, [sp, #40]
	str r1, [sp, #284]
	lsls r6, r0, #24
	ldr r0, [sp, #44]
	orr.w r0, r6, r0, lsr #8
	lsl.w r6, r9, #27
	orr.w r2, r6, r2, lsr #5
	str r0, [sp, #80]
	bic.w r6, r2, r0
	str r2, [sp, #64]
	eor.w r0, r6, r1
	str r0, [sp, #120]
	eors r5, r0
	lsl.w r0, r12, #7
	orr.w r0, r0, r10, lsr #25
	orr.w r1, r4, lr, lsr #2
	str r0, [sp, #60]
	bics r0, r3
	eors r0, r1
	str r1, [sp, #280]
	eor.w r1, r5, r0
	ldr r3, [sp, #240]
	str r0, [sp, #140]
	lsl.w r0, r8, #1
	ldr r6, [sp, #264]
	orr.w r0, r0, r1, lsr #31
	str r0, [sp, #332]
	lsls r0, r3, #1
	str r1, [sp, #336]
	orr.w r1, r0, r6, lsr #31
	ldr r0, [sp, #268]
	str r1, [sp, #164]
	eors r1, r0
	ldr r0, [sp, #184]
	ldr.w lr, [sp, #236]
	eor.w r0, r0, r11
	ldr r4, [sp, #272]
	eor.w r2, r1, r0
	lsls r0, r6, #1
	ldr r6, [sp, #152]
	orr.w r3, r0, r3, lsr #31
	ldr r0, [sp, #244]
	eor.w r6, r6, lr
	str r2, [sp, #268]
	eors r0, r3
	eor.w r5, r0, r6
	lsls r6, r2, #12
	eor.w r2, r4, r3
	ldr r3, [sp, #328]
	orr.w r12, r6, r5, lsr #20
	str r2, [sp, #264]
	bic.w r3, r3, r12
	ldr r6, [sp, #324]
	eors r2, r3
	str r2, [sp, #272]
	ldr r3, [sp, #340]
	ldr r2, [sp, #220]
	str r5, [sp, #152]
	eors r3, r2
	str.w r12, [sp, #256]
	eors r3, r6
	ldr r6, [sp, #320]
	eors r3, r6
	ldr r6, [sp, #144]
	bic.w r3, r3, r12
	eor.w r4, r0, r6
	ldr r6, [sp, #180]
	str r4, [sp, #184]
	eors r6, r1
	lsls r5, r4, #2
	str r6, [sp, #180]
	orr.w r4, r5, r6, lsr #30
	ldr r6, [sp, #160]
	eor.w r9, r3, r4
	str r4, [sp, #260]
	eor.w r3, r0, r6
	str r3, [sp, #160]
	ldr r6, [sp, #212]
	lsls r5, r3, #10
	ldr r3, [sp, #196]
	eor.w r4, r1, r6
	eor.w r10, r1, r3
	ldr r3, [sp, #168]
	orr.w r5, r5, r4, lsr #22
	str r5, [sp, #252]
	eors r3, r0
	lsl.w r6, r10, #13
	eor.w r5, r5, r9
	lsls r4, r4, #10
	orr.w r6, r6, r3, lsr #19
	str r6, [sp, #240]
	eors r5, r6
	ldr r6, [sp, #192]
	lsls r3, r3, #13
	eor.w r6, r6, lr
	eor.w r9, r0, r6
	ldr r0, [sp, #204]
	ldr r6, [sp, #284]
	eor.w r0, r0, r11
	eor.w r11, r1, r0
	lsl.w r0, r9, #1
	ldr r1, [sp, #272]
	orr.w r0, r0, r11, lsr #31
	str r0, [sp, #244]
	eors r0, r5
	str r0, [sp, #236]
	eors r0, r1
	ldr r1, [sp, #316]
	str r0, [sp, #192]
	bic.w r2, r1, r2
	eor r1, r0, #-2147483648
	ldr r0, [sp, #332]
	str r1, [sp, #204]
	eors r1, r0
	eor.w r0, r2, r12
	eors r0, r1
	str r0, [sp, #272]
	ldr r0, [sp, #336]
	str r1, [sp, #128]
	ldr r1, [sp, #268]
	lsls r0, r0, #1
	orr.w r5, r0, r8, lsr #31
	ldr r0, [sp, #152]
	str r2, [sp, #68]
	ldr.w r8, [sp, #188]
	lsls r0, r0, #12
	orr.w lr, r0, r1, lsr #20
	ldr r0, [sp, #248]
	ldr r1, [sp, #164]
	str r5, [sp, #220]
	eor.w r2, r0, r1
	ldr r0, [sp, #296]
	str r2, [sp, #52]
	bic.w r1, r0, lr
	str.w lr, [sp, #268]
	eor.w r0, r1, r2
	ldr r1, [sp, #304]
	ldr r2, [sp, #280]
	eor.w r1, r1, r8
	eors r1, r6
	eors r1, r2
	ldr r2, [sp, #180]
	bic.w r1, r1, lr
	lsls r6, r2, #2
	ldr r2, [sp, #184]
	orr.w r2, r6, r2, lsr #30
	ldr r6, [sp, #160]
	eors r1, r2
	str r2, [sp, #28]
	orr.w r4, r4, r6, lsr #22
	str r4, [sp, #36]
	eors r1, r4
	orr.w r4, r3, r10, lsr #19
	eor.w r3, r1, r4
	lsl.w r1, r11, #1
	orr.w r1, r1, r9, lsr #31
	mov r6, r4
	eors r3, r1
	str r4, [sp, #40]
	mov r4, r1
	str r1, [sp, #32]
	ldr r1, [sp, #276]
	eors r0, r3
	str r3, [sp, #224]
	movw r3, #32906
	bic.w r1, r1, r8
	str r0, [sp, #160]
	eors r0, r3
	str r0, [sp, #164]
	eors r0, r5
	eor.w r3, r1, lr
	str r0, [sp, #108]
	eors r0, r3
	str r0, [sp, #56]
	lsls r3, r0, #12
	ldr r0, [sp, #272]
	str r1, [sp, #44]
	ldr r1, [sp, #264]
	orr.w r0, r3, r0, lsr #20
	str r0, [sp, #248]
	ldr r0, [sp, #244]
	ldr.w r11, [sp, #92]
	bic.w r3, r12, r0
	ldr r0, [sp, #312]
	ldr.w r8, [sp, #72]
	eor.w r5, r3, r0
	ldr r0, [sp, #240]
	str r5, [sp, #136]
	bic.w r3, r12, r0
	ldr r0, [sp, #300]
	ldr.w r9, [sp, #36]
	eors r0, r3
	bic.w r3, r12, r1
	ldr r1, [sp, #292]
	str r0, [sp, #196]
	eors r3, r1
	str r3, [sp, #168]
	eors r3, r0
	ldr r0, [sp, #252]
	eors r3, r5
	ldr.w r10, [sp, #64]
	bic.w r5, r12, r0
	ldr r0, [sp, #288]
	eors r0, r5
	str r0, [sp, #180]
	eors r3, r0
	ldr r0, [sp, #260]
	bic.w r5, r12, r0
	ldr r0, [sp, #308]
	eors r0, r5
	bic.w r5, lr, r4
	eor.w r1, r5, r11
	bic.w r5, lr, r6
	ldr r4, [sp, #88]
	eor.w r12, r3, r0
	ldr r6, [sp, #52]
	str r0, [sp, #212]
	eor.w r0, r5, r4
	bic.w r5, lr, r6
	str r0, [sp, #184]
	eor.w r3, r5, r8
	str r1, [sp, #132]
	eor.w r5, r3, r0
	bic.w r0, lr, r9
	eors r5, r1
	eor.w r0, r0, r10
	str r0, [sp, #152]
	eors r0, r5
	bic.w r5, lr, r2
	ldr.w lr, [sp, #60]
	ldr r1, [sp, #232]
	eor.w r5, r5, lr
	str r5, [sp, #188]
	eors r0, r5
	lsl.w r5, r12, #1
	str r3, [sp, #144]
	orr.w r5, r5, r0, lsr #31
	lsls r0, r0, #1
	eor.w r2, r5, r1
	ldr r1, [sp, #336]
	orr.w r0, r0, r12, lsr #31
	str r2, [sp, #48]
	eor.w r5, r0, r1
	ldr r0, [sp, #240]
	ldr r1, [sp, #300]
	str r5, [sp, #336]
	bics r0, r1
	ldr r1, [sp, #316]
	ldr.w r12, [sp, #156]
	eors r0, r1
	ldr r1, [sp, #40]
	bic.w r3, r1, r4
	ldr r1, [sp, #276]
	ldr r4, [sp, #84]
	eors r3, r1
	eor.w r1, r2, r0
	eor.w r2, r5, r3
	str r1, [sp, #276]
	str r2, [sp, #40]
	lsls r5, r2, #23
	orr.w r1, r5, r1, lsr #9
	bic.w r5, r6, r8
	str r1, [sp, #316]
	eor.w r1, r5, r4
	str r1, [sp, #300]
	eors r3, r1
	ldr r1, [sp, #32]
	ldr r6, [sp, #96]
	bic.w r1, r1, r11
	ldr.w r11, [sp, #80]
	eors r1, r6
	str r1, [sp, #52]
	eors r1, r3
	bic.w r3, r9, r10
	eor.w r2, r3, r11
	str r2, [sp, #240]
	eors r1, r2
	ldr r2, [sp, #28]
	ldr.w r10, [sp, #124]
	bic.w r3, r2, lr
	ldr.w lr, [sp, #76]
	ldr.w r9, [sp, #116]
	eor.w r2, r3, lr
	str r2, [sp, #64]
	eor.w r5, r1, r2
	ldr r1, [sp, #292]
	ldr r2, [sp, #264]
	ldr.w r8, [sp, #112]
	bic.w r1, r2, r1
	ldr r2, [sp, #244]
	eor.w r1, r1, r10
	str r1, [sp, #72]
	eors r0, r1
	ldr r1, [sp, #312]
	ldr r3, [sp, #268]
	bic.w r1, r2, r1
	ldr r2, [sp, #252]
	eor.w r1, r1, r12
	str r1, [sp, #312]
	eors r0, r1
	ldr r1, [sp, #288]
	str r5, [sp, #92]
	bic.w r1, r2, r1
	ldr r2, [sp, #260]
	eor.w r1, r1, r9
	str r1, [sp, #232]
	eors r0, r1
	ldr r1, [sp, #308]
	bic.w r1, r2, r1
	eor.w r1, r1, r8
	str r1, [sp, #308]
	eor.w r2, r0, r1
	lsls r0, r5, #1
	ldr r1, [sp, #44]
	orr.w r0, r0, r2, lsr #31
	str r2, [sp, #88]
	eors r0, r1
	ldr r1, [sp, #296]
	bic.w r1, r4, r1
	str r1, [sp, #84]
	eors r0, r1
	ldr r1, [sp, #304]
	bic.w r1, r6, r1
	eors r1, r3
	str r1, [sp, #96]
	eors r0, r1
	ldr r1, [sp, #284]
	bic.w r1, r11, r1
	eors r1, r3
	str r1, [sp, #288]
	eors r0, r1
	ldr r1, [sp, #280]
	bic.w r1, lr, r1
	eors r1, r3
	str r1, [sp, #292]
	eors r1, r0
	ldr r0, [sp, #104]
	str r1, [sp, #296]
	eor.w r6, r1, r0
	lsls r1, r2, #1
	ldr r0, [sp, #68]
	orr.w r1, r1, r5, lsr #31
	ldr r2, [sp, #256]
	eors r1, r0
	ldr r0, [sp, #328]
	bic.w r0, r10, r0
	str r0, [sp, #284]
	eors r1, r0
	ldr r0, [sp, #340]
	bic.w r5, r12, r0
	ldr.w r12, [sp, #248]
	eor.w r0, r5, r2
	str r0, [sp, #156]
	eors r1, r0
	ldr r0, [sp, #324]
	bic.w r5, r9, r0
	ldr.w r9, [sp, #296]
	eor.w r0, r5, r2
	str r0, [sp, #280]
	eors r1, r0
	ldr r0, [sp, #320]
	bic.w r5, r8, r0
	eor.w r0, r5, r2
	str r0, [sp, #124]
	eors r1, r0
	ldr r0, [sp, #172]
	str r1, [sp, #116]
	lsls r5, r6, #30
	eors r0, r1
	mov lr, r1
	ldr r1, [sp, #316]
	orr.w r3, r5, r0, lsr #2
	ldr r2, [sp, #100]
	bic.w r5, r1, r3
	ldr r1, [sp, #272]
	eor.w r5, r5, r12
	lsls r0, r0, #30
	str.w r5, [r2, #172]
	orr.w r0, r0, r6, lsr #2
	lsls r5, r1, #12
	ldr r1, [sp, #56]
	str r0, [sp, #328]
	str r3, [sp, #340]
	orr.w r11, r5, r1, lsr #20
	ldr r1, [sp, #276]
	ldr r5, [sp, #48]
	lsls r4, r1, #23
	ldr r1, [sp, #40]
	orr.w r1, r4, r1, lsr #9
	str r1, [sp, #276]
	bic.w r0, r1, r0
	ldr r1, [sp, #336]
	eor.w r0, r0, r11
	str.w r0, [r2, #168]
	ldr r0, [sp, #64]
	eor.w r10, r1, r0
	ldr r0, [sp, #308]
	eor.w r6, r5, r0
	ldr r0, [sp, #176]
	lsl.w r4, r10, #24
	orr.w r1, r4, r6, lsr #8
	eor.w r4, lr, r0
	ldr r0, [sp, #120]
	mov lr, r2
	lsls r3, r4, #15
	str r1, [sp, #272]
	eor.w r0, r0, r9
	orr.w r3, r3, r0, lsr #17
	str r3, [sp, #324]
	bic.w r3, r1, r3
	lsls r0, r0, #15
	eor.w r3, r3, r12
	orr.w r0, r0, r4, lsr #17
	str.w r3, [r2, #132]
	lsls r3, r6, #24
	orr.w r1, r3, r10, lsr #8
	str r0, [sp, #320]
	bic.w r0, r1, r0
	ldr.w r12, [sp, #336]
	eor.w r0, r0, r11
	str.w r0, [r2, #128]
	ldr r0, [sp, #312]
	mov r10, r5
	ldr r4, [sp, #216]
	eor.w r8, r5, r0
	ldr r0, [sp, #52]
	ldr r2, [sp, #116]
	eor.w r3, r12, r0
	ldr r5, [sp, #148]
	lsl.w r6, r8, #25
	str r1, [sp, #264]
	orr.w r0, r6, r3, lsr #7
	eor.w r6, r2, r4
	eor.w r4, r9, r5
	str r0, [sp, #260]
	lsls r5, r6, #6
	lsls r3, r3, #25
	orr.w r1, r5, r4, lsr #26
	str r1, [sp, #312]
	bic.w r5, r0, r1
	lsls r0, r4, #6
	orr.w r0, r0, r6, lsr #26
	orr.w r1, r3, r8, lsr #7
	str r0, [sp, #308]
	bic.w r0, r1, r0
	eor.w r0, r0, r11
	str.w r0, [lr, #88]
	ldr r0, [sp, #72]
	ldr.w r9, [sp, #248]
	eor.w r8, r10, r0
	ldr r0, [sp, #300]
	eor.w r5, r5, r9
	str.w r5, [lr, #92]
	ldr r5, [sp, #208]
	eor.w r3, r12, r0
	ldr r6, [sp, #140]
	lsl.w r4, r8, #28
	ldr.w r12, [sp, #296]
	orr.w r0, r4, r3, lsr #4
	eors r5, r2
	str r1, [sp, #252]
	eor.w r4, r12, r6
	str r0, [sp, #244]
	lsls r3, r3, #28
	lsls r6, r4, #29
	orr.w r1, r6, r5, lsr #3
	bic.w r6, r0, r1
	lsls r0, r5, #29
	str r1, [sp, #304]
	orr.w r1, r3, r8, lsr #4
	orr.w r0, r0, r4, lsr #3
	str r0, [sp, #300]
	bic.w r0, r1, r0
	str r1, [sp, #216]
	eor.w r0, r0, r11
	str.w r0, [lr, #48]
	ldr r0, [sp, #232]
	eor.w r6, r6, r9
	ldr r1, [sp, #336]
	eor.w r8, r10, r0
	ldr r0, [sp, #240]
	str.w r6, [lr, #52]
	eor.w r3, r1, r0
	ldr r6, [sp, #200]
	lsl.w r4, r8, #21
	ldr r5, [sp, #228]
	orr.w r0, r4, r3, lsr #11
	eor.w r4, r12, r6
	eor.w r1, r2, r5
	str r0, [sp, #208]
	lsls r5, r4, #11
	lsls r3, r3, #21
	orr.w r5, r5, r1, lsr #21
	str r5, [sp, #240]
	bic.w r5, r0, r5
	lsls r0, r1, #11
	orr.w r2, r3, r8, lsr #11
	orr.w r0, r0, r4, lsr #21
	str r0, [sp, #232]
	bic.w r0, r2, r0
	eor.w r5, r5, r9
	eor.w r0, r0, r11
	ldrd r1, r6, [sp, #124]
	str.w r5, [lr, #12]
	str.w r0, [lr, #8]
	eors r1, r6
	ldr r5, [sp, #108]
	ldr r0, [sp, #292]
	lsls r3, r1, #2
	str r2, [sp, #228]
	mov r2, lr
	eors r0, r5
	orr.w r4, r3, r0, lsr #30
	lsls r0, r0, #2
	orr.w r1, r0, r1, lsr #30
	ldr r0, [sp, #328]
	ldr r3, [sp, #340]
	bic.w r0, r0, r11
	str r1, [sp, #336]
	eors r0, r1
	ldr r1, [sp, #156]
	str.w r0, [lr, #160]
	bic.w r3, r3, r9
	ldr r0, [sp, #96]
	eors r1, r6
	eors r3, r4
	str.w r3, [lr, #164]
	eors r0, r5
	str r4, [sp, #292]
	lsls r3, r1, #10
	orr.w r4, r3, r0, lsr #22
	lsls r0, r0, #10
	orr.w r1, r0, r1, lsr #22
	ldr r0, [sp, #320]
	ldr r3, [sp, #324]
	mov r10, r4
	bic.w r0, r0, r11
	str r1, [sp, #296]
	eors r0, r1
	bic.w r3, r3, r9
	str.w r0, [lr, #120]
	eors r3, r4
	ldr r0, [sp, #84]
	ldr r1, [sp, #268]
	str.w r3, [lr, #124]
	eors r0, r1
	ldr r1, [sp, #284]
	ldr r3, [sp, #256]
	eors r0, r5
	str r4, [sp, #200]
	eors r1, r3
	ldr r4, [sp, #292]
	eors r1, r6
	lsls r3, r1, #1
	orr.w r12, r3, r0, lsr #31
	lsls r0, r0, #1
	orr.w r1, r0, r1, lsr #31
	ldr r0, [sp, #308]
	ldr r3, [sp, #312]
	bic.w r0, r0, r11
	str r1, [sp, #284]
	eors r0, r1
	ldr r1, [sp, #288]
	str.w r0, [lr, #80]
	bic.w r3, r3, r9
	ldr r0, [sp, #280]
	eors r1, r5
	eor.w r3, r3, r12
	str.w r3, [lr, #84]
	eors r0, r6
	lsls r3, r1, #13
	str.w r12, [sp, #268]
	orr.w r6, r3, r0, lsr #19
	lsls r0, r0, #13
	orr.w r1, r0, r1, lsr #19
	ldr r0, [sp, #300]
	str r1, [sp, #280]
	bic.w r0, r0, r11
	ldr r3, [sp, #304]
	eors r0, r1
	str.w r0, [lr, #40]
	ldr r0, [sp, #192]
	bic.w r3, r3, r9
	ldr r1, [sp, #160]
	eors r3, r6
	str.w r3, [lr, #44]
	lsls r0, r0, #1
	ldr r3, [sp, #204]
	orr.w r0, r0, r1, lsr #31
	ldr r1, [sp, #88]
	str r6, [sp, #288]
	eor.w r8, r0, r1
	ldr r1, [sp, #164]
	ldr r0, [sp, #136]
	lsls r1, r1, #1
	eor.w r0, r0, r8
	orr.w r1, r1, r3, lsr #31
	ldr r3, [sp, #92]
	eors r1, r3
	ldr r3, [sp, #132]
	eors r3, r1
	lsls r6, r3, #7
	orr.w r5, r6, r0, lsr #25
	bic.w r6, r9, r4
	lsls r0, r0, #7
	str r5, [sp, #176]
	eors r6, r5
	orr.w r5, r0, r3, lsr #25
	ldr r0, [sp, #336]
	ldr r3, [sp, #168]
	bic.w r0, r11, r0
	eors r0, r5
	strd r0, r6, [lr, #192]
	ldr r0, [sp, #144]
	eor.w r3, r3, r8
	eors r0, r1
	lsls r6, r3, #27
	orr.w r4, r6, r0, lsr #5
	lsls r0, r0, #27
	bic.w r6, r9, r10
	orr.w r10, r0, r3, lsr #5
	ldr r0, [sp, #296]
	eors r6, r4
	str.w r6, [lr, #156]
	bic.w r3, r11, r0
	ldr r6, [sp, #180]
	eor.w r3, r3, r10
	str.w r3, [lr, #152]
	ldr r3, [sp, #152]
	eor.w r6, r6, r8
	str r4, [sp, #204]
	eors r3, r1
	lsls r4, r6, #9
	orr.w r0, r4, r3, lsr #23
	bic.w r4, r9, r12
	eors r4, r0
	str r0, [sp, #192]
	ldr r0, [sp, #284]
	lsls r3, r3, #9
	str.w r4, [lr, #116]
	orr.w lr, r3, r6, lsr #23
	bic.w r6, r11, r0
	ldr r0, [sp, #288]
	eor.w r6, r6, lr
	str r6, [r2, #112]
	ldr r6, [sp, #184]
	eor.w r4, r1, r6
	ldr r6, [sp, #196]
	eor.w r12, r8, r6
	lsl.w r6, r12, #20
	orr.w r3, r6, r4, lsr #12
	bic.w r6, r9, r0
	ldr r0, [sp, #280]
	lsls r4, r4, #20
	orr.w r12, r4, r12, lsr #12
	bic.w r4, r11, r0
	eors r6, r3
	eor.w r4, r4, r12
	str r4, [r2, #72]
	ldr r4, [sp, #188]
	str r3, [sp, #256]
	eor.w r3, r1, r4
	ldr r4, [sp, #212]
	str r6, [r2, #76]
	eor.w r4, r4, r8
	ldr.w r8, [sp, #236]
	lsls r6, r4, #14
	orr.w r1, r6, r3, lsr #18
	ldr r6, [sp, #332]
	str r1, [sp, #212]
	eor.w r0, r6, r8
	str r0, [sp, #332]
	bic.w r6, r9, r0
	ldr r0, [sp, #292]
	eors r6, r1
	lsls r1, r3, #14
	str r6, [r2, #36]
	orr.w r1, r1, r4, lsr #18
	ldrd r6, r4, [sp, #220]
	ldr r3, [sp, #176]
	eor.w r8, r6, r4
	ldr r4, [sp, #316]
	bic.w r6, r11, r8
	eors r6, r1
	str r6, [r2, #32]
	bic.w r6, r0, r3
	ldr r0, [sp, #336]
	eors r6, r4
	str.w r6, [r2, #188]
	bic.w r6, r0, r5
	ldr r0, [sp, #276]
	eors r6, r0
	str.w r6, [r2, #184]
	bic.w r6, r3, r4
	ldr r4, [sp, #340]
	bics r5, r0
	ldr r0, [sp, #328]
	eors r6, r4
	str.w r6, [r2, #180]
	eors r5, r0
	ldrd r0, r6, [sp, #200]
	ldr r4, [sp, #272]
	str.w r5, [r2, #176]
	bic.w r5, r0, r6
	ldr r0, [sp, #296]
	eors r5, r4
	str.w r5, [r2, #148]
	bic.w r5, r0, r10
	ldr r0, [sp, #264]
	ldr r3, [sp, #308]
	eors r5, r0
	str.w r5, [r2, #144]
	bic.w r5, r6, r4
	ldr r4, [sp, #324]
	bic.w r0, r10, r0
	ldr r6, [sp, #192]
	eors r5, r4
	ldr r4, [sp, #320]
	str.w r5, [r2, #140]
	eors r0, r4
	str.w r0, [r2, #136]
	ldr r0, [sp, #268]
	ldr r4, [sp, #260]
	bics r0, r6
	ldr r5, [sp, #252]
	eors r0, r4
	str r0, [r2, #108]
	ldr r0, [sp, #284]
	bic.w r0, r0, lr
	eors r0, r5
	str r0, [r2, #104]
	bic.w r0, r6, r4
	ldr r4, [sp, #312]
	ldr r6, [sp, #256]
	eors r0, r4
	str r0, [r2, #100]
	bic.w r0, lr, r5
	ldr r4, [sp, #216]
	eors r0, r3
	str r0, [r2, #96]
	ldr r0, [sp, #288]
	ldr r3, [sp, #244]
	bics r0, r6
	ldr r5, [sp, #212]
	eors r0, r3
	str r0, [r2, #68]
	ldr r0, [sp, #280]
	bic.w r0, r0, r12
	eors r0, r4
	str r0, [r2, #64]
	bic.w r0, r6, r3
	ldr r3, [sp, #304]
	ldr r6, [sp, #228]
	eors r0, r3
	ldr r3, [sp, #300]
	str r0, [r2, #60]
	bic.w r0, r12, r4
	ldr r4, [sp, #332]
	eors r0, r3
	ldr r3, [sp, #208]
	str r0, [r2, #56]
	bic.w r0, r4, r5
	eors r0, r3
	str r0, [r2, #28]
	bic.w r0, r8, r1
	eors r0, r6
	str r0, [r2, #24]
	bic.w r0, r5, r3
	ldr r3, [sp, #240]
	eors r0, r3
	str r0, [r2, #20]
	bic.w r0, r1, r6
	ldr r1, [sp, #232]
	eors r0, r1
	str r0, [r2, #16]
	bic.w r0, r3, r9
	eors r0, r4
	eor r0, r0, #-2147483648
	str r0, [r2, #4]
	bic.w r0, r1, r11
	eor.w r0, r0, r8
	eor r0, r0, #-2147450880
	str r0, [r2]
	add sp, #344
	pop.w {r8, r9, r10, r11}
	pop {r4, r5, r6, r7, pc}
