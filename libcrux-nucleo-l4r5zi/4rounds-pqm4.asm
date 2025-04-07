08005100 <KeccakF1600_StatePermute_4Rounds>:
 8005100:	f2af 1104 	subw	r1, pc, #260	@ 0x104
 8005104:	e92d 5ff0 	stmdb	sp!, {r4, r5, r6, r7, r8, r9, sl, fp, ip, lr}
 8005108:	b086      	sub	sp, #24
 800510a:	9105      	str	r1, [sp, #20]
 800510c:	f8d0 3020 	ldr.w	r3, [r0, #32]
 8005110:	f8d0 1048 	ldr.w	r1, [r0, #72]	@ 0x48
 8005114:	f8d0 5070 	ldr.w	r5, [r0, #112]	@ 0x70
 8005118:	f8d0 b098 	ldr.w	fp, [r0, #152]	@ 0x98
 800511c:	f8d0 c0c0 	ldr.w	ip, [r0, #192]	@ 0xc0
 8005120:	ea83 0301 	eor.w	r3, r3, r1
 8005124:	ea83 0305 	eor.w	r3, r3, r5
 8005128:	ea83 030b 	eor.w	r3, r3, fp
 800512c:	ea83 030c 	eor.w	r3, r3, ip
 8005130:	f8d0 700c 	ldr.w	r7, [r0, #12]
 8005134:	f8d0 1034 	ldr.w	r1, [r0, #52]	@ 0x34
 8005138:	f8d0 505c 	ldr.w	r5, [r0, #92]	@ 0x5c
 800513c:	f8d0 b084 	ldr.w	fp, [r0, #132]	@ 0x84
 8005140:	f8d0 c0ac 	ldr.w	ip, [r0, #172]	@ 0xac
 8005144:	ea87 0701 	eor.w	r7, r7, r1
 8005148:	ea87 0705 	eor.w	r7, r7, r5
 800514c:	ea87 070b 	eor.w	r7, r7, fp
 8005150:	ea87 070c 	eor.w	r7, r7, ip
 8005154:	ea83 76f7 	eor.w	r6, r3, r7, ror #31
 8005158:	f8d0 4014 	ldr.w	r4, [r0, #20]
 800515c:	f8d0 103c 	ldr.w	r1, [r0, #60]	@ 0x3c
 8005160:	f8d0 5064 	ldr.w	r5, [r0, #100]	@ 0x64
 8005164:	f8d0 b08c 	ldr.w	fp, [r0, #140]	@ 0x8c
 8005168:	f8d0 c0b4 	ldr.w	ip, [r0, #180]	@ 0xb4
 800516c:	f8cd 6000 	str.w	r6, [sp]
 8005170:	ea84 0401 	eor.w	r4, r4, r1
 8005174:	ea84 0405 	eor.w	r4, r4, r5
 8005178:	ea84 040b 	eor.w	r4, r4, fp
 800517c:	ea84 040c 	eor.w	r4, r4, ip
 8005180:	ea83 0604 	eor.w	r6, r3, r4
 8005184:	f8d0 3018 	ldr.w	r3, [r0, #24]
 8005188:	f8d0 1040 	ldr.w	r1, [r0, #64]	@ 0x40
 800518c:	f8d0 5068 	ldr.w	r5, [r0, #104]	@ 0x68
 8005190:	f8d0 b090 	ldr.w	fp, [r0, #144]	@ 0x90
 8005194:	f8d0 c0b8 	ldr.w	ip, [r0, #184]	@ 0xb8
 8005198:	f8cd 600c 	str.w	r6, [sp, #12]
 800519c:	ea83 0301 	eor.w	r3, r3, r1
 80051a0:	ea83 0305 	eor.w	r3, r3, r5
 80051a4:	ea83 030b 	eor.w	r3, r3, fp
 80051a8:	ea83 030c 	eor.w	r3, r3, ip
 80051ac:	ea87 0203 	eor.w	r2, r7, r3
 80051b0:	f8d0 7000 	ldr.w	r7, [r0]
 80051b4:	f8d0 1028 	ldr.w	r1, [r0, #40]	@ 0x28
 80051b8:	f8d0 5050 	ldr.w	r5, [r0, #80]	@ 0x50
 80051bc:	f8d0 b078 	ldr.w	fp, [r0, #120]	@ 0x78
 80051c0:	f8d0 c0a0 	ldr.w	ip, [r0, #160]	@ 0xa0
 80051c4:	ea87 0701 	eor.w	r7, r7, r1
 80051c8:	ea87 0705 	eor.w	r7, r7, r5
 80051cc:	ea87 070b 	eor.w	r7, r7, fp
 80051d0:	ea87 070c 	eor.w	r7, r7, ip
 80051d4:	ea87 7af4 	eor.w	sl, r7, r4, ror #31
 80051d8:	f8d0 401c 	ldr.w	r4, [r0, #28]
 80051dc:	f8d0 1044 	ldr.w	r1, [r0, #68]	@ 0x44
 80051e0:	f8d0 506c 	ldr.w	r5, [r0, #108]	@ 0x6c
 80051e4:	f8d0 b094 	ldr.w	fp, [r0, #148]	@ 0x94
 80051e8:	f8d0 c0bc 	ldr.w	ip, [r0, #188]	@ 0xbc
 80051ec:	ea84 0401 	eor.w	r4, r4, r1
 80051f0:	ea84 0405 	eor.w	r4, r4, r5
 80051f4:	ea84 040b 	eor.w	r4, r4, fp
 80051f8:	ea84 040c 	eor.w	r4, r4, ip
 80051fc:	ea84 0e07 	eor.w	lr, r4, r7
 8005200:	f8d0 7008 	ldr.w	r7, [r0, #8]
 8005204:	f8d0 1030 	ldr.w	r1, [r0, #48]	@ 0x30
 8005208:	f8d0 5058 	ldr.w	r5, [r0, #88]	@ 0x58
 800520c:	f8d0 b080 	ldr.w	fp, [r0, #128]	@ 0x80
 8005210:	f8d0 c0a8 	ldr.w	ip, [r0, #168]	@ 0xa8
 8005214:	ea87 0701 	eor.w	r7, r7, r1
 8005218:	ea87 0705 	eor.w	r7, r7, r5
 800521c:	ea87 070b 	eor.w	r7, r7, fp
 8005220:	ea87 070c 	eor.w	r7, r7, ip
 8005224:	ea87 76f4 	eor.w	r6, r7, r4, ror #31
 8005228:	f8d0 4024 	ldr.w	r4, [r0, #36]	@ 0x24
 800522c:	f8d0 104c 	ldr.w	r1, [r0, #76]	@ 0x4c
 8005230:	f8d0 5074 	ldr.w	r5, [r0, #116]	@ 0x74
 8005234:	f8d0 b09c 	ldr.w	fp, [r0, #156]	@ 0x9c
 8005238:	f8d0 c0c4 	ldr.w	ip, [r0, #196]	@ 0xc4
 800523c:	f8cd 6010 	str.w	r6, [sp, #16]
 8005240:	ea84 0401 	eor.w	r4, r4, r1
 8005244:	ea84 0405 	eor.w	r4, r4, r5
 8005248:	ea84 040b 	eor.w	r4, r4, fp
 800524c:	ea84 040c 	eor.w	r4, r4, ip
 8005250:	ea84 0807 	eor.w	r8, r4, r7
 8005254:	f8d0 7010 	ldr.w	r7, [r0, #16]
 8005258:	f8d0 1038 	ldr.w	r1, [r0, #56]	@ 0x38
 800525c:	f8d0 5060 	ldr.w	r5, [r0, #96]	@ 0x60
 8005260:	f8d0 b088 	ldr.w	fp, [r0, #136]	@ 0x88
 8005264:	f8d0 c0b0 	ldr.w	ip, [r0, #176]	@ 0xb0
 8005268:	f8cd 8004 	str.w	r8, [sp, #4]
 800526c:	ea87 0701 	eor.w	r7, r7, r1
 8005270:	ea87 0705 	eor.w	r7, r7, r5
 8005274:	ea87 070b 	eor.w	r7, r7, fp
 8005278:	ea87 070c 	eor.w	r7, r7, ip
 800527c:	ea87 79f4 	eor.w	r9, r7, r4, ror #31
 8005280:	f8d0 4004 	ldr.w	r4, [r0, #4]
 8005284:	f8d0 102c 	ldr.w	r1, [r0, #44]	@ 0x2c
 8005288:	f8d0 5054 	ldr.w	r5, [r0, #84]	@ 0x54
 800528c:	f8d0 b07c 	ldr.w	fp, [r0, #124]	@ 0x7c
 8005290:	f8d0 c0a4 	ldr.w	ip, [r0, #164]	@ 0xa4
 8005294:	f8cd 9008 	str.w	r9, [sp, #8]
 8005298:	ea84 0401 	eor.w	r4, r4, r1
 800529c:	ea84 0405 	eor.w	r4, r4, r5
 80052a0:	ea84 040b 	eor.w	r4, r4, fp
 80052a4:	ea84 040c 	eor.w	r4, r4, ip
 80052a8:	ea84 0b07 	eor.w	fp, r4, r7
 80052ac:	ea83 7cf4 	eor.w	ip, r3, r4, ror #31
 80052b0:	f8d0 3018 	ldr.w	r3, [r0, #24]
 80052b4:	f8d0 4048 	ldr.w	r4, [r0, #72]	@ 0x48
 80052b8:	f8d0 5054 	ldr.w	r5, [r0, #84]	@ 0x54
 80052bc:	f8d0 6084 	ldr.w	r6, [r0, #132]	@ 0x84
 80052c0:	f8d0 70b4 	ldr.w	r7, [r0, #180]	@ 0xb4
 80052c4:	f8c0 1054 	str.w	r1, [r0, #84]	@ 0x54
 80052c8:	ea89 0303 	eor.w	r3, r9, r3
 80052cc:	ea8c 0404 	eor.w	r4, ip, r4
 80052d0:	ea88 0505 	eor.w	r5, r8, r5
 80052d4:	ea8b 0606 	eor.w	r6, fp, r6
 80052d8:	ea82 0707 	eor.w	r7, r2, r7
 80052dc:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 80052e0:	ea81 5133 	eor.w	r1, r1, r3, ror #20
 80052e4:	f8c0 1054 	str.w	r1, [r0, #84]	@ 0x54
 80052e8:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 80052ec:	ea81 3174 	eor.w	r1, r1, r4, ror #13
 80052f0:	f8c0 1084 	str.w	r1, [r0, #132]	@ 0x84
 80052f4:	ea27 2136 	bic.w	r1, r7, r6, ror #8
 80052f8:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 80052fc:	f8c0 10b4 	str.w	r1, [r0, #180]	@ 0xb4
 8005300:	ea23 31f7 	bic.w	r1, r3, r7, ror #15
 8005304:	ea81 51f6 	eor.w	r1, r1, r6, ror #23
 8005308:	f8c0 1018 	str.w	r1, [r0, #24]
 800530c:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 8005310:	ea81 21f7 	eor.w	r1, r1, r7, ror #11
 8005314:	f8d0 3008 	ldr.w	r3, [r0, #8]
 8005318:	f8d0 403c 	ldr.w	r4, [r0, #60]	@ 0x3c
 800531c:	f8d0 5068 	ldr.w	r5, [r0, #104]	@ 0x68
 8005320:	f8d0 609c 	ldr.w	r6, [r0, #156]	@ 0x9c
 8005324:	f8d0 70a4 	ldr.w	r7, [r0, #164]	@ 0xa4
 8005328:	f8c0 1048 	str.w	r1, [r0, #72]	@ 0x48
 800532c:	ea8a 0303 	eor.w	r3, sl, r3
 8005330:	ea82 0404 	eor.w	r4, r2, r4
 8005334:	ea89 0505 	eor.w	r5, r9, r5
 8005338:	ea8e 0606 	eor.w	r6, lr, r6
 800533c:	ea88 0707 	eor.w	r7, r8, r7
 8005340:	ea25 2174 	bic.w	r1, r5, r4, ror #9
 8005344:	ea81 3133 	eor.w	r1, r1, r3, ror #12
 8005348:	f8c0 10a4 	str.w	r1, [r0, #164]	@ 0xa4
 800534c:	ea26 6135 	bic.w	r1, r6, r5, ror #24
 8005350:	ea81 0174 	eor.w	r1, r1, r4, ror #1
 8005354:	f8c0 1008 	str.w	r1, [r0, #8]
 8005358:	ea27 1176 	bic.w	r1, r7, r6, ror #5
 800535c:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 8005360:	f8c0 103c 	str.w	r1, [r0, #60]	@ 0x3c
 8005364:	ea23 51f7 	bic.w	r1, r3, r7, ror #23
 8005368:	ea81 7136 	eor.w	r1, r1, r6, ror #28
 800536c:	f8c0 1068 	str.w	r1, [r0, #104]	@ 0x68
 8005370:	ea24 01f3 	bic.w	r1, r4, r3, ror #3
 8005374:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 8005378:	f8dd 8000 	ldr.w	r8, [sp]
 800537c:	f8d0 3024 	ldr.w	r3, [r0, #36]	@ 0x24
 8005380:	f8d0 4028 	ldr.w	r4, [r0, #40]	@ 0x28
 8005384:	f8d0 5058 	ldr.w	r5, [r0, #88]	@ 0x58
 8005388:	f8d0 608c 	ldr.w	r6, [r0, #140]	@ 0x8c
 800538c:	f8d0 70b8 	ldr.w	r7, [r0, #184]	@ 0xb8
 8005390:	f8c0 109c 	str.w	r1, [r0, #156]	@ 0x9c
 8005394:	ea8e 0303 	eor.w	r3, lr, r3
 8005398:	ea88 0404 	eor.w	r4, r8, r4
 800539c:	ea8a 0505 	eor.w	r5, sl, r5
 80053a0:	ea82 0606 	eor.w	r6, r2, r6
 80053a4:	ea89 0707 	eor.w	r7, r9, r7
 80053a8:	ea25 41f4 	bic.w	r1, r5, r4, ror #19
 80053ac:	ea81 51f3 	eor.w	r1, r1, r3, ror #23
 80053b0:	f8c0 1028 	str.w	r1, [r0, #40]	@ 0x28
 80053b4:	ea26 01f5 	bic.w	r1, r6, r5, ror #3
 80053b8:	ea81 51b4 	eor.w	r1, r1, r4, ror #22
 80053bc:	f8c0 1058 	str.w	r1, [r0, #88]	@ 0x58
 80053c0:	ea27 5136 	bic.w	r1, r7, r6, ror #20
 80053c4:	ea81 51f5 	eor.w	r1, r1, r5, ror #23
 80053c8:	f8c0 108c 	str.w	r1, [r0, #140]	@ 0x8c
 80053cc:	ea23 41b7 	bic.w	r1, r3, r7, ror #18
 80053d0:	ea81 11b6 	eor.w	r1, r1, r6, ror #6
 80053d4:	f8c0 10b8 	str.w	r1, [r0, #184]	@ 0xb8
 80053d8:	ea24 1133 	bic.w	r1, r4, r3, ror #4
 80053dc:	ea81 51b7 	eor.w	r1, r1, r7, ror #22
 80053e0:	f8d0 3014 	ldr.w	r3, [r0, #20]
 80053e4:	f8d0 4040 	ldr.w	r4, [r0, #64]	@ 0x40
 80053e8:	f8d0 5070 	ldr.w	r5, [r0, #112]	@ 0x70
 80053ec:	f8d0 6078 	ldr.w	r6, [r0, #120]	@ 0x78
 80053f0:	f8d0 70ac 	ldr.w	r7, [r0, #172]	@ 0xac
 80053f4:	f8c0 1024 	str.w	r1, [r0, #36]	@ 0x24
 80053f8:	ea82 0303 	eor.w	r3, r2, r3
 80053fc:	ea89 0404 	eor.w	r4, r9, r4
 8005400:	ea8c 0505 	eor.w	r5, ip, r5
 8005404:	ea88 0606 	eor.w	r6, r8, r6
 8005408:	ea8b 0707 	eor.w	r7, fp, r7
 800540c:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 8005410:	ea81 5133 	eor.w	r1, r1, r3, ror #20
 8005414:	f8c0 1078 	str.w	r1, [r0, #120]	@ 0x78
 8005418:	ea26 0175 	bic.w	r1, r6, r5, ror #1
 800541c:	ea81 6174 	eor.w	r1, r1, r4, ror #25
 8005420:	f8c0 10ac 	str.w	r1, [r0, #172]	@ 0xac
 8005424:	ea27 3176 	bic.w	r1, r7, r6, ror #13
 8005428:	ea81 31b5 	eor.w	r1, r1, r5, ror #14
 800542c:	f8c0 1014 	str.w	r1, [r0, #20]
 8005430:	ea23 71b7 	bic.w	r1, r3, r7, ror #30
 8005434:	ea81 21f6 	eor.w	r1, r1, r6, ror #11
 8005438:	f8c0 1040 	str.w	r1, [r0, #64]	@ 0x40
 800543c:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 8005440:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 8005444:	f8dd 900c 	ldr.w	r9, [sp, #12]
 8005448:	f8d0 3000 	ldr.w	r3, [r0]
 800544c:	6b04      	ldr	r4, [r0, #48]	@ 0x30
 800544e:	6e45      	ldr	r5, [r0, #100]	@ 0x64
 8005450:	f8d0 6094 	ldr.w	r6, [r0, #148]	@ 0x94
 8005454:	f8d0 70c0 	ldr.w	r7, [r0, #192]	@ 0xc0
 8005458:	f8c0 1070 	str.w	r1, [r0, #112]	@ 0x70
 800545c:	ea88 0303 	eor.w	r3, r8, r3
 8005460:	ea8a 0404 	eor.w	r4, sl, r4
 8005464:	ea82 0505 	eor.w	r5, r2, r5
 8005468:	ea89 0606 	eor.w	r6, r9, r6
 800546c:	ea8c 0707 	eor.w	r7, ip, r7
 8005470:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8005474:	ea81 5174 	eor.w	r1, r1, r4, ror #21
 8005478:	f8c0 1030 	str.w	r1, [r0, #48]	@ 0x30
 800547c:	ea27 7136 	bic.w	r1, r7, r6, ror #28
 8005480:	ea81 4175 	eor.w	r1, r1, r5, ror #17
 8005484:	f8c0 1064 	str.w	r1, [r0, #100]	@ 0x64
 8005488:	ea23 6177 	bic.w	r1, r3, r7, ror #25
 800548c:	ea81 5176 	eor.w	r1, r1, r6, ror #21
 8005490:	f8c0 1094 	str.w	r1, [r0, #148]	@ 0x94
 8005494:	ea24 51b3 	bic.w	r1, r4, r3, ror #22
 8005498:	ea81 31f7 	eor.w	r1, r1, r7, ror #15
 800549c:	f8c0 10c0 	str.w	r1, [r0, #192]	@ 0xc0
 80054a0:	ea25 0504 	bic.w	r5, r5, r4
 80054a4:	9905      	ldr	r1, [sp, #20]
 80054a6:	680c      	ldr	r4, [r1, #0]
 80054a8:	ea83 23b5 	eor.w	r3, r3, r5, ror #10
 80054ac:	ea84 0103 	eor.w	r1, r4, r3
 80054b0:	f8dd 2010 	ldr.w	r2, [sp, #16]
 80054b4:	f8d0 301c 	ldr.w	r3, [r0, #28]
 80054b8:	f8d0 404c 	ldr.w	r4, [r0, #76]	@ 0x4c
 80054bc:	f8d0 5050 	ldr.w	r5, [r0, #80]	@ 0x50
 80054c0:	f8d0 6080 	ldr.w	r6, [r0, #128]	@ 0x80
 80054c4:	f8d0 70b0 	ldr.w	r7, [r0, #176]	@ 0xb0
 80054c8:	f8c0 1000 	str.w	r1, [r0]
 80054cc:	ea89 0303 	eor.w	r3, r9, r3
 80054d0:	ea8e 0404 	eor.w	r4, lr, r4
 80054d4:	ea88 0505 	eor.w	r5, r8, r5
 80054d8:	ea8a 0606 	eor.w	r6, sl, r6
 80054dc:	ea82 0707 	eor.w	r7, r2, r7
 80054e0:	ea25 51f4 	bic.w	r1, r5, r4, ror #23
 80054e4:	ea81 41f3 	eor.w	r1, r1, r3, ror #19
 80054e8:	f8c0 1050 	str.w	r1, [r0, #80]	@ 0x50
 80054ec:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 80054f0:	ea81 3134 	eor.w	r1, r1, r4, ror #12
 80054f4:	f8c0 1080 	str.w	r1, [r0, #128]	@ 0x80
 80054f8:	ea27 2136 	bic.w	r1, r7, r6, ror #8
 80054fc:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 8005500:	f8c0 10b0 	str.w	r1, [r0, #176]	@ 0xb0
 8005504:	ea23 4137 	bic.w	r1, r3, r7, ror #16
 8005508:	ea81 6136 	eor.w	r1, r1, r6, ror #24
 800550c:	f8c0 101c 	str.w	r1, [r0, #28]
 8005510:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 8005514:	ea81 3137 	eor.w	r1, r1, r7, ror #12
 8005518:	f8d0 300c 	ldr.w	r3, [r0, #12]
 800551c:	f8d0 4038 	ldr.w	r4, [r0, #56]	@ 0x38
 8005520:	f8d0 506c 	ldr.w	r5, [r0, #108]	@ 0x6c
 8005524:	f8d0 6098 	ldr.w	r6, [r0, #152]	@ 0x98
 8005528:	f8d0 70a0 	ldr.w	r7, [r0, #160]	@ 0xa0
 800552c:	f8c0 104c 	str.w	r1, [r0, #76]	@ 0x4c
 8005530:	ea8b 0303 	eor.w	r3, fp, r3
 8005534:	ea82 0404 	eor.w	r4, r2, r4
 8005538:	ea89 0505 	eor.w	r5, r9, r5
 800553c:	ea8c 0606 	eor.w	r6, ip, r6
 8005540:	ea88 0707 	eor.w	r7, r8, r7
 8005544:	ea25 21b4 	bic.w	r1, r5, r4, ror #10
 8005548:	ea81 3133 	eor.w	r1, r1, r3, ror #12
 800554c:	f8c0 10a0 	str.w	r1, [r0, #160]	@ 0xa0
 8005550:	ea26 51f5 	bic.w	r1, r6, r5, ror #23
 8005554:	ea81 0174 	eor.w	r1, r1, r4, ror #1
 8005558:	f8c0 100c 	str.w	r1, [r0, #12]
 800555c:	ea27 1176 	bic.w	r1, r7, r6, ror #5
 8005560:	ea81 7135 	eor.w	r1, r1, r5, ror #28
 8005564:	f8c0 1038 	str.w	r1, [r0, #56]	@ 0x38
 8005568:	ea23 6137 	bic.w	r1, r3, r7, ror #24
 800556c:	ea81 7176 	eor.w	r1, r1, r6, ror #29
 8005570:	f8c0 106c 	str.w	r1, [r0, #108]	@ 0x6c
 8005574:	ea24 01b3 	bic.w	r1, r4, r3, ror #2
 8005578:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 800557c:	f8dd 8004 	ldr.w	r8, [sp, #4]
 8005580:	f8d0 3020 	ldr.w	r3, [r0, #32]
 8005584:	f8d0 402c 	ldr.w	r4, [r0, #44]	@ 0x2c
 8005588:	f8d0 505c 	ldr.w	r5, [r0, #92]	@ 0x5c
 800558c:	f8d0 6088 	ldr.w	r6, [r0, #136]	@ 0x88
 8005590:	f8d0 70bc 	ldr.w	r7, [r0, #188]	@ 0xbc
 8005594:	f8c0 1098 	str.w	r1, [r0, #152]	@ 0x98
 8005598:	ea8c 0303 	eor.w	r3, ip, r3
 800559c:	ea88 0404 	eor.w	r4, r8, r4
 80055a0:	ea8b 0505 	eor.w	r5, fp, r5
 80055a4:	ea82 0606 	eor.w	r6, r2, r6
 80055a8:	ea89 0707 	eor.w	r7, r9, r7
 80055ac:	ea25 41f4 	bic.w	r1, r5, r4, ror #19
 80055b0:	ea81 6133 	eor.w	r1, r1, r3, ror #24
 80055b4:	f8c0 102c 	str.w	r1, [r0, #44]	@ 0x2c
 80055b8:	ea26 01b5 	bic.w	r1, r6, r5, ror #2
 80055bc:	ea81 5174 	eor.w	r1, r1, r4, ror #21
 80055c0:	f8c0 105c 	str.w	r1, [r0, #92]	@ 0x5c
 80055c4:	ea27 5176 	bic.w	r1, r7, r6, ror #21
 80055c8:	ea81 51f5 	eor.w	r1, r1, r5, ror #23
 80055cc:	f8c0 1088 	str.w	r1, [r0, #136]	@ 0x88
 80055d0:	ea23 4177 	bic.w	r1, r3, r7, ror #17
 80055d4:	ea81 11b6 	eor.w	r1, r1, r6, ror #6
 80055d8:	f8c0 10bc 	str.w	r1, [r0, #188]	@ 0xbc
 80055dc:	ea24 1173 	bic.w	r1, r4, r3, ror #5
 80055e0:	ea81 51b7 	eor.w	r1, r1, r7, ror #22
 80055e4:	f8d0 3010 	ldr.w	r3, [r0, #16]
 80055e8:	f8d0 4044 	ldr.w	r4, [r0, #68]	@ 0x44
 80055ec:	f8d0 5074 	ldr.w	r5, [r0, #116]	@ 0x74
 80055f0:	f8d0 607c 	ldr.w	r6, [r0, #124]	@ 0x7c
 80055f4:	f8d0 70a8 	ldr.w	r7, [r0, #168]	@ 0xa8
 80055f8:	f8c0 1020 	str.w	r1, [r0, #32]
 80055fc:	ea82 0303 	eor.w	r3, r2, r3
 8005600:	ea89 0404 	eor.w	r4, r9, r4
 8005604:	ea8e 0505 	eor.w	r5, lr, r5
 8005608:	ea88 0606 	eor.w	r6, r8, r6
 800560c:	ea8a 0707 	eor.w	r7, sl, r7
 8005610:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 8005614:	ea81 5173 	eor.w	r1, r1, r3, ror #21
 8005618:	f8c0 107c 	str.w	r1, [r0, #124]	@ 0x7c
 800561c:	ea26 0175 	bic.w	r1, r6, r5, ror #1
 8005620:	ea81 6174 	eor.w	r1, r1, r4, ror #25
 8005624:	f8c0 10a8 	str.w	r1, [r0, #168]	@ 0xa8
 8005628:	ea27 3136 	bic.w	r1, r7, r6, ror #12
 800562c:	ea81 3175 	eor.w	r1, r1, r5, ror #13
 8005630:	f8c0 1010 	str.w	r1, [r0, #16]
 8005634:	ea23 71b7 	bic.w	r1, r3, r7, ror #30
 8005638:	ea81 21b6 	eor.w	r1, r1, r6, ror #10
 800563c:	f8c0 1044 	str.w	r1, [r0, #68]	@ 0x44
 8005640:	ea24 7173 	bic.w	r1, r4, r3, ror #29
 8005644:	ea81 61f7 	eor.w	r1, r1, r7, ror #27
 8005648:	f8dd 9008 	ldr.w	r9, [sp, #8]
 800564c:	f8d0 3004 	ldr.w	r3, [r0, #4]
 8005650:	6b44      	ldr	r4, [r0, #52]	@ 0x34
 8005652:	6e05      	ldr	r5, [r0, #96]	@ 0x60
 8005654:	f8d0 6090 	ldr.w	r6, [r0, #144]	@ 0x90
 8005658:	f8d0 70c4 	ldr.w	r7, [r0, #196]	@ 0xc4
 800565c:	f8c0 1074 	str.w	r1, [r0, #116]	@ 0x74
 8005660:	ea88 0303 	eor.w	r3, r8, r3
 8005664:	ea8b 0404 	eor.w	r4, fp, r4
 8005668:	ea82 0505 	eor.w	r5, r2, r5
 800566c:	ea89 0606 	eor.w	r6, r9, r6
 8005670:	ea8e 0707 	eor.w	r7, lr, r7
 8005674:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8005678:	ea81 5134 	eor.w	r1, r1, r4, ror #20
 800567c:	f8c0 1034 	str.w	r1, [r0, #52]	@ 0x34
 8005680:	ea27 7176 	bic.w	r1, r7, r6, ror #29
 8005684:	ea81 41b5 	eor.w	r1, r1, r5, ror #18
 8005688:	f8c0 1060 	str.w	r1, [r0, #96]	@ 0x60
 800568c:	ea23 6177 	bic.w	r1, r3, r7, ror #25
 8005690:	ea81 51b6 	eor.w	r1, r1, r6, ror #22
 8005694:	f8c0 1090 	str.w	r1, [r0, #144]	@ 0x90
 8005698:	ea24 51b3 	bic.w	r1, r4, r3, ror #22
 800569c:	ea81 31f7 	eor.w	r1, r1, r7, ror #15
 80056a0:	f8c0 10c4 	str.w	r1, [r0, #196]	@ 0xc4
 80056a4:	ea25 75f4 	bic.w	r5, r5, r4, ror #31
 80056a8:	9905      	ldr	r1, [sp, #20]
 80056aa:	684c      	ldr	r4, [r1, #4]
 80056ac:	ea83 23f5 	eor.w	r3, r3, r5, ror #11
 80056b0:	ea84 0e03 	eor.w	lr, r4, r3
 80056b4:	f8d0 30c0 	ldr.w	r3, [r0, #192]	@ 0xc0
 80056b8:	f8d0 1048 	ldr.w	r1, [r0, #72]	@ 0x48
 80056bc:	f8d0 5098 	ldr.w	r5, [r0, #152]	@ 0x98
 80056c0:	f8d0 b024 	ldr.w	fp, [r0, #36]	@ 0x24
 80056c4:	f8d0 c074 	ldr.w	ip, [r0, #116]	@ 0x74
 80056c8:	f8c0 e004 	str.w	lr, [r0, #4]
 80056cc:	ea83 3331 	eor.w	r3, r3, r1, ror #12
 80056d0:	ea83 43f5 	eor.w	r3, r3, r5, ror #19
 80056d4:	ea83 133b 	eor.w	r3, r3, fp, ror #4
 80056d8:	ea83 63bc 	eor.w	r3, r3, ip, ror #26
 80056dc:	f8d0 7034 	ldr.w	r7, [r0, #52]	@ 0x34
 80056e0:	f8d0 1080 	ldr.w	r1, [r0, #128]	@ 0x80
 80056e4:	f8d0 5008 	ldr.w	r5, [r0, #8]
 80056e8:	f8d0 b05c 	ldr.w	fp, [r0, #92]	@ 0x5c
 80056ec:	f8d0 c0ac 	ldr.w	ip, [r0, #172]	@ 0xac
 80056f0:	ea87 5731 	eor.w	r7, r7, r1, ror #20
 80056f4:	ea87 17b5 	eor.w	r7, r7, r5, ror #6
 80056f8:	ea87 07fb 	eor.w	r7, r7, fp, ror #3
 80056fc:	ea87 57bc 	eor.w	r7, r7, ip, ror #22
 8005700:	ea4f 23b3 	mov.w	r3, r3, ror #10
 8005704:	ea83 5677 	eor.w	r6, r3, r7, ror #21
 8005708:	f8d0 4060 	ldr.w	r4, [r0, #96]	@ 0x60
 800570c:	f8d0 10b0 	ldr.w	r1, [r0, #176]	@ 0xb0
 8005710:	f8d0 503c 	ldr.w	r5, [r0, #60]	@ 0x3c
 8005714:	f8d0 b088 	ldr.w	fp, [r0, #136]	@ 0x88
 8005718:	f8d0 c014 	ldr.w	ip, [r0, #20]
 800571c:	f8cd 6000 	str.w	r6, [sp]
 8005720:	ea84 2471 	eor.w	r4, r4, r1, ror #9
 8005724:	ea84 74b5 	eor.w	r4, r4, r5, ror #30
 8005728:	ea84 24fb 	eor.w	r4, r4, fp, ror #11
 800572c:	ea84 14bc 	eor.w	r4, r4, ip, ror #6
 8005730:	ea83 6674 	eor.w	r6, r3, r4, ror #25
 8005734:	f8d0 3094 	ldr.w	r3, [r0, #148]	@ 0x94
 8005738:	f8d0 1018 	ldr.w	r1, [r0, #24]
 800573c:	f8d0 506c 	ldr.w	r5, [r0, #108]	@ 0x6c
 8005740:	f8d0 b0b8 	ldr.w	fp, [r0, #184]	@ 0xb8
 8005744:	f8d0 c044 	ldr.w	ip, [r0, #68]	@ 0x44
 8005748:	f8cd 600c 	str.w	r6, [sp, #12]
 800574c:	ea83 43b1 	eor.w	r3, r3, r1, ror #18
 8005750:	ea83 73f5 	eor.w	r3, r3, r5, ror #31
 8005754:	ea83 43bb 	eor.w	r3, r3, fp, ror #18
 8005758:	ea83 037c 	eor.w	r3, r3, ip, ror #1
 800575c:	ea83 52b7 	eor.w	r2, r3, r7, ror #22
 8005760:	f8d0 7000 	ldr.w	r7, [r0]
 8005764:	f8d0 1054 	ldr.w	r1, [r0, #84]	@ 0x54
 8005768:	f8d0 50a0 	ldr.w	r5, [r0, #160]	@ 0xa0
 800576c:	f8d0 b028 	ldr.w	fp, [r0, #40]	@ 0x28
 8005770:	f8d0 c07c 	ldr.w	ip, [r0, #124]	@ 0x7c
 8005774:	ea87 77b1 	eor.w	r7, r7, r1, ror #30
 8005778:	ea87 47f5 	eor.w	r7, r7, r5, ror #19
 800577c:	ea87 67fb 	eor.w	r7, r7, fp, ror #27
 8005780:	ea87 373c 	eor.w	r7, r7, ip, ror #12
 8005784:	ea87 6a34 	eor.w	sl, r7, r4, ror #24
 8005788:	f8d0 4090 	ldr.w	r4, [r0, #144]	@ 0x90
 800578c:	f8d0 101c 	ldr.w	r1, [r0, #28]
 8005790:	f8d0 5068 	ldr.w	r5, [r0, #104]	@ 0x68
 8005794:	f8d0 b0bc 	ldr.w	fp, [r0, #188]	@ 0xbc
 8005798:	f8d0 c040 	ldr.w	ip, [r0, #64]	@ 0x40
 800579c:	ea84 44b1 	eor.w	r4, r4, r1, ror #18
 80057a0:	ea84 0405 	eor.w	r4, r4, r5
 80057a4:	ea84 44fb 	eor.w	r4, r4, fp, ror #19
 80057a8:	ea84 047c 	eor.w	r4, r4, ip, ror #1
 80057ac:	ea84 0e07 	eor.w	lr, r4, r7
 80057b0:	f8d0 7030 	ldr.w	r7, [r0, #48]	@ 0x30
 80057b4:	f8d0 1084 	ldr.w	r1, [r0, #132]	@ 0x84
 80057b8:	f8d0 500c 	ldr.w	r5, [r0, #12]
 80057bc:	f8d0 b058 	ldr.w	fp, [r0, #88]	@ 0x58
 80057c0:	f8d0 c0a8 	ldr.w	ip, [r0, #168]	@ 0xa8
 80057c4:	ea87 5731 	eor.w	r7, r7, r1, ror #20
 80057c8:	ea87 17f5 	eor.w	r7, r7, r5, ror #7
 80057cc:	ea87 07fb 	eor.w	r7, r7, fp, ror #3
 80057d0:	ea87 57bc 	eor.w	r7, r7, ip, ror #22
 80057d4:	ea4f 5777 	mov.w	r7, r7, ror #21
 80057d8:	ea87 76f4 	eor.w	r6, r7, r4, ror #31
 80057dc:	f8d0 40c4 	ldr.w	r4, [r0, #196]	@ 0xc4
 80057e0:	f8d0 104c 	ldr.w	r1, [r0, #76]	@ 0x4c
 80057e4:	f8d0 509c 	ldr.w	r5, [r0, #156]	@ 0x9c
 80057e8:	f8d0 b020 	ldr.w	fp, [r0, #32]
 80057ec:	f8d0 c070 	ldr.w	ip, [r0, #112]	@ 0x70
 80057f0:	f8cd 6010 	str.w	r6, [sp, #16]
 80057f4:	ea84 3431 	eor.w	r4, r4, r1, ror #12
 80057f8:	ea84 44f5 	eor.w	r4, r4, r5, ror #19
 80057fc:	ea84 143b 	eor.w	r4, r4, fp, ror #4
 8005800:	ea84 64fc 	eor.w	r4, r4, ip, ror #27
 8005804:	ea87 28b4 	eor.w	r8, r7, r4, ror #10
 8005808:	f8d0 7064 	ldr.w	r7, [r0, #100]	@ 0x64
 800580c:	f8d0 10b4 	ldr.w	r1, [r0, #180]	@ 0xb4
 8005810:	f8d0 5038 	ldr.w	r5, [r0, #56]	@ 0x38
 8005814:	f8d0 b08c 	ldr.w	fp, [r0, #140]	@ 0x8c
 8005818:	f8d0 c010 	ldr.w	ip, [r0, #16]
 800581c:	f8cd 8004 	str.w	r8, [sp, #4]
 8005820:	ea87 2731 	eor.w	r7, r7, r1, ror #8
 8005824:	ea87 77b5 	eor.w	r7, r7, r5, ror #30
 8005828:	ea87 27fb 	eor.w	r7, r7, fp, ror #11
 800582c:	ea87 17bc 	eor.w	r7, r7, ip, ror #6
 8005830:	ea4f 6777 	mov.w	r7, r7, ror #25
 8005834:	ea87 2974 	eor.w	r9, r7, r4, ror #9
 8005838:	f8d0 4004 	ldr.w	r4, [r0, #4]
 800583c:	f8d0 1050 	ldr.w	r1, [r0, #80]	@ 0x50
 8005840:	f8d0 50a4 	ldr.w	r5, [r0, #164]	@ 0xa4
 8005844:	f8d0 b02c 	ldr.w	fp, [r0, #44]	@ 0x2c
 8005848:	f8d0 c078 	ldr.w	ip, [r0, #120]	@ 0x78
 800584c:	f8cd 9008 	str.w	r9, [sp, #8]
 8005850:	ea84 74f1 	eor.w	r4, r4, r1, ror #31
 8005854:	ea84 5435 	eor.w	r4, r4, r5, ror #20
 8005858:	ea84 64fb 	eor.w	r4, r4, fp, ror #27
 800585c:	ea84 347c 	eor.w	r4, r4, ip, ror #13
 8005860:	ea84 0b07 	eor.w	fp, r4, r7
 8005864:	ea83 7cf4 	eor.w	ip, r3, r4, ror #31
 8005868:	f8d0 3094 	ldr.w	r3, [r0, #148]	@ 0x94
 800586c:	f8d0 4048 	ldr.w	r4, [r0, #72]	@ 0x48
 8005870:	f8d0 50a4 	ldr.w	r5, [r0, #164]	@ 0xa4
 8005874:	f8d0 605c 	ldr.w	r6, [r0, #92]	@ 0x5c
 8005878:	f8d0 7014 	ldr.w	r7, [r0, #20]
 800587c:	f8c0 10a4 	str.w	r1, [r0, #164]	@ 0xa4
 8005880:	ea89 0303 	eor.w	r3, r9, r3
 8005884:	ea8c 54b4 	eor.w	r4, ip, r4, ror #22
 8005888:	ea88 5535 	eor.w	r5, r8, r5, ror #20
 800588c:	ea8b 6676 	eor.w	r6, fp, r6, ror #25
 8005890:	ea82 77f7 	eor.w	r7, r2, r7, ror #31
 8005894:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 8005898:	ea81 5133 	eor.w	r1, r1, r3, ror #20
 800589c:	f8c0 10a4 	str.w	r1, [r0, #164]	@ 0xa4
 80058a0:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 80058a4:	ea81 3174 	eor.w	r1, r1, r4, ror #13
 80058a8:	f8c0 105c 	str.w	r1, [r0, #92]	@ 0x5c
 80058ac:	ea27 2136 	bic.w	r1, r7, r6, ror #8
 80058b0:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 80058b4:	f8c0 1014 	str.w	r1, [r0, #20]
 80058b8:	ea23 31f7 	bic.w	r1, r3, r7, ror #15
 80058bc:	ea81 51f6 	eor.w	r1, r1, r6, ror #23
 80058c0:	f8c0 1094 	str.w	r1, [r0, #148]	@ 0x94
 80058c4:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 80058c8:	ea81 21f7 	eor.w	r1, r1, r7, ror #11
 80058cc:	f8d0 3030 	ldr.w	r3, [r0, #48]	@ 0x30
 80058d0:	f8d0 40b0 	ldr.w	r4, [r0, #176]	@ 0xb0
 80058d4:	f8d0 506c 	ldr.w	r5, [r0, #108]	@ 0x6c
 80058d8:	f8d0 6020 	ldr.w	r6, [r0, #32]
 80058dc:	f8d0 7078 	ldr.w	r7, [r0, #120]	@ 0x78
 80058e0:	f8c0 1048 	str.w	r1, [r0, #72]	@ 0x48
 80058e4:	ea8a 5373 	eor.w	r3, sl, r3, ror #21
 80058e8:	ea82 04b4 	eor.w	r4, r2, r4, ror #2
 80058ec:	ea89 75f5 	eor.w	r5, r9, r5, ror #31
 80058f0:	ea8e 36b6 	eor.w	r6, lr, r6, ror #14
 80058f4:	ea88 3777 	eor.w	r7, r8, r7, ror #13
 80058f8:	ea25 2174 	bic.w	r1, r5, r4, ror #9
 80058fc:	ea81 3133 	eor.w	r1, r1, r3, ror #12
 8005900:	f8c0 1078 	str.w	r1, [r0, #120]	@ 0x78
 8005904:	ea26 6135 	bic.w	r1, r6, r5, ror #24
 8005908:	ea81 0174 	eor.w	r1, r1, r4, ror #1
 800590c:	f8c0 1030 	str.w	r1, [r0, #48]	@ 0x30
 8005910:	ea27 1176 	bic.w	r1, r7, r6, ror #5
 8005914:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 8005918:	f8c0 10b0 	str.w	r1, [r0, #176]	@ 0xb0
 800591c:	ea23 51f7 	bic.w	r1, r3, r7, ror #23
 8005920:	ea81 7136 	eor.w	r1, r1, r6, ror #28
 8005924:	f8c0 106c 	str.w	r1, [r0, #108]	@ 0x6c
 8005928:	ea24 01f3 	bic.w	r1, r4, r3, ror #3
 800592c:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 8005930:	f8dd 8000 	ldr.w	r8, [sp]
 8005934:	f8d0 30c4 	ldr.w	r3, [r0, #196]	@ 0xc4
 8005938:	f8d0 4054 	ldr.w	r4, [r0, #84]	@ 0x54
 800593c:	f8d0 500c 	ldr.w	r5, [r0, #12]
 8005940:	f8d0 6088 	ldr.w	r6, [r0, #136]	@ 0x88
 8005944:	f8d0 7044 	ldr.w	r7, [r0, #68]	@ 0x44
 8005948:	f8c0 1020 	str.w	r1, [r0, #32]
 800594c:	ea8e 23b3 	eor.w	r3, lr, r3, ror #10
 8005950:	ea88 74b4 	eor.w	r4, r8, r4, ror #30
 8005954:	ea8a 7535 	eor.w	r5, sl, r5, ror #28
 8005958:	ea82 1636 	eor.w	r6, r2, r6, ror #4
 800595c:	ea89 0777 	eor.w	r7, r9, r7, ror #1
 8005960:	ea25 41f4 	bic.w	r1, r5, r4, ror #19
 8005964:	ea81 51f3 	eor.w	r1, r1, r3, ror #23
 8005968:	f8c0 1054 	str.w	r1, [r0, #84]	@ 0x54
 800596c:	ea26 01f5 	bic.w	r1, r6, r5, ror #3
 8005970:	ea81 51b4 	eor.w	r1, r1, r4, ror #22
 8005974:	f8c0 100c 	str.w	r1, [r0, #12]
 8005978:	ea27 5136 	bic.w	r1, r7, r6, ror #20
 800597c:	ea81 51f5 	eor.w	r1, r1, r5, ror #23
 8005980:	f8c0 1088 	str.w	r1, [r0, #136]	@ 0x88
 8005984:	ea23 41b7 	bic.w	r1, r3, r7, ror #18
 8005988:	ea81 11b6 	eor.w	r1, r1, r6, ror #6
 800598c:	f8c0 1044 	str.w	r1, [r0, #68]	@ 0x44
 8005990:	ea24 1133 	bic.w	r1, r4, r3, ror #4
 8005994:	ea81 51b7 	eor.w	r1, r1, r7, ror #22
 8005998:	f8d0 3060 	ldr.w	r3, [r0, #96]	@ 0x60
 800599c:	f8d0 4018 	ldr.w	r4, [r0, #24]
 80059a0:	f8d0 5098 	ldr.w	r5, [r0, #152]	@ 0x98
 80059a4:	f8d0 6028 	ldr.w	r6, [r0, #40]	@ 0x28
 80059a8:	f8d0 70ac 	ldr.w	r7, [r0, #172]	@ 0xac
 80059ac:	f8c0 10c4 	str.w	r1, [r0, #196]	@ 0xc4
 80059b0:	ea82 6373 	eor.w	r3, r2, r3, ror #25
 80059b4:	ea89 44b4 	eor.w	r4, r9, r4, ror #18
 80059b8:	ea8c 7575 	eor.w	r5, ip, r5, ror #29
 80059bc:	ea88 66f6 	eor.w	r6, r8, r6, ror #27
 80059c0:	ea8b 3737 	eor.w	r7, fp, r7, ror #12
 80059c4:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 80059c8:	ea81 5133 	eor.w	r1, r1, r3, ror #20
 80059cc:	f8c0 1028 	str.w	r1, [r0, #40]	@ 0x28
 80059d0:	ea26 0175 	bic.w	r1, r6, r5, ror #1
 80059d4:	ea81 6174 	eor.w	r1, r1, r4, ror #25
 80059d8:	f8c0 10ac 	str.w	r1, [r0, #172]	@ 0xac
 80059dc:	ea27 3176 	bic.w	r1, r7, r6, ror #13
 80059e0:	ea81 31b5 	eor.w	r1, r1, r5, ror #14
 80059e4:	f8c0 1060 	str.w	r1, [r0, #96]	@ 0x60
 80059e8:	ea23 71b7 	bic.w	r1, r3, r7, ror #30
 80059ec:	ea81 21f6 	eor.w	r1, r1, r6, ror #11
 80059f0:	f8c0 1018 	str.w	r1, [r0, #24]
 80059f4:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 80059f8:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 80059fc:	f8dd 900c 	ldr.w	r9, [sp, #12]
 8005a00:	f8d0 3000 	ldr.w	r3, [r0]
 8005a04:	f8d0 4084 	ldr.w	r4, [r0, #132]	@ 0x84
 8005a08:	6bc5      	ldr	r5, [r0, #60]	@ 0x3c
 8005a0a:	f8d0 60bc 	ldr.w	r6, [r0, #188]	@ 0xbc
 8005a0e:	6f47      	ldr	r7, [r0, #116]	@ 0x74
 8005a10:	f8c0 1098 	str.w	r1, [r0, #152]	@ 0x98
 8005a14:	ea88 0303 	eor.w	r3, r8, r3
 8005a18:	ea8a 2474 	eor.w	r4, sl, r4, ror #9
 8005a1c:	ea82 55f5 	eor.w	r5, r2, r5, ror #23
 8005a20:	ea89 46f6 	eor.w	r6, r9, r6, ror #19
 8005a24:	ea8c 1737 	eor.w	r7, ip, r7, ror #4
 8005a28:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8005a2c:	ea81 5174 	eor.w	r1, r1, r4, ror #21
 8005a30:	f8c0 1084 	str.w	r1, [r0, #132]	@ 0x84
 8005a34:	ea27 7136 	bic.w	r1, r7, r6, ror #28
 8005a38:	ea81 4175 	eor.w	r1, r1, r5, ror #17
 8005a3c:	f8c0 103c 	str.w	r1, [r0, #60]	@ 0x3c
 8005a40:	ea23 6177 	bic.w	r1, r3, r7, ror #25
 8005a44:	ea81 5176 	eor.w	r1, r1, r6, ror #21
 8005a48:	f8c0 10bc 	str.w	r1, [r0, #188]	@ 0xbc
 8005a4c:	ea24 51b3 	bic.w	r1, r4, r3, ror #22
 8005a50:	ea81 31f7 	eor.w	r1, r1, r7, ror #15
 8005a54:	f8c0 1074 	str.w	r1, [r0, #116]	@ 0x74
 8005a58:	ea25 0504 	bic.w	r5, r5, r4
 8005a5c:	9905      	ldr	r1, [sp, #20]
 8005a5e:	688c      	ldr	r4, [r1, #8]
 8005a60:	ea83 23b5 	eor.w	r3, r3, r5, ror #10
 8005a64:	ea84 0103 	eor.w	r1, r4, r3
 8005a68:	f8dd 2010 	ldr.w	r2, [sp, #16]
 8005a6c:	f8d0 3090 	ldr.w	r3, [r0, #144]	@ 0x90
 8005a70:	f8d0 404c 	ldr.w	r4, [r0, #76]	@ 0x4c
 8005a74:	f8d0 50a0 	ldr.w	r5, [r0, #160]	@ 0xa0
 8005a78:	f8d0 6058 	ldr.w	r6, [r0, #88]	@ 0x58
 8005a7c:	f8d0 7010 	ldr.w	r7, [r0, #16]
 8005a80:	f8c0 1000 	str.w	r1, [r0]
 8005a84:	ea89 0303 	eor.w	r3, r9, r3
 8005a88:	ea8e 54b4 	eor.w	r4, lr, r4, ror #22
 8005a8c:	ea88 45f5 	eor.w	r5, r8, r5, ror #19
 8005a90:	ea8a 6636 	eor.w	r6, sl, r6, ror #24
 8005a94:	ea82 77f7 	eor.w	r7, r2, r7, ror #31
 8005a98:	ea25 51f4 	bic.w	r1, r5, r4, ror #23
 8005a9c:	ea81 41f3 	eor.w	r1, r1, r3, ror #19
 8005aa0:	f8c0 10a0 	str.w	r1, [r0, #160]	@ 0xa0
 8005aa4:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8005aa8:	ea81 3134 	eor.w	r1, r1, r4, ror #12
 8005aac:	f8c0 1058 	str.w	r1, [r0, #88]	@ 0x58
 8005ab0:	ea27 2136 	bic.w	r1, r7, r6, ror #8
 8005ab4:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 8005ab8:	f8c0 1010 	str.w	r1, [r0, #16]
 8005abc:	ea23 4137 	bic.w	r1, r3, r7, ror #16
 8005ac0:	ea81 6136 	eor.w	r1, r1, r6, ror #24
 8005ac4:	f8c0 1090 	str.w	r1, [r0, #144]	@ 0x90
 8005ac8:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 8005acc:	ea81 3137 	eor.w	r1, r1, r7, ror #12
 8005ad0:	f8d0 3034 	ldr.w	r3, [r0, #52]	@ 0x34
 8005ad4:	f8d0 40b4 	ldr.w	r4, [r0, #180]	@ 0xb4
 8005ad8:	f8d0 5068 	ldr.w	r5, [r0, #104]	@ 0x68
 8005adc:	f8d0 6024 	ldr.w	r6, [r0, #36]	@ 0x24
 8005ae0:	f8d0 707c 	ldr.w	r7, [r0, #124]	@ 0x7c
 8005ae4:	f8c0 104c 	str.w	r1, [r0, #76]	@ 0x4c
 8005ae8:	ea8b 53b3 	eor.w	r3, fp, r3, ror #22
 8005aec:	ea82 0474 	eor.w	r4, r2, r4, ror #1
 8005af0:	ea89 0505 	eor.w	r5, r9, r5
 8005af4:	ea8c 36b6 	eor.w	r6, ip, r6, ror #14
 8005af8:	ea88 3737 	eor.w	r7, r8, r7, ror #12
 8005afc:	ea25 21b4 	bic.w	r1, r5, r4, ror #10
 8005b00:	ea81 3133 	eor.w	r1, r1, r3, ror #12
 8005b04:	f8c0 107c 	str.w	r1, [r0, #124]	@ 0x7c
 8005b08:	ea26 51f5 	bic.w	r1, r6, r5, ror #23
 8005b0c:	ea81 0174 	eor.w	r1, r1, r4, ror #1
 8005b10:	f8c0 1034 	str.w	r1, [r0, #52]	@ 0x34
 8005b14:	ea27 1176 	bic.w	r1, r7, r6, ror #5
 8005b18:	ea81 7135 	eor.w	r1, r1, r5, ror #28
 8005b1c:	f8c0 10b4 	str.w	r1, [r0, #180]	@ 0xb4
 8005b20:	ea23 6137 	bic.w	r1, r3, r7, ror #24
 8005b24:	ea81 7176 	eor.w	r1, r1, r6, ror #29
 8005b28:	f8c0 1068 	str.w	r1, [r0, #104]	@ 0x68
 8005b2c:	ea24 01b3 	bic.w	r1, r4, r3, ror #2
 8005b30:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 8005b34:	f8dd 8004 	ldr.w	r8, [sp, #4]
 8005b38:	f8d0 30c0 	ldr.w	r3, [r0, #192]	@ 0xc0
 8005b3c:	f8d0 4050 	ldr.w	r4, [r0, #80]	@ 0x50
 8005b40:	f8d0 5008 	ldr.w	r5, [r0, #8]
 8005b44:	f8d0 608c 	ldr.w	r6, [r0, #140]	@ 0x8c
 8005b48:	f8d0 7040 	ldr.w	r7, [r0, #64]	@ 0x40
 8005b4c:	f8c0 1024 	str.w	r1, [r0, #36]	@ 0x24
 8005b50:	ea8c 23b3 	eor.w	r3, ip, r3, ror #10
 8005b54:	ea88 74f4 	eor.w	r4, r8, r4, ror #31
 8005b58:	ea8b 7535 	eor.w	r5, fp, r5, ror #28
 8005b5c:	ea82 1636 	eor.w	r6, r2, r6, ror #4
 8005b60:	ea89 0777 	eor.w	r7, r9, r7, ror #1
 8005b64:	ea25 41f4 	bic.w	r1, r5, r4, ror #19
 8005b68:	ea81 6133 	eor.w	r1, r1, r3, ror #24
 8005b6c:	f8c0 1050 	str.w	r1, [r0, #80]	@ 0x50
 8005b70:	ea26 01b5 	bic.w	r1, r6, r5, ror #2
 8005b74:	ea81 5174 	eor.w	r1, r1, r4, ror #21
 8005b78:	f8c0 1008 	str.w	r1, [r0, #8]
 8005b7c:	ea27 5176 	bic.w	r1, r7, r6, ror #21
 8005b80:	ea81 51f5 	eor.w	r1, r1, r5, ror #23
 8005b84:	f8c0 108c 	str.w	r1, [r0, #140]	@ 0x8c
 8005b88:	ea23 4177 	bic.w	r1, r3, r7, ror #17
 8005b8c:	ea81 11b6 	eor.w	r1, r1, r6, ror #6
 8005b90:	f8c0 1040 	str.w	r1, [r0, #64]	@ 0x40
 8005b94:	ea24 1173 	bic.w	r1, r4, r3, ror #5
 8005b98:	ea81 51b7 	eor.w	r1, r1, r7, ror #22
 8005b9c:	f8d0 3064 	ldr.w	r3, [r0, #100]	@ 0x64
 8005ba0:	f8d0 401c 	ldr.w	r4, [r0, #28]
 8005ba4:	f8d0 509c 	ldr.w	r5, [r0, #156]	@ 0x9c
 8005ba8:	f8d0 602c 	ldr.w	r6, [r0, #44]	@ 0x2c
 8005bac:	f8d0 70a8 	ldr.w	r7, [r0, #168]	@ 0xa8
 8005bb0:	f8c0 10c0 	str.w	r1, [r0, #192]	@ 0xc0
 8005bb4:	ea82 6373 	eor.w	r3, r2, r3, ror #25
 8005bb8:	ea89 44b4 	eor.w	r4, r9, r4, ror #18
 8005bbc:	ea8e 7575 	eor.w	r5, lr, r5, ror #29
 8005bc0:	ea88 66f6 	eor.w	r6, r8, r6, ror #27
 8005bc4:	ea8a 27f7 	eor.w	r7, sl, r7, ror #11
 8005bc8:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 8005bcc:	ea81 5173 	eor.w	r1, r1, r3, ror #21
 8005bd0:	f8c0 102c 	str.w	r1, [r0, #44]	@ 0x2c
 8005bd4:	ea26 0175 	bic.w	r1, r6, r5, ror #1
 8005bd8:	ea81 6174 	eor.w	r1, r1, r4, ror #25
 8005bdc:	f8c0 10a8 	str.w	r1, [r0, #168]	@ 0xa8
 8005be0:	ea27 3136 	bic.w	r1, r7, r6, ror #12
 8005be4:	ea81 3175 	eor.w	r1, r1, r5, ror #13
 8005be8:	f8c0 1064 	str.w	r1, [r0, #100]	@ 0x64
 8005bec:	ea23 71b7 	bic.w	r1, r3, r7, ror #30
 8005bf0:	ea81 21b6 	eor.w	r1, r1, r6, ror #10
 8005bf4:	f8c0 101c 	str.w	r1, [r0, #28]
 8005bf8:	ea24 7173 	bic.w	r1, r4, r3, ror #29
 8005bfc:	ea81 61f7 	eor.w	r1, r1, r7, ror #27
 8005c00:	f8dd 9008 	ldr.w	r9, [sp, #8]
 8005c04:	f8d0 3004 	ldr.w	r3, [r0, #4]
 8005c08:	f8d0 4080 	ldr.w	r4, [r0, #128]	@ 0x80
 8005c0c:	6b85      	ldr	r5, [r0, #56]	@ 0x38
 8005c0e:	f8d0 60b8 	ldr.w	r6, [r0, #184]	@ 0xb8
 8005c12:	6f07      	ldr	r7, [r0, #112]	@ 0x70
 8005c14:	f8c0 109c 	str.w	r1, [r0, #156]	@ 0x9c
 8005c18:	ea88 0303 	eor.w	r3, r8, r3
 8005c1c:	ea8b 24b4 	eor.w	r4, fp, r4, ror #10
 8005c20:	ea82 55f5 	eor.w	r5, r2, r5, ror #23
 8005c24:	ea89 46b6 	eor.w	r6, r9, r6, ror #18
 8005c28:	ea8e 1777 	eor.w	r7, lr, r7, ror #5
 8005c2c:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8005c30:	ea81 5134 	eor.w	r1, r1, r4, ror #20
 8005c34:	f8c0 1080 	str.w	r1, [r0, #128]	@ 0x80
 8005c38:	ea27 7176 	bic.w	r1, r7, r6, ror #29
 8005c3c:	ea81 41b5 	eor.w	r1, r1, r5, ror #18
 8005c40:	f8c0 1038 	str.w	r1, [r0, #56]	@ 0x38
 8005c44:	ea23 6177 	bic.w	r1, r3, r7, ror #25
 8005c48:	ea81 51b6 	eor.w	r1, r1, r6, ror #22
 8005c4c:	f8c0 10b8 	str.w	r1, [r0, #184]	@ 0xb8
 8005c50:	ea24 51b3 	bic.w	r1, r4, r3, ror #22
 8005c54:	ea81 31f7 	eor.w	r1, r1, r7, ror #15
 8005c58:	f8c0 1070 	str.w	r1, [r0, #112]	@ 0x70
 8005c5c:	ea25 75f4 	bic.w	r5, r5, r4, ror #31
 8005c60:	9905      	ldr	r1, [sp, #20]
 8005c62:	68cc      	ldr	r4, [r1, #12]
 8005c64:	ea83 23f5 	eor.w	r3, r3, r5, ror #11
 8005c68:	ea84 0e03 	eor.w	lr, r4, r3
 8005c6c:	f8d0 3074 	ldr.w	r3, [r0, #116]	@ 0x74
 8005c70:	f8d0 1048 	ldr.w	r1, [r0, #72]	@ 0x48
 8005c74:	f8d0 5024 	ldr.w	r5, [r0, #36]	@ 0x24
 8005c78:	f8d0 b0c4 	ldr.w	fp, [r0, #196]	@ 0xc4
 8005c7c:	f8d0 c09c 	ldr.w	ip, [r0, #156]	@ 0x9c
 8005c80:	f8c0 e004 	str.w	lr, [r0, #4]
 8005c84:	ea83 3331 	eor.w	r3, r3, r1, ror #12
 8005c88:	ea83 43f5 	eor.w	r3, r3, r5, ror #19
 8005c8c:	ea83 133b 	eor.w	r3, r3, fp, ror #4
 8005c90:	ea83 63bc 	eor.w	r3, r3, ip, ror #26
 8005c94:	f8d0 7080 	ldr.w	r7, [r0, #128]	@ 0x80
 8005c98:	f8d0 1058 	ldr.w	r1, [r0, #88]	@ 0x58
 8005c9c:	f8d0 5030 	ldr.w	r5, [r0, #48]	@ 0x30
 8005ca0:	f8d0 b008 	ldr.w	fp, [r0, #8]
 8005ca4:	f8d0 c0ac 	ldr.w	ip, [r0, #172]	@ 0xac
 8005ca8:	ea87 5731 	eor.w	r7, r7, r1, ror #20
 8005cac:	ea87 17b5 	eor.w	r7, r7, r5, ror #6
 8005cb0:	ea87 07fb 	eor.w	r7, r7, fp, ror #3
 8005cb4:	ea87 57bc 	eor.w	r7, r7, ip, ror #22
 8005cb8:	ea4f 23b3 	mov.w	r3, r3, ror #10
 8005cbc:	ea83 5677 	eor.w	r6, r3, r7, ror #21
 8005cc0:	f8d0 4038 	ldr.w	r4, [r0, #56]	@ 0x38
 8005cc4:	f8d0 1010 	ldr.w	r1, [r0, #16]
 8005cc8:	f8d0 50b0 	ldr.w	r5, [r0, #176]	@ 0xb0
 8005ccc:	f8d0 b08c 	ldr.w	fp, [r0, #140]	@ 0x8c
 8005cd0:	f8d0 c060 	ldr.w	ip, [r0, #96]	@ 0x60
 8005cd4:	f8cd 6000 	str.w	r6, [sp]
 8005cd8:	ea84 2471 	eor.w	r4, r4, r1, ror #9
 8005cdc:	ea84 74b5 	eor.w	r4, r4, r5, ror #30
 8005ce0:	ea84 24fb 	eor.w	r4, r4, fp, ror #11
 8005ce4:	ea84 14bc 	eor.w	r4, r4, ip, ror #6
 8005ce8:	ea83 6674 	eor.w	r6, r3, r4, ror #25
 8005cec:	f8d0 30bc 	ldr.w	r3, [r0, #188]	@ 0xbc
 8005cf0:	f8d0 1094 	ldr.w	r1, [r0, #148]	@ 0x94
 8005cf4:	f8d0 5068 	ldr.w	r5, [r0, #104]	@ 0x68
 8005cf8:	f8d0 b044 	ldr.w	fp, [r0, #68]	@ 0x44
 8005cfc:	f8d0 c01c 	ldr.w	ip, [r0, #28]
 8005d00:	f8cd 600c 	str.w	r6, [sp, #12]
 8005d04:	ea83 43b1 	eor.w	r3, r3, r1, ror #18
 8005d08:	ea83 73f5 	eor.w	r3, r3, r5, ror #31
 8005d0c:	ea83 43bb 	eor.w	r3, r3, fp, ror #18
 8005d10:	ea83 037c 	eor.w	r3, r3, ip, ror #1
 8005d14:	ea83 52b7 	eor.w	r2, r3, r7, ror #22
 8005d18:	f8d0 7000 	ldr.w	r7, [r0]
 8005d1c:	f8d0 10a4 	ldr.w	r1, [r0, #164]	@ 0xa4
 8005d20:	f8d0 507c 	ldr.w	r5, [r0, #124]	@ 0x7c
 8005d24:	f8d0 b054 	ldr.w	fp, [r0, #84]	@ 0x54
 8005d28:	f8d0 c02c 	ldr.w	ip, [r0, #44]	@ 0x2c
 8005d2c:	ea87 77b1 	eor.w	r7, r7, r1, ror #30
 8005d30:	ea87 47f5 	eor.w	r7, r7, r5, ror #19
 8005d34:	ea87 67fb 	eor.w	r7, r7, fp, ror #27
 8005d38:	ea87 373c 	eor.w	r7, r7, ip, ror #12
 8005d3c:	ea87 6a34 	eor.w	sl, r7, r4, ror #24
 8005d40:	f8d0 40b8 	ldr.w	r4, [r0, #184]	@ 0xb8
 8005d44:	f8d0 1090 	ldr.w	r1, [r0, #144]	@ 0x90
 8005d48:	f8d0 506c 	ldr.w	r5, [r0, #108]	@ 0x6c
 8005d4c:	f8d0 b040 	ldr.w	fp, [r0, #64]	@ 0x40
 8005d50:	f8d0 c018 	ldr.w	ip, [r0, #24]
 8005d54:	ea84 44b1 	eor.w	r4, r4, r1, ror #18
 8005d58:	ea84 0405 	eor.w	r4, r4, r5
 8005d5c:	ea84 44fb 	eor.w	r4, r4, fp, ror #19
 8005d60:	ea84 047c 	eor.w	r4, r4, ip, ror #1
 8005d64:	ea84 0e07 	eor.w	lr, r4, r7
 8005d68:	f8d0 7084 	ldr.w	r7, [r0, #132]	@ 0x84
 8005d6c:	f8d0 105c 	ldr.w	r1, [r0, #92]	@ 0x5c
 8005d70:	f8d0 5034 	ldr.w	r5, [r0, #52]	@ 0x34
 8005d74:	f8d0 b00c 	ldr.w	fp, [r0, #12]
 8005d78:	f8d0 c0a8 	ldr.w	ip, [r0, #168]	@ 0xa8
 8005d7c:	ea87 5731 	eor.w	r7, r7, r1, ror #20
 8005d80:	ea87 17f5 	eor.w	r7, r7, r5, ror #7
 8005d84:	ea87 07fb 	eor.w	r7, r7, fp, ror #3
 8005d88:	ea87 57bc 	eor.w	r7, r7, ip, ror #22
 8005d8c:	ea4f 5777 	mov.w	r7, r7, ror #21
 8005d90:	ea87 76f4 	eor.w	r6, r7, r4, ror #31
 8005d94:	f8d0 4070 	ldr.w	r4, [r0, #112]	@ 0x70
 8005d98:	f8d0 104c 	ldr.w	r1, [r0, #76]	@ 0x4c
 8005d9c:	f8d0 5020 	ldr.w	r5, [r0, #32]
 8005da0:	f8d0 b0c0 	ldr.w	fp, [r0, #192]	@ 0xc0
 8005da4:	f8d0 c098 	ldr.w	ip, [r0, #152]	@ 0x98
 8005da8:	f8cd 6010 	str.w	r6, [sp, #16]
 8005dac:	ea84 3431 	eor.w	r4, r4, r1, ror #12
 8005db0:	ea84 44f5 	eor.w	r4, r4, r5, ror #19
 8005db4:	ea84 143b 	eor.w	r4, r4, fp, ror #4
 8005db8:	ea84 64fc 	eor.w	r4, r4, ip, ror #27
 8005dbc:	ea87 28b4 	eor.w	r8, r7, r4, ror #10
 8005dc0:	f8d0 703c 	ldr.w	r7, [r0, #60]	@ 0x3c
 8005dc4:	f8d0 1014 	ldr.w	r1, [r0, #20]
 8005dc8:	f8d0 50b4 	ldr.w	r5, [r0, #180]	@ 0xb4
 8005dcc:	f8d0 b088 	ldr.w	fp, [r0, #136]	@ 0x88
 8005dd0:	f8d0 c064 	ldr.w	ip, [r0, #100]	@ 0x64
 8005dd4:	f8cd 8004 	str.w	r8, [sp, #4]
 8005dd8:	ea87 2731 	eor.w	r7, r7, r1, ror #8
 8005ddc:	ea87 77b5 	eor.w	r7, r7, r5, ror #30
 8005de0:	ea87 27fb 	eor.w	r7, r7, fp, ror #11
 8005de4:	ea87 17bc 	eor.w	r7, r7, ip, ror #6
 8005de8:	ea4f 6777 	mov.w	r7, r7, ror #25
 8005dec:	ea87 2974 	eor.w	r9, r7, r4, ror #9
 8005df0:	f8d0 4004 	ldr.w	r4, [r0, #4]
 8005df4:	f8d0 10a0 	ldr.w	r1, [r0, #160]	@ 0xa0
 8005df8:	f8d0 5078 	ldr.w	r5, [r0, #120]	@ 0x78
 8005dfc:	f8d0 b050 	ldr.w	fp, [r0, #80]	@ 0x50
 8005e00:	f8d0 c028 	ldr.w	ip, [r0, #40]	@ 0x28
 8005e04:	f8cd 9008 	str.w	r9, [sp, #8]
 8005e08:	ea84 74f1 	eor.w	r4, r4, r1, ror #31
 8005e0c:	ea84 5435 	eor.w	r4, r4, r5, ror #20
 8005e10:	ea84 64fb 	eor.w	r4, r4, fp, ror #27
 8005e14:	ea84 347c 	eor.w	r4, r4, ip, ror #13
 8005e18:	ea84 0b07 	eor.w	fp, r4, r7
 8005e1c:	ea83 7cf4 	eor.w	ip, r3, r4, ror #31
 8005e20:	f8d0 30bc 	ldr.w	r3, [r0, #188]	@ 0xbc
 8005e24:	f8d0 4048 	ldr.w	r4, [r0, #72]	@ 0x48
 8005e28:	f8d0 5078 	ldr.w	r5, [r0, #120]	@ 0x78
 8005e2c:	f8d0 6008 	ldr.w	r6, [r0, #8]
 8005e30:	f8d0 7060 	ldr.w	r7, [r0, #96]	@ 0x60
 8005e34:	f8c0 1078 	str.w	r1, [r0, #120]	@ 0x78
 8005e38:	ea89 0303 	eor.w	r3, r9, r3
 8005e3c:	ea8c 54b4 	eor.w	r4, ip, r4, ror #22
 8005e40:	ea88 5535 	eor.w	r5, r8, r5, ror #20
 8005e44:	ea8b 6676 	eor.w	r6, fp, r6, ror #25
 8005e48:	ea82 77f7 	eor.w	r7, r2, r7, ror #31
 8005e4c:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 8005e50:	ea81 5133 	eor.w	r1, r1, r3, ror #20
 8005e54:	f8c0 1078 	str.w	r1, [r0, #120]	@ 0x78
 8005e58:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8005e5c:	ea81 3174 	eor.w	r1, r1, r4, ror #13
 8005e60:	f8c0 1008 	str.w	r1, [r0, #8]
 8005e64:	ea27 2136 	bic.w	r1, r7, r6, ror #8
 8005e68:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 8005e6c:	f8c0 1060 	str.w	r1, [r0, #96]	@ 0x60
 8005e70:	ea23 31f7 	bic.w	r1, r3, r7, ror #15
 8005e74:	ea81 51f6 	eor.w	r1, r1, r6, ror #23
 8005e78:	f8c0 10bc 	str.w	r1, [r0, #188]	@ 0xbc
 8005e7c:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 8005e80:	ea81 21f7 	eor.w	r1, r1, r7, ror #11
 8005e84:	f8d0 3084 	ldr.w	r3, [r0, #132]	@ 0x84
 8005e88:	f8d0 4010 	ldr.w	r4, [r0, #16]
 8005e8c:	f8d0 5068 	ldr.w	r5, [r0, #104]	@ 0x68
 8005e90:	f8d0 60c0 	ldr.w	r6, [r0, #192]	@ 0xc0
 8005e94:	f8d0 7028 	ldr.w	r7, [r0, #40]	@ 0x28
 8005e98:	f8c0 1048 	str.w	r1, [r0, #72]	@ 0x48
 8005e9c:	ea8a 5373 	eor.w	r3, sl, r3, ror #21
 8005ea0:	ea82 04b4 	eor.w	r4, r2, r4, ror #2
 8005ea4:	ea89 75f5 	eor.w	r5, r9, r5, ror #31
 8005ea8:	ea8e 36b6 	eor.w	r6, lr, r6, ror #14
 8005eac:	ea88 3777 	eor.w	r7, r8, r7, ror #13
 8005eb0:	ea25 2174 	bic.w	r1, r5, r4, ror #9
 8005eb4:	ea81 3133 	eor.w	r1, r1, r3, ror #12
 8005eb8:	f8c0 1028 	str.w	r1, [r0, #40]	@ 0x28
 8005ebc:	ea26 6135 	bic.w	r1, r6, r5, ror #24
 8005ec0:	ea81 0174 	eor.w	r1, r1, r4, ror #1
 8005ec4:	f8c0 1084 	str.w	r1, [r0, #132]	@ 0x84
 8005ec8:	ea27 1176 	bic.w	r1, r7, r6, ror #5
 8005ecc:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 8005ed0:	f8c0 1010 	str.w	r1, [r0, #16]
 8005ed4:	ea23 51f7 	bic.w	r1, r3, r7, ror #23
 8005ed8:	ea81 7136 	eor.w	r1, r1, r6, ror #28
 8005edc:	f8c0 1068 	str.w	r1, [r0, #104]	@ 0x68
 8005ee0:	ea24 01f3 	bic.w	r1, r4, r3, ror #3
 8005ee4:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 8005ee8:	f8dd 8000 	ldr.w	r8, [sp]
 8005eec:	f8d0 3070 	ldr.w	r3, [r0, #112]	@ 0x70
 8005ef0:	f8d0 40a4 	ldr.w	r4, [r0, #164]	@ 0xa4
 8005ef4:	f8d0 5034 	ldr.w	r5, [r0, #52]	@ 0x34
 8005ef8:	f8d0 608c 	ldr.w	r6, [r0, #140]	@ 0x8c
 8005efc:	f8d0 701c 	ldr.w	r7, [r0, #28]
 8005f00:	f8c0 10c0 	str.w	r1, [r0, #192]	@ 0xc0
 8005f04:	ea8e 23b3 	eor.w	r3, lr, r3, ror #10
 8005f08:	ea88 74b4 	eor.w	r4, r8, r4, ror #30
 8005f0c:	ea8a 7535 	eor.w	r5, sl, r5, ror #28
 8005f10:	ea82 1636 	eor.w	r6, r2, r6, ror #4
 8005f14:	ea89 0777 	eor.w	r7, r9, r7, ror #1
 8005f18:	ea25 41f4 	bic.w	r1, r5, r4, ror #19
 8005f1c:	ea81 51f3 	eor.w	r1, r1, r3, ror #23
 8005f20:	f8c0 10a4 	str.w	r1, [r0, #164]	@ 0xa4
 8005f24:	ea26 01f5 	bic.w	r1, r6, r5, ror #3
 8005f28:	ea81 51b4 	eor.w	r1, r1, r4, ror #22
 8005f2c:	f8c0 1034 	str.w	r1, [r0, #52]	@ 0x34
 8005f30:	ea27 5136 	bic.w	r1, r7, r6, ror #20
 8005f34:	ea81 51f5 	eor.w	r1, r1, r5, ror #23
 8005f38:	f8c0 108c 	str.w	r1, [r0, #140]	@ 0x8c
 8005f3c:	ea23 41b7 	bic.w	r1, r3, r7, ror #18
 8005f40:	ea81 11b6 	eor.w	r1, r1, r6, ror #6
 8005f44:	f8c0 101c 	str.w	r1, [r0, #28]
 8005f48:	ea24 1133 	bic.w	r1, r4, r3, ror #4
 8005f4c:	ea81 51b7 	eor.w	r1, r1, r7, ror #22
 8005f50:	f8d0 3038 	ldr.w	r3, [r0, #56]	@ 0x38
 8005f54:	f8d0 4094 	ldr.w	r4, [r0, #148]	@ 0x94
 8005f58:	f8d0 5024 	ldr.w	r5, [r0, #36]	@ 0x24
 8005f5c:	f8d0 6054 	ldr.w	r6, [r0, #84]	@ 0x54
 8005f60:	f8d0 70ac 	ldr.w	r7, [r0, #172]	@ 0xac
 8005f64:	f8c0 1070 	str.w	r1, [r0, #112]	@ 0x70
 8005f68:	ea82 6373 	eor.w	r3, r2, r3, ror #25
 8005f6c:	ea89 44b4 	eor.w	r4, r9, r4, ror #18
 8005f70:	ea8c 7575 	eor.w	r5, ip, r5, ror #29
 8005f74:	ea88 66f6 	eor.w	r6, r8, r6, ror #27
 8005f78:	ea8b 3737 	eor.w	r7, fp, r7, ror #12
 8005f7c:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 8005f80:	ea81 5133 	eor.w	r1, r1, r3, ror #20
 8005f84:	f8c0 1054 	str.w	r1, [r0, #84]	@ 0x54
 8005f88:	ea26 0175 	bic.w	r1, r6, r5, ror #1
 8005f8c:	ea81 6174 	eor.w	r1, r1, r4, ror #25
 8005f90:	f8c0 10ac 	str.w	r1, [r0, #172]	@ 0xac
 8005f94:	ea27 3176 	bic.w	r1, r7, r6, ror #13
 8005f98:	ea81 31b5 	eor.w	r1, r1, r5, ror #14
 8005f9c:	f8c0 1038 	str.w	r1, [r0, #56]	@ 0x38
 8005fa0:	ea23 71b7 	bic.w	r1, r3, r7, ror #30
 8005fa4:	ea81 21f6 	eor.w	r1, r1, r6, ror #11
 8005fa8:	f8c0 1094 	str.w	r1, [r0, #148]	@ 0x94
 8005fac:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 8005fb0:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 8005fb4:	f8dd 900c 	ldr.w	r9, [sp, #12]
 8005fb8:	f8d0 3000 	ldr.w	r3, [r0]
 8005fbc:	6dc4      	ldr	r4, [r0, #92]	@ 0x5c
 8005fbe:	f8d0 50b0 	ldr.w	r5, [r0, #176]	@ 0xb0
 8005fc2:	6c06      	ldr	r6, [r0, #64]	@ 0x40
 8005fc4:	f8d0 709c 	ldr.w	r7, [r0, #156]	@ 0x9c
 8005fc8:	f8c0 1024 	str.w	r1, [r0, #36]	@ 0x24
 8005fcc:	ea88 0303 	eor.w	r3, r8, r3
 8005fd0:	ea8a 2474 	eor.w	r4, sl, r4, ror #9
 8005fd4:	ea82 55f5 	eor.w	r5, r2, r5, ror #23
 8005fd8:	ea89 46f6 	eor.w	r6, r9, r6, ror #19
 8005fdc:	ea8c 1737 	eor.w	r7, ip, r7, ror #4
 8005fe0:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8005fe4:	ea81 5174 	eor.w	r1, r1, r4, ror #21
 8005fe8:	f8c0 105c 	str.w	r1, [r0, #92]	@ 0x5c
 8005fec:	ea27 7136 	bic.w	r1, r7, r6, ror #28
 8005ff0:	ea81 4175 	eor.w	r1, r1, r5, ror #17
 8005ff4:	f8c0 10b0 	str.w	r1, [r0, #176]	@ 0xb0
 8005ff8:	ea23 6177 	bic.w	r1, r3, r7, ror #25
 8005ffc:	ea81 5176 	eor.w	r1, r1, r6, ror #21
 8006000:	f8c0 1040 	str.w	r1, [r0, #64]	@ 0x40
 8006004:	ea24 51b3 	bic.w	r1, r4, r3, ror #22
 8006008:	ea81 31f7 	eor.w	r1, r1, r7, ror #15
 800600c:	f8c0 109c 	str.w	r1, [r0, #156]	@ 0x9c
 8006010:	ea25 0504 	bic.w	r5, r5, r4
 8006014:	9905      	ldr	r1, [sp, #20]
 8006016:	690c      	ldr	r4, [r1, #16]
 8006018:	ea83 23b5 	eor.w	r3, r3, r5, ror #10
 800601c:	ea84 0103 	eor.w	r1, r4, r3
 8006020:	f8dd 2010 	ldr.w	r2, [sp, #16]
 8006024:	f8d0 30b8 	ldr.w	r3, [r0, #184]	@ 0xb8
 8006028:	f8d0 404c 	ldr.w	r4, [r0, #76]	@ 0x4c
 800602c:	f8d0 507c 	ldr.w	r5, [r0, #124]	@ 0x7c
 8006030:	f8d0 600c 	ldr.w	r6, [r0, #12]
 8006034:	f8d0 7064 	ldr.w	r7, [r0, #100]	@ 0x64
 8006038:	f8c0 1000 	str.w	r1, [r0]
 800603c:	ea89 0303 	eor.w	r3, r9, r3
 8006040:	ea8e 54b4 	eor.w	r4, lr, r4, ror #22
 8006044:	ea88 45f5 	eor.w	r5, r8, r5, ror #19
 8006048:	ea8a 6636 	eor.w	r6, sl, r6, ror #24
 800604c:	ea82 77f7 	eor.w	r7, r2, r7, ror #31
 8006050:	ea25 51f4 	bic.w	r1, r5, r4, ror #23
 8006054:	ea81 41f3 	eor.w	r1, r1, r3, ror #19
 8006058:	f8c0 107c 	str.w	r1, [r0, #124]	@ 0x7c
 800605c:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8006060:	ea81 3134 	eor.w	r1, r1, r4, ror #12
 8006064:	f8c0 100c 	str.w	r1, [r0, #12]
 8006068:	ea27 2136 	bic.w	r1, r7, r6, ror #8
 800606c:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 8006070:	f8c0 1064 	str.w	r1, [r0, #100]	@ 0x64
 8006074:	ea23 4137 	bic.w	r1, r3, r7, ror #16
 8006078:	ea81 6136 	eor.w	r1, r1, r6, ror #24
 800607c:	f8c0 10b8 	str.w	r1, [r0, #184]	@ 0xb8
 8006080:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 8006084:	ea81 3137 	eor.w	r1, r1, r7, ror #12
 8006088:	f8d0 3080 	ldr.w	r3, [r0, #128]	@ 0x80
 800608c:	f8d0 4014 	ldr.w	r4, [r0, #20]
 8006090:	f8d0 506c 	ldr.w	r5, [r0, #108]	@ 0x6c
 8006094:	f8d0 60c4 	ldr.w	r6, [r0, #196]	@ 0xc4
 8006098:	f8d0 702c 	ldr.w	r7, [r0, #44]	@ 0x2c
 800609c:	f8c0 104c 	str.w	r1, [r0, #76]	@ 0x4c
 80060a0:	ea8b 53b3 	eor.w	r3, fp, r3, ror #22
 80060a4:	ea82 0474 	eor.w	r4, r2, r4, ror #1
 80060a8:	ea89 0505 	eor.w	r5, r9, r5
 80060ac:	ea8c 36b6 	eor.w	r6, ip, r6, ror #14
 80060b0:	ea88 3737 	eor.w	r7, r8, r7, ror #12
 80060b4:	ea25 21b4 	bic.w	r1, r5, r4, ror #10
 80060b8:	ea81 3133 	eor.w	r1, r1, r3, ror #12
 80060bc:	f8c0 102c 	str.w	r1, [r0, #44]	@ 0x2c
 80060c0:	ea26 51f5 	bic.w	r1, r6, r5, ror #23
 80060c4:	ea81 0174 	eor.w	r1, r1, r4, ror #1
 80060c8:	f8c0 1080 	str.w	r1, [r0, #128]	@ 0x80
 80060cc:	ea27 1176 	bic.w	r1, r7, r6, ror #5
 80060d0:	ea81 7135 	eor.w	r1, r1, r5, ror #28
 80060d4:	f8c0 1014 	str.w	r1, [r0, #20]
 80060d8:	ea23 6137 	bic.w	r1, r3, r7, ror #24
 80060dc:	ea81 7176 	eor.w	r1, r1, r6, ror #29
 80060e0:	f8c0 106c 	str.w	r1, [r0, #108]	@ 0x6c
 80060e4:	ea24 01b3 	bic.w	r1, r4, r3, ror #2
 80060e8:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 80060ec:	f8dd 8004 	ldr.w	r8, [sp, #4]
 80060f0:	f8d0 3074 	ldr.w	r3, [r0, #116]	@ 0x74
 80060f4:	f8d0 40a0 	ldr.w	r4, [r0, #160]	@ 0xa0
 80060f8:	f8d0 5030 	ldr.w	r5, [r0, #48]	@ 0x30
 80060fc:	f8d0 6088 	ldr.w	r6, [r0, #136]	@ 0x88
 8006100:	f8d0 7018 	ldr.w	r7, [r0, #24]
 8006104:	f8c0 10c4 	str.w	r1, [r0, #196]	@ 0xc4
 8006108:	ea8c 23b3 	eor.w	r3, ip, r3, ror #10
 800610c:	ea88 74f4 	eor.w	r4, r8, r4, ror #31
 8006110:	ea8b 7535 	eor.w	r5, fp, r5, ror #28
 8006114:	ea82 1636 	eor.w	r6, r2, r6, ror #4
 8006118:	ea89 0777 	eor.w	r7, r9, r7, ror #1
 800611c:	ea25 41f4 	bic.w	r1, r5, r4, ror #19
 8006120:	ea81 6133 	eor.w	r1, r1, r3, ror #24
 8006124:	f8c0 10a0 	str.w	r1, [r0, #160]	@ 0xa0
 8006128:	ea26 01b5 	bic.w	r1, r6, r5, ror #2
 800612c:	ea81 5174 	eor.w	r1, r1, r4, ror #21
 8006130:	f8c0 1030 	str.w	r1, [r0, #48]	@ 0x30
 8006134:	ea27 5176 	bic.w	r1, r7, r6, ror #21
 8006138:	ea81 51f5 	eor.w	r1, r1, r5, ror #23
 800613c:	f8c0 1088 	str.w	r1, [r0, #136]	@ 0x88
 8006140:	ea23 4177 	bic.w	r1, r3, r7, ror #17
 8006144:	ea81 11b6 	eor.w	r1, r1, r6, ror #6
 8006148:	f8c0 1018 	str.w	r1, [r0, #24]
 800614c:	ea24 1173 	bic.w	r1, r4, r3, ror #5
 8006150:	ea81 51b7 	eor.w	r1, r1, r7, ror #22
 8006154:	f8d0 303c 	ldr.w	r3, [r0, #60]	@ 0x3c
 8006158:	f8d0 4090 	ldr.w	r4, [r0, #144]	@ 0x90
 800615c:	f8d0 5020 	ldr.w	r5, [r0, #32]
 8006160:	f8d0 6050 	ldr.w	r6, [r0, #80]	@ 0x50
 8006164:	f8d0 70a8 	ldr.w	r7, [r0, #168]	@ 0xa8
 8006168:	f8c0 1074 	str.w	r1, [r0, #116]	@ 0x74
 800616c:	ea82 6373 	eor.w	r3, r2, r3, ror #25
 8006170:	ea89 44b4 	eor.w	r4, r9, r4, ror #18
 8006174:	ea8e 7575 	eor.w	r5, lr, r5, ror #29
 8006178:	ea88 66f6 	eor.w	r6, r8, r6, ror #27
 800617c:	ea8a 27f7 	eor.w	r7, sl, r7, ror #11
 8006180:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 8006184:	ea81 5173 	eor.w	r1, r1, r3, ror #21
 8006188:	f8c0 1050 	str.w	r1, [r0, #80]	@ 0x50
 800618c:	ea26 0175 	bic.w	r1, r6, r5, ror #1
 8006190:	ea81 6174 	eor.w	r1, r1, r4, ror #25
 8006194:	f8c0 10a8 	str.w	r1, [r0, #168]	@ 0xa8
 8006198:	ea27 3136 	bic.w	r1, r7, r6, ror #12
 800619c:	ea81 3175 	eor.w	r1, r1, r5, ror #13
 80061a0:	f8c0 103c 	str.w	r1, [r0, #60]	@ 0x3c
 80061a4:	ea23 71b7 	bic.w	r1, r3, r7, ror #30
 80061a8:	ea81 21b6 	eor.w	r1, r1, r6, ror #10
 80061ac:	f8c0 1090 	str.w	r1, [r0, #144]	@ 0x90
 80061b0:	ea24 7173 	bic.w	r1, r4, r3, ror #29
 80061b4:	ea81 61f7 	eor.w	r1, r1, r7, ror #27
 80061b8:	f8dd 9008 	ldr.w	r9, [sp, #8]
 80061bc:	f8d0 3004 	ldr.w	r3, [r0, #4]
 80061c0:	6d84      	ldr	r4, [r0, #88]	@ 0x58
 80061c2:	f8d0 50b4 	ldr.w	r5, [r0, #180]	@ 0xb4
 80061c6:	6c46      	ldr	r6, [r0, #68]	@ 0x44
 80061c8:	f8d0 7098 	ldr.w	r7, [r0, #152]	@ 0x98
 80061cc:	f8c0 1020 	str.w	r1, [r0, #32]
 80061d0:	ea88 0303 	eor.w	r3, r8, r3
 80061d4:	ea8b 24b4 	eor.w	r4, fp, r4, ror #10
 80061d8:	ea82 55f5 	eor.w	r5, r2, r5, ror #23
 80061dc:	ea89 46b6 	eor.w	r6, r9, r6, ror #18
 80061e0:	ea8e 1777 	eor.w	r7, lr, r7, ror #5
 80061e4:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 80061e8:	ea81 5134 	eor.w	r1, r1, r4, ror #20
 80061ec:	f8c0 1058 	str.w	r1, [r0, #88]	@ 0x58
 80061f0:	ea27 7176 	bic.w	r1, r7, r6, ror #29
 80061f4:	ea81 41b5 	eor.w	r1, r1, r5, ror #18
 80061f8:	f8c0 10b4 	str.w	r1, [r0, #180]	@ 0xb4
 80061fc:	ea23 6177 	bic.w	r1, r3, r7, ror #25
 8006200:	ea81 51b6 	eor.w	r1, r1, r6, ror #22
 8006204:	f8c0 1044 	str.w	r1, [r0, #68]	@ 0x44
 8006208:	ea24 51b3 	bic.w	r1, r4, r3, ror #22
 800620c:	ea81 31f7 	eor.w	r1, r1, r7, ror #15
 8006210:	f8c0 1098 	str.w	r1, [r0, #152]	@ 0x98
 8006214:	ea25 75f4 	bic.w	r5, r5, r4, ror #31
 8006218:	9905      	ldr	r1, [sp, #20]
 800621a:	694c      	ldr	r4, [r1, #20]
 800621c:	ea83 23f5 	eor.w	r3, r3, r5, ror #11
 8006220:	ea84 0e03 	eor.w	lr, r4, r3
 8006224:	f8d0 309c 	ldr.w	r3, [r0, #156]	@ 0x9c
 8006228:	f8d0 1048 	ldr.w	r1, [r0, #72]	@ 0x48
 800622c:	f8d0 50c4 	ldr.w	r5, [r0, #196]	@ 0xc4
 8006230:	f8d0 b070 	ldr.w	fp, [r0, #112]	@ 0x70
 8006234:	f8d0 c020 	ldr.w	ip, [r0, #32]
 8006238:	f8c0 e004 	str.w	lr, [r0, #4]
 800623c:	ea83 3331 	eor.w	r3, r3, r1, ror #12
 8006240:	ea83 43f5 	eor.w	r3, r3, r5, ror #19
 8006244:	ea83 133b 	eor.w	r3, r3, fp, ror #4
 8006248:	ea83 63bc 	eor.w	r3, r3, ip, ror #26
 800624c:	f8d0 7058 	ldr.w	r7, [r0, #88]	@ 0x58
 8006250:	f8d0 100c 	ldr.w	r1, [r0, #12]
 8006254:	f8d0 5084 	ldr.w	r5, [r0, #132]	@ 0x84
 8006258:	f8d0 b030 	ldr.w	fp, [r0, #48]	@ 0x30
 800625c:	f8d0 c0ac 	ldr.w	ip, [r0, #172]	@ 0xac
 8006260:	ea87 5731 	eor.w	r7, r7, r1, ror #20
 8006264:	ea87 17b5 	eor.w	r7, r7, r5, ror #6
 8006268:	ea87 07fb 	eor.w	r7, r7, fp, ror #3
 800626c:	ea87 57bc 	eor.w	r7, r7, ip, ror #22
 8006270:	ea4f 23b3 	mov.w	r3, r3, ror #10
 8006274:	ea83 5677 	eor.w	r6, r3, r7, ror #21
 8006278:	f8d0 40b4 	ldr.w	r4, [r0, #180]	@ 0xb4
 800627c:	f8d0 1064 	ldr.w	r1, [r0, #100]	@ 0x64
 8006280:	f8d0 5010 	ldr.w	r5, [r0, #16]
 8006284:	f8d0 b088 	ldr.w	fp, [r0, #136]	@ 0x88
 8006288:	f8d0 c038 	ldr.w	ip, [r0, #56]	@ 0x38
 800628c:	f8cd 6000 	str.w	r6, [sp]
 8006290:	ea84 2471 	eor.w	r4, r4, r1, ror #9
 8006294:	ea84 74b5 	eor.w	r4, r4, r5, ror #30
 8006298:	ea84 24fb 	eor.w	r4, r4, fp, ror #11
 800629c:	ea84 14bc 	eor.w	r4, r4, ip, ror #6
 80062a0:	ea83 6674 	eor.w	r6, r3, r4, ror #25
 80062a4:	f8d0 3040 	ldr.w	r3, [r0, #64]	@ 0x40
 80062a8:	f8d0 10bc 	ldr.w	r1, [r0, #188]	@ 0xbc
 80062ac:	f8d0 506c 	ldr.w	r5, [r0, #108]	@ 0x6c
 80062b0:	f8d0 b01c 	ldr.w	fp, [r0, #28]
 80062b4:	f8d0 c090 	ldr.w	ip, [r0, #144]	@ 0x90
 80062b8:	f8cd 600c 	str.w	r6, [sp, #12]
 80062bc:	ea83 43b1 	eor.w	r3, r3, r1, ror #18
 80062c0:	ea83 73f5 	eor.w	r3, r3, r5, ror #31
 80062c4:	ea83 43bb 	eor.w	r3, r3, fp, ror #18
 80062c8:	ea83 037c 	eor.w	r3, r3, ip, ror #1
 80062cc:	ea83 52b7 	eor.w	r2, r3, r7, ror #22
 80062d0:	f8d0 7000 	ldr.w	r7, [r0]
 80062d4:	f8d0 1078 	ldr.w	r1, [r0, #120]	@ 0x78
 80062d8:	f8d0 502c 	ldr.w	r5, [r0, #44]	@ 0x2c
 80062dc:	f8d0 b0a4 	ldr.w	fp, [r0, #164]	@ 0xa4
 80062e0:	f8d0 c050 	ldr.w	ip, [r0, #80]	@ 0x50
 80062e4:	ea87 77b1 	eor.w	r7, r7, r1, ror #30
 80062e8:	ea87 47f5 	eor.w	r7, r7, r5, ror #19
 80062ec:	ea87 67fb 	eor.w	r7, r7, fp, ror #27
 80062f0:	ea87 373c 	eor.w	r7, r7, ip, ror #12
 80062f4:	ea87 6a34 	eor.w	sl, r7, r4, ror #24
 80062f8:	f8d0 4044 	ldr.w	r4, [r0, #68]	@ 0x44
 80062fc:	f8d0 10b8 	ldr.w	r1, [r0, #184]	@ 0xb8
 8006300:	f8d0 5068 	ldr.w	r5, [r0, #104]	@ 0x68
 8006304:	f8d0 b018 	ldr.w	fp, [r0, #24]
 8006308:	f8d0 c094 	ldr.w	ip, [r0, #148]	@ 0x94
 800630c:	ea84 44b1 	eor.w	r4, r4, r1, ror #18
 8006310:	ea84 0405 	eor.w	r4, r4, r5
 8006314:	ea84 44fb 	eor.w	r4, r4, fp, ror #19
 8006318:	ea84 047c 	eor.w	r4, r4, ip, ror #1
 800631c:	ea84 0e07 	eor.w	lr, r4, r7
 8006320:	f8d0 705c 	ldr.w	r7, [r0, #92]	@ 0x5c
 8006324:	f8d0 1008 	ldr.w	r1, [r0, #8]
 8006328:	f8d0 5080 	ldr.w	r5, [r0, #128]	@ 0x80
 800632c:	f8d0 b034 	ldr.w	fp, [r0, #52]	@ 0x34
 8006330:	f8d0 c0a8 	ldr.w	ip, [r0, #168]	@ 0xa8
 8006334:	ea87 5731 	eor.w	r7, r7, r1, ror #20
 8006338:	ea87 17f5 	eor.w	r7, r7, r5, ror #7
 800633c:	ea87 07fb 	eor.w	r7, r7, fp, ror #3
 8006340:	ea87 57bc 	eor.w	r7, r7, ip, ror #22
 8006344:	ea4f 5777 	mov.w	r7, r7, ror #21
 8006348:	ea87 76f4 	eor.w	r6, r7, r4, ror #31
 800634c:	f8d0 4098 	ldr.w	r4, [r0, #152]	@ 0x98
 8006350:	f8d0 104c 	ldr.w	r1, [r0, #76]	@ 0x4c
 8006354:	f8d0 50c0 	ldr.w	r5, [r0, #192]	@ 0xc0
 8006358:	f8d0 b074 	ldr.w	fp, [r0, #116]	@ 0x74
 800635c:	f8d0 c024 	ldr.w	ip, [r0, #36]	@ 0x24
 8006360:	f8cd 6010 	str.w	r6, [sp, #16]
 8006364:	ea84 3431 	eor.w	r4, r4, r1, ror #12
 8006368:	ea84 44f5 	eor.w	r4, r4, r5, ror #19
 800636c:	ea84 143b 	eor.w	r4, r4, fp, ror #4
 8006370:	ea84 64fc 	eor.w	r4, r4, ip, ror #27
 8006374:	ea87 28b4 	eor.w	r8, r7, r4, ror #10
 8006378:	f8d0 70b0 	ldr.w	r7, [r0, #176]	@ 0xb0
 800637c:	f8d0 1060 	ldr.w	r1, [r0, #96]	@ 0x60
 8006380:	f8d0 5014 	ldr.w	r5, [r0, #20]
 8006384:	f8d0 b08c 	ldr.w	fp, [r0, #140]	@ 0x8c
 8006388:	f8d0 c03c 	ldr.w	ip, [r0, #60]	@ 0x3c
 800638c:	f8cd 8004 	str.w	r8, [sp, #4]
 8006390:	ea87 2731 	eor.w	r7, r7, r1, ror #8
 8006394:	ea87 77b5 	eor.w	r7, r7, r5, ror #30
 8006398:	ea87 27fb 	eor.w	r7, r7, fp, ror #11
 800639c:	ea87 17bc 	eor.w	r7, r7, ip, ror #6
 80063a0:	ea4f 6777 	mov.w	r7, r7, ror #25
 80063a4:	ea87 2974 	eor.w	r9, r7, r4, ror #9
 80063a8:	f8d0 4004 	ldr.w	r4, [r0, #4]
 80063ac:	f8d0 107c 	ldr.w	r1, [r0, #124]	@ 0x7c
 80063b0:	f8d0 5028 	ldr.w	r5, [r0, #40]	@ 0x28
 80063b4:	f8d0 b0a0 	ldr.w	fp, [r0, #160]	@ 0xa0
 80063b8:	f8d0 c054 	ldr.w	ip, [r0, #84]	@ 0x54
 80063bc:	f8cd 9008 	str.w	r9, [sp, #8]
 80063c0:	ea84 74f1 	eor.w	r4, r4, r1, ror #31
 80063c4:	ea84 5435 	eor.w	r4, r4, r5, ror #20
 80063c8:	ea84 64fb 	eor.w	r4, r4, fp, ror #27
 80063cc:	ea84 347c 	eor.w	r4, r4, ip, ror #13
 80063d0:	ea84 0b07 	eor.w	fp, r4, r7
 80063d4:	ea83 7cf4 	eor.w	ip, r3, r4, ror #31
 80063d8:	f8d0 3040 	ldr.w	r3, [r0, #64]	@ 0x40
 80063dc:	f8d0 4048 	ldr.w	r4, [r0, #72]	@ 0x48
 80063e0:	f8d0 5028 	ldr.w	r5, [r0, #40]	@ 0x28
 80063e4:	f8d0 6030 	ldr.w	r6, [r0, #48]	@ 0x30
 80063e8:	f8d0 7038 	ldr.w	r7, [r0, #56]	@ 0x38
 80063ec:	f8c0 1028 	str.w	r1, [r0, #40]	@ 0x28
 80063f0:	ea89 0303 	eor.w	r3, r9, r3
 80063f4:	ea8c 54b4 	eor.w	r4, ip, r4, ror #22
 80063f8:	ea88 5535 	eor.w	r5, r8, r5, ror #20
 80063fc:	ea8b 6676 	eor.w	r6, fp, r6, ror #25
 8006400:	ea82 77f7 	eor.w	r7, r2, r7, ror #31
 8006404:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 8006408:	ea81 5133 	eor.w	r1, r1, r3, ror #20
 800640c:	ea4f 71b1 	mov.w	r1, r1, ror #30
 8006410:	f8c0 1028 	str.w	r1, [r0, #40]	@ 0x28
 8006414:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8006418:	ea81 3174 	eor.w	r1, r1, r4, ror #13
 800641c:	ea4f 2171 	mov.w	r1, r1, ror #9
 8006420:	f8c0 1030 	str.w	r1, [r0, #48]	@ 0x30
 8006424:	ea27 2136 	bic.w	r1, r7, r6, ror #8
 8006428:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 800642c:	ea4f 0171 	mov.w	r1, r1, ror #1
 8006430:	f8c0 1038 	str.w	r1, [r0, #56]	@ 0x38
 8006434:	ea23 31f7 	bic.w	r1, r3, r7, ror #15
 8006438:	ea81 51f6 	eor.w	r1, r1, r6, ror #23
 800643c:	ea4f 41b1 	mov.w	r1, r1, ror #18
 8006440:	f8c0 1040 	str.w	r1, [r0, #64]	@ 0x40
 8006444:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 8006448:	ea81 21f7 	eor.w	r1, r1, r7, ror #11
 800644c:	ea4f 51b1 	mov.w	r1, r1, ror #22
 8006450:	f8d0 305c 	ldr.w	r3, [r0, #92]	@ 0x5c
 8006454:	f8d0 4064 	ldr.w	r4, [r0, #100]	@ 0x64
 8006458:	f8d0 506c 	ldr.w	r5, [r0, #108]	@ 0x6c
 800645c:	f8d0 6074 	ldr.w	r6, [r0, #116]	@ 0x74
 8006460:	f8d0 7054 	ldr.w	r7, [r0, #84]	@ 0x54
 8006464:	f8c0 1048 	str.w	r1, [r0, #72]	@ 0x48
 8006468:	ea8a 5373 	eor.w	r3, sl, r3, ror #21
 800646c:	ea82 04b4 	eor.w	r4, r2, r4, ror #2
 8006470:	ea89 75f5 	eor.w	r5, r9, r5, ror #31
 8006474:	ea8e 36b6 	eor.w	r6, lr, r6, ror #14
 8006478:	ea88 3777 	eor.w	r7, r8, r7, ror #13
 800647c:	ea25 2174 	bic.w	r1, r5, r4, ror #9
 8006480:	ea81 3133 	eor.w	r1, r1, r3, ror #12
 8006484:	ea4f 5131 	mov.w	r1, r1, ror #20
 8006488:	f8c0 1054 	str.w	r1, [r0, #84]	@ 0x54
 800648c:	ea26 6135 	bic.w	r1, r6, r5, ror #24
 8006490:	ea81 0174 	eor.w	r1, r1, r4, ror #1
 8006494:	ea4f 7131 	mov.w	r1, r1, ror #28
 8006498:	f8c0 105c 	str.w	r1, [r0, #92]	@ 0x5c
 800649c:	ea27 1176 	bic.w	r1, r7, r6, ror #5
 80064a0:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 80064a4:	ea4f 51f1 	mov.w	r1, r1, ror #23
 80064a8:	f8c0 1064 	str.w	r1, [r0, #100]	@ 0x64
 80064ac:	ea23 51f7 	bic.w	r1, r3, r7, ror #23
 80064b0:	ea81 7136 	eor.w	r1, r1, r6, ror #28
 80064b4:	f8c0 106c 	str.w	r1, [r0, #108]	@ 0x6c
 80064b8:	ea24 01f3 	bic.w	r1, r4, r3, ror #3
 80064bc:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 80064c0:	ea4f 7171 	mov.w	r1, r1, ror #29
 80064c4:	f8dd 8000 	ldr.w	r8, [sp]
 80064c8:	f8d0 3098 	ldr.w	r3, [r0, #152]	@ 0x98
 80064cc:	f8d0 4078 	ldr.w	r4, [r0, #120]	@ 0x78
 80064d0:	f8d0 5080 	ldr.w	r5, [r0, #128]	@ 0x80
 80064d4:	f8d0 6088 	ldr.w	r6, [r0, #136]	@ 0x88
 80064d8:	f8d0 7090 	ldr.w	r7, [r0, #144]	@ 0x90
 80064dc:	f8c0 1074 	str.w	r1, [r0, #116]	@ 0x74
 80064e0:	ea8e 23b3 	eor.w	r3, lr, r3, ror #10
 80064e4:	ea88 74b4 	eor.w	r4, r8, r4, ror #30
 80064e8:	ea8a 7535 	eor.w	r5, sl, r5, ror #28
 80064ec:	ea82 1636 	eor.w	r6, r2, r6, ror #4
 80064f0:	ea89 0777 	eor.w	r7, r9, r7, ror #1
 80064f4:	ea25 41f4 	bic.w	r1, r5, r4, ror #19
 80064f8:	ea81 51f3 	eor.w	r1, r1, r3, ror #23
 80064fc:	ea4f 61f1 	mov.w	r1, r1, ror #27
 8006500:	f8c0 1078 	str.w	r1, [r0, #120]	@ 0x78
 8006504:	ea26 01f5 	bic.w	r1, r6, r5, ror #3
 8006508:	ea81 51b4 	eor.w	r1, r1, r4, ror #22
 800650c:	ea4f 6131 	mov.w	r1, r1, ror #24
 8006510:	f8c0 1080 	str.w	r1, [r0, #128]	@ 0x80
 8006514:	ea27 5136 	bic.w	r1, r7, r6, ror #20
 8006518:	ea81 51f5 	eor.w	r1, r1, r5, ror #23
 800651c:	ea4f 1131 	mov.w	r1, r1, ror #4
 8006520:	f8c0 1088 	str.w	r1, [r0, #136]	@ 0x88
 8006524:	ea23 41b7 	bic.w	r1, r3, r7, ror #18
 8006528:	ea81 11b6 	eor.w	r1, r1, r6, ror #6
 800652c:	ea4f 41b1 	mov.w	r1, r1, ror #18
 8006530:	f8c0 1090 	str.w	r1, [r0, #144]	@ 0x90
 8006534:	ea24 1133 	bic.w	r1, r4, r3, ror #4
 8006538:	ea81 51b7 	eor.w	r1, r1, r7, ror #22
 800653c:	ea4f 31b1 	mov.w	r1, r1, ror #14
 8006540:	f8d0 30b4 	ldr.w	r3, [r0, #180]	@ 0xb4
 8006544:	f8d0 40bc 	ldr.w	r4, [r0, #188]	@ 0xbc
 8006548:	f8d0 50c4 	ldr.w	r5, [r0, #196]	@ 0xc4
 800654c:	f8d0 60a4 	ldr.w	r6, [r0, #164]	@ 0xa4
 8006550:	f8d0 70ac 	ldr.w	r7, [r0, #172]	@ 0xac
 8006554:	f8c0 1098 	str.w	r1, [r0, #152]	@ 0x98
 8006558:	ea82 6373 	eor.w	r3, r2, r3, ror #25
 800655c:	ea89 44b4 	eor.w	r4, r9, r4, ror #18
 8006560:	ea8c 7575 	eor.w	r5, ip, r5, ror #29
 8006564:	ea88 66f6 	eor.w	r6, r8, r6, ror #27
 8006568:	ea8b 3737 	eor.w	r7, fp, r7, ror #12
 800656c:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 8006570:	ea81 5133 	eor.w	r1, r1, r3, ror #20
 8006574:	ea4f 3171 	mov.w	r1, r1, ror #13
 8006578:	f8c0 10a4 	str.w	r1, [r0, #164]	@ 0xa4
 800657c:	ea26 0175 	bic.w	r1, r6, r5, ror #1
 8006580:	ea81 6174 	eor.w	r1, r1, r4, ror #25
 8006584:	ea4f 3131 	mov.w	r1, r1, ror #12
 8006588:	f8c0 10ac 	str.w	r1, [r0, #172]	@ 0xac
 800658c:	ea27 3176 	bic.w	r1, r7, r6, ror #13
 8006590:	ea81 31b5 	eor.w	r1, r1, r5, ror #14
 8006594:	ea4f 71f1 	mov.w	r1, r1, ror #31
 8006598:	f8c0 10b4 	str.w	r1, [r0, #180]	@ 0xb4
 800659c:	ea23 71b7 	bic.w	r1, r3, r7, ror #30
 80065a0:	ea81 21f6 	eor.w	r1, r1, r6, ror #11
 80065a4:	ea4f 0171 	mov.w	r1, r1, ror #1
 80065a8:	f8c0 10bc 	str.w	r1, [r0, #188]	@ 0xbc
 80065ac:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 80065b0:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 80065b4:	ea4f 1171 	mov.w	r1, r1, ror #5
 80065b8:	f8dd 900c 	ldr.w	r9, [sp, #12]
 80065bc:	f8d0 3000 	ldr.w	r3, [r0]
 80065c0:	6884      	ldr	r4, [r0, #8]
 80065c2:	6905      	ldr	r5, [r0, #16]
 80065c4:	6986      	ldr	r6, [r0, #24]
 80065c6:	6a07      	ldr	r7, [r0, #32]
 80065c8:	f8c0 10c4 	str.w	r1, [r0, #196]	@ 0xc4
 80065cc:	ea88 0303 	eor.w	r3, r8, r3
 80065d0:	ea8a 2474 	eor.w	r4, sl, r4, ror #9
 80065d4:	ea82 55f5 	eor.w	r5, r2, r5, ror #23
 80065d8:	ea89 46f6 	eor.w	r6, r9, r6, ror #19
 80065dc:	ea8c 1737 	eor.w	r7, ip, r7, ror #4
 80065e0:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 80065e4:	ea81 5174 	eor.w	r1, r1, r4, ror #21
 80065e8:	ea4f 5171 	mov.w	r1, r1, ror #21
 80065ec:	f8c0 1008 	str.w	r1, [r0, #8]
 80065f0:	ea27 7136 	bic.w	r1, r7, r6, ror #28
 80065f4:	ea81 4175 	eor.w	r1, r1, r5, ror #17
 80065f8:	ea4f 6171 	mov.w	r1, r1, ror #25
 80065fc:	f8c0 1010 	str.w	r1, [r0, #16]
 8006600:	ea23 6177 	bic.w	r1, r3, r7, ror #25
 8006604:	ea81 5176 	eor.w	r1, r1, r6, ror #21
 8006608:	f8c0 1018 	str.w	r1, [r0, #24]
 800660c:	ea24 51b3 	bic.w	r1, r4, r3, ror #22
 8006610:	ea81 31f7 	eor.w	r1, r1, r7, ror #15
 8006614:	ea4f 21b1 	mov.w	r1, r1, ror #10
 8006618:	f8c0 1020 	str.w	r1, [r0, #32]
 800661c:	ea25 0504 	bic.w	r5, r5, r4
 8006620:	9905      	ldr	r1, [sp, #20]
 8006622:	698c      	ldr	r4, [r1, #24]
 8006624:	ea83 23b5 	eor.w	r3, r3, r5, ror #10
 8006628:	ea84 0103 	eor.w	r1, r4, r3
 800662c:	f8dd 2010 	ldr.w	r2, [sp, #16]
 8006630:	f8d0 3044 	ldr.w	r3, [r0, #68]	@ 0x44
 8006634:	f8d0 404c 	ldr.w	r4, [r0, #76]	@ 0x4c
 8006638:	f8d0 502c 	ldr.w	r5, [r0, #44]	@ 0x2c
 800663c:	f8d0 6034 	ldr.w	r6, [r0, #52]	@ 0x34
 8006640:	f8d0 703c 	ldr.w	r7, [r0, #60]	@ 0x3c
 8006644:	f8c0 1000 	str.w	r1, [r0]
 8006648:	ea89 0303 	eor.w	r3, r9, r3
 800664c:	ea8e 54b4 	eor.w	r4, lr, r4, ror #22
 8006650:	ea88 45f5 	eor.w	r5, r8, r5, ror #19
 8006654:	ea8a 6636 	eor.w	r6, sl, r6, ror #24
 8006658:	ea82 77f7 	eor.w	r7, r2, r7, ror #31
 800665c:	ea25 51f4 	bic.w	r1, r5, r4, ror #23
 8006660:	ea81 41f3 	eor.w	r1, r1, r3, ror #19
 8006664:	ea4f 71f1 	mov.w	r1, r1, ror #31
 8006668:	f8c0 102c 	str.w	r1, [r0, #44]	@ 0x2c
 800666c:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8006670:	ea81 3134 	eor.w	r1, r1, r4, ror #12
 8006674:	ea4f 21b1 	mov.w	r1, r1, ror #10
 8006678:	f8c0 1034 	str.w	r1, [r0, #52]	@ 0x34
 800667c:	ea27 2136 	bic.w	r1, r7, r6, ror #8
 8006680:	ea81 7175 	eor.w	r1, r1, r5, ror #29
 8006684:	ea4f 01b1 	mov.w	r1, r1, ror #2
 8006688:	f8c0 103c 	str.w	r1, [r0, #60]	@ 0x3c
 800668c:	ea23 4137 	bic.w	r1, r3, r7, ror #16
 8006690:	ea81 6136 	eor.w	r1, r1, r6, ror #24
 8006694:	ea4f 41b1 	mov.w	r1, r1, ror #18
 8006698:	f8c0 1044 	str.w	r1, [r0, #68]	@ 0x44
 800669c:	ea24 7133 	bic.w	r1, r4, r3, ror #28
 80066a0:	ea81 3137 	eor.w	r1, r1, r7, ror #12
 80066a4:	ea4f 51b1 	mov.w	r1, r1, ror #22
 80066a8:	f8d0 3058 	ldr.w	r3, [r0, #88]	@ 0x58
 80066ac:	f8d0 4060 	ldr.w	r4, [r0, #96]	@ 0x60
 80066b0:	f8d0 5068 	ldr.w	r5, [r0, #104]	@ 0x68
 80066b4:	f8d0 6070 	ldr.w	r6, [r0, #112]	@ 0x70
 80066b8:	f8d0 7050 	ldr.w	r7, [r0, #80]	@ 0x50
 80066bc:	f8c0 104c 	str.w	r1, [r0, #76]	@ 0x4c
 80066c0:	ea8b 53b3 	eor.w	r3, fp, r3, ror #22
 80066c4:	ea82 0474 	eor.w	r4, r2, r4, ror #1
 80066c8:	ea89 0505 	eor.w	r5, r9, r5
 80066cc:	ea8c 36b6 	eor.w	r6, ip, r6, ror #14
 80066d0:	ea88 3737 	eor.w	r7, r8, r7, ror #12
 80066d4:	ea25 21b4 	bic.w	r1, r5, r4, ror #10
 80066d8:	ea81 3133 	eor.w	r1, r1, r3, ror #12
 80066dc:	ea4f 41f1 	mov.w	r1, r1, ror #19
 80066e0:	f8c0 1050 	str.w	r1, [r0, #80]	@ 0x50
 80066e4:	ea26 51f5 	bic.w	r1, r6, r5, ror #23
 80066e8:	ea81 0174 	eor.w	r1, r1, r4, ror #1
 80066ec:	ea4f 7131 	mov.w	r1, r1, ror #28
 80066f0:	f8c0 1058 	str.w	r1, [r0, #88]	@ 0x58
 80066f4:	ea27 1176 	bic.w	r1, r7, r6, ror #5
 80066f8:	ea81 7135 	eor.w	r1, r1, r5, ror #28
 80066fc:	ea4f 51f1 	mov.w	r1, r1, ror #23
 8006700:	f8c0 1060 	str.w	r1, [r0, #96]	@ 0x60
 8006704:	ea23 6137 	bic.w	r1, r3, r7, ror #24
 8006708:	ea81 7176 	eor.w	r1, r1, r6, ror #29
 800670c:	ea4f 71f1 	mov.w	r1, r1, ror #31
 8006710:	f8c0 1068 	str.w	r1, [r0, #104]	@ 0x68
 8006714:	ea24 01b3 	bic.w	r1, r4, r3, ror #2
 8006718:	ea81 61b7 	eor.w	r1, r1, r7, ror #26
 800671c:	ea4f 7171 	mov.w	r1, r1, ror #29
 8006720:	f8dd 8004 	ldr.w	r8, [sp, #4]
 8006724:	f8d0 309c 	ldr.w	r3, [r0, #156]	@ 0x9c
 8006728:	f8d0 407c 	ldr.w	r4, [r0, #124]	@ 0x7c
 800672c:	f8d0 5084 	ldr.w	r5, [r0, #132]	@ 0x84
 8006730:	f8d0 608c 	ldr.w	r6, [r0, #140]	@ 0x8c
 8006734:	f8d0 7094 	ldr.w	r7, [r0, #148]	@ 0x94
 8006738:	f8c0 1070 	str.w	r1, [r0, #112]	@ 0x70
 800673c:	ea8c 23b3 	eor.w	r3, ip, r3, ror #10
 8006740:	ea88 74f4 	eor.w	r4, r8, r4, ror #31
 8006744:	ea8b 7535 	eor.w	r5, fp, r5, ror #28
 8006748:	ea82 1636 	eor.w	r6, r2, r6, ror #4
 800674c:	ea89 0777 	eor.w	r7, r9, r7, ror #1
 8006750:	ea25 41f4 	bic.w	r1, r5, r4, ror #19
 8006754:	ea81 6133 	eor.w	r1, r1, r3, ror #24
 8006758:	ea4f 61f1 	mov.w	r1, r1, ror #27
 800675c:	f8c0 107c 	str.w	r1, [r0, #124]	@ 0x7c
 8006760:	ea26 01b5 	bic.w	r1, r6, r5, ror #2
 8006764:	ea81 5174 	eor.w	r1, r1, r4, ror #21
 8006768:	ea4f 6171 	mov.w	r1, r1, ror #25
 800676c:	f8c0 1084 	str.w	r1, [r0, #132]	@ 0x84
 8006770:	ea27 5176 	bic.w	r1, r7, r6, ror #21
 8006774:	ea81 51f5 	eor.w	r1, r1, r5, ror #23
 8006778:	ea4f 1131 	mov.w	r1, r1, ror #4
 800677c:	f8c0 108c 	str.w	r1, [r0, #140]	@ 0x8c
 8006780:	ea23 4177 	bic.w	r1, r3, r7, ror #17
 8006784:	ea81 11b6 	eor.w	r1, r1, r6, ror #6
 8006788:	ea4f 41f1 	mov.w	r1, r1, ror #19
 800678c:	f8c0 1094 	str.w	r1, [r0, #148]	@ 0x94
 8006790:	ea24 1173 	bic.w	r1, r4, r3, ror #5
 8006794:	ea81 51b7 	eor.w	r1, r1, r7, ror #22
 8006798:	ea4f 31b1 	mov.w	r1, r1, ror #14
 800679c:	f8d0 30b0 	ldr.w	r3, [r0, #176]	@ 0xb0
 80067a0:	f8d0 40b8 	ldr.w	r4, [r0, #184]	@ 0xb8
 80067a4:	f8d0 50c0 	ldr.w	r5, [r0, #192]	@ 0xc0
 80067a8:	f8d0 60a0 	ldr.w	r6, [r0, #160]	@ 0xa0
 80067ac:	f8d0 70a8 	ldr.w	r7, [r0, #168]	@ 0xa8
 80067b0:	f8c0 109c 	str.w	r1, [r0, #156]	@ 0x9c
 80067b4:	ea82 6373 	eor.w	r3, r2, r3, ror #25
 80067b8:	ea89 44b4 	eor.w	r4, r9, r4, ror #18
 80067bc:	ea8e 7575 	eor.w	r5, lr, r5, ror #29
 80067c0:	ea88 66f6 	eor.w	r6, r8, r6, ror #27
 80067c4:	ea8a 27f7 	eor.w	r7, sl, r7, ror #11
 80067c8:	ea25 6134 	bic.w	r1, r5, r4, ror #24
 80067cc:	ea81 5173 	eor.w	r1, r1, r3, ror #21
 80067d0:	ea4f 3131 	mov.w	r1, r1, ror #12
 80067d4:	f8c0 10a0 	str.w	r1, [r0, #160]	@ 0xa0
 80067d8:	ea26 0175 	bic.w	r1, r6, r5, ror #1
 80067dc:	ea81 6174 	eor.w	r1, r1, r4, ror #25
 80067e0:	ea4f 21f1 	mov.w	r1, r1, ror #11
 80067e4:	f8c0 10a8 	str.w	r1, [r0, #168]	@ 0xa8
 80067e8:	ea27 3136 	bic.w	r1, r7, r6, ror #12
 80067ec:	ea81 3175 	eor.w	r1, r1, r5, ror #13
 80067f0:	ea4f 71f1 	mov.w	r1, r1, ror #31
 80067f4:	f8c0 10b0 	str.w	r1, [r0, #176]	@ 0xb0
 80067f8:	ea23 71b7 	bic.w	r1, r3, r7, ror #30
 80067fc:	ea81 21b6 	eor.w	r1, r1, r6, ror #10
 8006800:	ea4f 0171 	mov.w	r1, r1, ror #1
 8006804:	f8c0 10b8 	str.w	r1, [r0, #184]	@ 0xb8
 8006808:	ea24 7173 	bic.w	r1, r4, r3, ror #29
 800680c:	ea81 61f7 	eor.w	r1, r1, r7, ror #27
 8006810:	ea4f 1131 	mov.w	r1, r1, ror #4
 8006814:	f8dd 9008 	ldr.w	r9, [sp, #8]
 8006818:	f8d0 3004 	ldr.w	r3, [r0, #4]
 800681c:	68c4      	ldr	r4, [r0, #12]
 800681e:	6945      	ldr	r5, [r0, #20]
 8006820:	69c6      	ldr	r6, [r0, #28]
 8006822:	6a47      	ldr	r7, [r0, #36]	@ 0x24
 8006824:	f8c0 10c0 	str.w	r1, [r0, #192]	@ 0xc0
 8006828:	ea88 0303 	eor.w	r3, r8, r3
 800682c:	ea8b 24b4 	eor.w	r4, fp, r4, ror #10
 8006830:	ea82 55f5 	eor.w	r5, r2, r5, ror #23
 8006834:	ea89 46b6 	eor.w	r6, r9, r6, ror #18
 8006838:	ea8e 1777 	eor.w	r7, lr, r7, ror #5
 800683c:	ea26 5175 	bic.w	r1, r6, r5, ror #21
 8006840:	ea81 5134 	eor.w	r1, r1, r4, ror #20
 8006844:	ea4f 51b1 	mov.w	r1, r1, ror #22
 8006848:	f8c0 100c 	str.w	r1, [r0, #12]
 800684c:	ea27 7176 	bic.w	r1, r7, r6, ror #29
 8006850:	ea81 41b5 	eor.w	r1, r1, r5, ror #18
 8006854:	ea4f 6171 	mov.w	r1, r1, ror #25
 8006858:	f8c0 1014 	str.w	r1, [r0, #20]
 800685c:	ea23 6177 	bic.w	r1, r3, r7, ror #25
 8006860:	ea81 51b6 	eor.w	r1, r1, r6, ror #22
 8006864:	f8c0 101c 	str.w	r1, [r0, #28]
 8006868:	ea24 51b3 	bic.w	r1, r4, r3, ror #22
 800686c:	ea81 31f7 	eor.w	r1, r1, r7, ror #15
 8006870:	ea4f 21b1 	mov.w	r1, r1, ror #10
 8006874:	f8c0 1024 	str.w	r1, [r0, #36]	@ 0x24
 8006878:	ea25 75f4 	bic.w	r5, r5, r4, ror #31
 800687c:	9905      	ldr	r1, [sp, #20]
 800687e:	69cc      	ldr	r4, [r1, #28]
 8006880:	f851 7f20 	ldr.w	r7, [r1, #32]!
 8006884:	9105      	str	r1, [sp, #20]
 8006886:	2fff      	cmp	r7, #255	@ 0xff
 8006888:	ea83 23f5 	eor.w	r3, r3, r5, ror #11
 800688c:	ea84 0103 	eor.w	r1, r4, r3
 8006890:	f8c0 1004 	str.w	r1, [r0, #4]
 8006894:	b006      	add	sp, #24
 8006896:	e8bd 9ff0 	ldmia.w	sp!, {r4, r5, r6, r7, r8, r9, sl, fp, ip, pc}
 800689a:	bf00      	nop

