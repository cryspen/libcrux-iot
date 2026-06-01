# Benchmark Results

Results captured on the reference board.

## Available Devices

| Device                                          | Clock speed                   |
|-------------------------------------------------|-------------------------------|
| [STM32-L4R5xx] (our Nucleo-144 reference board) | 4 MHz (default, up to 120MHz) |
| [ESP32-S3] [^1] [^2]                            | 240 MHz                       |
| [ESP32-C6] [^3]                                 | 160 MHz                       |
| [nRF52840-DK]                                   | 64 MHz                        |
| [nRF5340-DK]                                    | 128 MHz                       |
| [nRF52-DK]                                      |                               |
| - nRF52832                                      | 64 MHz                        |
| - nRF52810                                      | 64 MHz                        |


## Cycle Measurements

Run `DEFMT_LOG=infor cargo rrb mlkem --no-default-features -F $variant` (`$variant` in {`mlkem512`, `mlkem768`, `mlkem1024`}) in `libcrux-nucleo-l4r5zi` to reproduce:

### ML-KEM 512
```
l,0,16000000,ML-KEM Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,684710
b,r,bench_keygen,1
b,d,bench_keygen,1,684704
b,r,bench_keygen,2
b,d,bench_keygen,2,684714
b,r,bench_keygen,3
b,d,bench_keygen,3,684704
b,r,bench_keygen,4
b,d,bench_keygen,4,684704
b,r,bench_encaps,0
b,d,bench_encaps,0,733321
b,r,bench_encaps,1
b,d,bench_encaps,1,733305
b,r,bench_encaps,2
b,d,bench_encaps,2,733313
b,r,bench_encaps,3
b,d,bench_encaps,3,733305
b,r,bench_encaps,4
b,d,bench_encaps,4,733302
b,r,bench_decaps,0
b,d,bench_decaps,0,852697
b,r,bench_decaps,1
b,d,bench_decaps,1,852684
b,r,bench_decaps,2
b,d,bench_decaps,2,852689
b,r,bench_decaps,3
b,d,bench_decaps,3,852684
b,r,bench_decaps,4
b,d,bench_decaps,4,852695
Firmware exited successfully
```

### ML-KEM 768

```
l,0,16000000,ML-KEM Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,1095826
b,r,bench_keygen,1
b,d,bench_keygen,1,1095826
b,r,bench_keygen,2
b,d,bench_keygen,2,1095825
b,r,bench_keygen,3
b,d,bench_keygen,3,1095821
b,r,bench_keygen,4
b,d,bench_keygen,4,1095831
b,r,bench_encaps,0
b,d,bench_encaps,0,1193281
b,r,bench_encaps,1
b,d,bench_encaps,1,1193278
b,r,bench_encaps,2
b,d,bench_encaps,2,1193292
b,r,bench_encaps,3
b,d,bench_encaps,3,1193283
b,r,bench_encaps,4
b,d,bench_encaps,4,1193283
b,r,bench_decaps,0
b,d,bench_decaps,0,1354113
b,r,bench_decaps,1
b,d,bench_decaps,1,1354122
b,r,bench_decaps,2
b,d,bench_decaps,2,1354122
b,r,bench_decaps,3
b,d,bench_decaps,3,1354120
b,r,bench_decaps,4
b,d,bench_decaps,4,1354114
Firmware exited successfully
```

### ML-KEM 1024

```
l,0,16000000,ML-KEM Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,1706579
b,r,bench_keygen,1
b,d,bench_keygen,1,1706578
b,r,bench_keygen,2
b,d,bench_keygen,2,1706580
b,r,bench_keygen,3
b,d,bench_keygen,3,1706580
b,r,bench_keygen,4
b,d,bench_keygen,4,1706578
b,r,bench_encaps,0
b,d,bench_encaps,0,1828323
b,r,bench_encaps,1
b,d,bench_encaps,1,1828322
b,r,bench_encaps,2
b,d,bench_encaps,2,1828325
b,r,bench_encaps,3
b,d,bench_encaps,3,1828322
b,r,bench_encaps,4
b,d,bench_encaps,4,1828318
b,r,bench_decaps,0
b,d,bench_decaps,0,2028319
b,r,bench_decaps,1
b,d,bench_decaps,1,2028313
b,r,bench_decaps,2
b,d,bench_decaps,2,2028319
b,r,bench_decaps,3
b,d,bench_decaps,3,2028313
b,r,bench_decaps,4
b,d,bench_decaps,4,2028316
Firmware exited successfully
```

### ML-DSA 87

Run `DEFMT_LOG=infor cargo rrb mldsa` in `libcrux-nucleo-l4r5zi` to reproduce:

```
l,0,16000000,ML-DSA Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,7786306
b,r,bench_keygen,1
b,d,bench_keygen,1,7786306
b,r,bench_keygen,2
b,d,bench_keygen,2,7786307
b,r,bench_keygen,3
b,d,bench_keygen,3,7786307
b,r,bench_keygen,4
b,d,bench_keygen,4,7786305
b,r,bench_sign,0
b,d,bench_sign,0,13558239
b,r,bench_sign,1
b,d,bench_sign,1,13558234
b,r,bench_sign,2
b,d,bench_sign,2,13558236
b,r,bench_sign,3
b,d,bench_sign,3,13558238
b,r,bench_sign,4
b,d,bench_sign,4,13558244
b,r,bench_verify,0
b,d,bench_verify,0,7210660
b,r,bench_verify,1
b,d,bench_verify,1,7210654
b,r,bench_verify,2
b,d,bench_verify,2,7210654
b,r,bench_verify,3
b,d,bench_verify,3,7210659
b,r,bench_verify,4
b,d,bench_verify,4,7210655
Firmware exited successfully
```


## Stack usage

Results in bytes on the reference board.
Run `./measure-stacks.sh` in `libcrux-nucleo-l4r5zi` to reproduce.

```
Repository at commit: 9218c076a08d4fb9697e4e615c049a576ea78c4f
l,0,0,ML-KEM 1024 Key Generation
b,r,stack,0
b,d,stack,0,34016
Firmware exited successfully
l,0,0,ML-KEM 1024 Encapsulation
b,r,stack,0
b,d,stack,0,20104
Firmware exited successfully
l,0,0,ML-KEM 1024 Decapsulation
b,r,stack,0
b,d,stack,0,23400
Firmware exited successfully
l,0,0,ML-DSA 87 Key Generation
b,r,stack,0
b,d,stack,0,109464
Firmware exited successfully
l,0,0,ML-DSA 87 Signing
b,r,stack,0
b,d,stack,0,168192
Firmware exited successfully
l,0,0,ML-DSA 87 Verification
b,r,stack,0
b,d,stack,0,9760
Firmware exited successfully
```



[STM32-L4R5xx]: https://www.st.com/en/microcontrollers-microprocessors/stm32l4r5zi.html?rt=db&id=DB3171
[ESP32-C6]: https://www.espressif.com/en/products/socs/esp32-c6
[STM32-L476RG]: https://www.st.com/en/microcontrollers-microprocessors/stm32l476rg.html?rt=db&id=DB2196
[nRF52840-DK]: https://www.nordicsemi.com/Products/nRF52840
[nRF5340-DK]: https://www.nordicsemi.com/Products/nRF5340
[nRF52-DK]: https://www.nordicsemi.com/Products/Development-hardware/nRF52-DK
[esp32-s3]: https://www.espressif.com/en/products/socs/esp32-s3
[^1]: https://docs.espressif.com/projects/esp-idf/en/latest/esp32s3/hw-reference/esp32s3/user-guide-devkitc-1.html
[^2]: https://www.espressif.com/sites/default/files/documentation/esp32-s3-wroom-1_wroom-1u_datasheet_en.pdf
[^3]: https://www.espressif.com/sites/default/files/documentation/esp32-c6-wroom-1_wroom-1u_datasheet_en.pdf
[^4]: The benchmark crashses due to insufficient stack space.
[^5]: Core locks up.
[^6]: Benchmark binary does not fit available flash space.
