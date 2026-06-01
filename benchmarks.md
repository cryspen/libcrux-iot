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
b,d,bench_keygen,0,690288
b,r,bench_keygen,1
b,d,bench_keygen,1,690283
b,r,bench_keygen,2
b,d,bench_keygen,2,690291
b,r,bench_keygen,3
b,d,bench_keygen,3,690283
b,r,bench_keygen,4
b,d,bench_keygen,4,690283
b,r,bench_encaps,0
b,d,bench_encaps,0,736271
b,r,bench_encaps,1
b,d,bench_encaps,1,736265
b,r,bench_encaps,2
b,d,bench_encaps,2,736279
b,r,bench_encaps,3
b,d,bench_encaps,3,736265
b,r,bench_encaps,4
b,d,bench_encaps,4,736272
b,r,bench_decaps,0
b,d,bench_decaps,0,852875
b,r,bench_decaps,1
b,d,bench_decaps,1,852884
b,r,bench_decaps,2
b,d,bench_decaps,2,852875
b,r,bench_decaps,3
b,d,bench_decaps,3,852886
b,r,bench_decaps,4
b,d,bench_decaps,4,852875
Firmware exited successfully
```

### ML-KEM 768

```
l,0,16000000,ML-KEM Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,1103357
b,r,bench_keygen,1
b,d,bench_keygen,1,1103352
b,r,bench_keygen,2
b,d,bench_keygen,2,1103351
b,r,bench_keygen,3
b,d,bench_keygen,3,1103349
b,r,bench_keygen,4
b,d,bench_keygen,4,1103360
b,r,bench_encaps,0
b,d,bench_encaps,0,1196721
b,r,bench_encaps,1
b,d,bench_encaps,1,1196718
b,r,bench_encaps,2
b,d,bench_encaps,2,1196727
b,r,bench_encaps,3
b,d,bench_encaps,3,1196724
b,r,bench_encaps,4
b,d,bench_encaps,4,1196721
b,r,bench_decaps,0
b,d,bench_decaps,0,1353702
b,r,bench_decaps,1
b,d,bench_decaps,1,1353708
b,r,bench_decaps,2
b,d,bench_decaps,2,1353705
b,r,bench_decaps,3
b,d,bench_decaps,3,1353709
b,r,bench_decaps,4
b,d,bench_decaps,4,1353709
Firmware exited successfully
```

### ML-KEM 1024

```
l,0,16000000,ML-KEM Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,1716921
b,r,bench_keygen,1
b,d,bench_keygen,1,1716923
b,r,bench_keygen,2
b,d,bench_keygen,2,1716920
b,r,bench_keygen,3
b,d,bench_keygen,3,1716922
b,r,bench_keygen,4
b,d,bench_keygen,4,1716919
b,r,bench_encaps,0
b,d,bench_encaps,0,1833626
b,r,bench_encaps,1
b,d,bench_encaps,1,1833627
b,r,bench_encaps,2
b,d,bench_encaps,2,1833630
b,r,bench_encaps,3
b,d,bench_encaps,3,1833631
b,r,bench_encaps,4
b,d,bench_encaps,4,1833629
b,r,bench_decaps,0
b,d,bench_decaps,0,2028191
b,r,bench_decaps,1
b,d,bench_decaps,1,2028196
b,r,bench_decaps,2
b,d,bench_decaps,2,2028193
b,r,bench_decaps,3
b,d,bench_decaps,3,2028196
b,r,bench_decaps,4
b,d,bench_decaps,4,2028194
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
