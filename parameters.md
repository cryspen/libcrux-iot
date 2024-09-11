# Parameter Selection

## Algorithm Parameters

| Algorithm | Key Size | Debug / Release | Stack Size (key_gen) | Stack Size (sign/encaps) | Stack Size (verify/decaps) | Binary Size (amd64) |
|:--------- | --------:|:--------------- | --------------------:| ------------------------:| --------------------------:| -------------------:|
| ML-KEM    |      512 | Debug           |               169938 |                   188110 |                     188094 |            10528024 |
| ML-KEM    |      513 | Release         |                17128 |                      560 |                       6376 |              869416 |
| ML-KEM    |      768 | Debug           |               208458 |                   222646 |                     222630 |            10526984 |
| ML-KEM    |      768 | Release         |                25472 |                      560 |                       9792 |              852856 |
| ML-KEM    |     1024 | Debug           |               254850 |                   264286 |                     264302 |            10527200 |
| ML-KEM    |     1024 | Release         |                33512 |                      560 |                      13304 |              865224 |
| ML-DSA    |       44 | Debug           |               356465 |                   584365 |                     361070 |             6537472 |
| ML-DSA    |       44 | Release         |                 5496 |                     4160 |                       7560 |             1410376 |
| ML-DSA    |       65 | Debug           |               547489 |                   799813 |                     526337 |             6615864 |
| ML-DSA    |       65 | Release         |                 8280 |                     5953 |                       7608 |             1701360 |
| ML-DSA    |       87 | Debug           |               812576 |                  1086052 |                     760281 |             6742312 |
| ML-DSA    |       87 | Release         |                 8280 |                     4168 |                       4544 |             2147464 |


## Device Parameters

| Device                          | Flash | RAM   | Architecture         | Clock       |
| ------------------------------- | ----- | ----- | -------------------- | ----------- |
| Raspberry Pi 3                  | Inf   | Inf   | 64 bit arm           | Inf         |
| Raspberry Pi 4                  | Inf   | Inf   | 64 bit arm           | Inf         |
| ESP32-S3                        | 8MB   | 2MB   | RISC V (which?)      | 240MHz      |
| [STM32-L4R5xx] (our Nucleo-144) | 2MB   | 640KB | Cortex-M4 32 Bit Arm | 120MHz      |
| [ESP32-C6]                      | 8MB   | 512KB | RISC-V               | 160MHz      |
| [STM32-L476RG]                  | 1MB   | 128KB | Cortex-M4 32 Bit Arm | 80MHz       |
| [nRF52840-DK]                   | 1MB   | 256KB | Cortex-M4 32 Bit Arm | 64MHz       |
| [nRF5340-DK]                    | 1MB   | 512KB | Cortex-M33           | 128 / 64MHz |
| [nRF52-DK]                      |       |       |                      |             |

[STM32-L4R5xx]: https://www.st.com/en/microcontrollers-microprocessors/stm32l4r5zi.html?rt=db&id=DB3171
[ESP32-C6]: https://www.espressif.com/en/products/socs/esp32-c6
[STM32-L476RG]: https://www.st.com/en/microcontrollers-microprocessors/stm32l476rg.html?rt=db&id=DB2196
[nRF52840-DK]: https://www.nordicsemi.com/Products/nRF52840
[nRF5340-DK]: https://www.nordicsemi.com/Products/nRF5340
[nRF52-DK]: https://www.nordicsemi.com/Products/Development-hardware/nRF52-DK
