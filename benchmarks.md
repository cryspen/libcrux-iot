# Benchmark Results

All numbers reported here refer to cycle counts.

| Device                          | Clock speed                   |
|---------------------------------|-------------------------------|
| [ESP32-S3] [^1] [^2]            | 240 MHz                       |
| [STM32-L4R5xx] (our Nucleo-144) | 4 MHz (default, up to 120MHz) |
| [ESP32-C6] [^3]                 | 160 MHz                       |
| [nRF52840-DK]                   | 64 MHz                        |
| [nRF5340-DK]                    | 128 MHz                       |
| [nRF52-DK]                      |                               |
| - nRF52832                      | 64 MHz                        |
| - nRF52810                      | 64 MHz                        |

## ML-KEM

### ML-KEM 512

| Device                          | KeyGen[Debug] | KeyGen[Release] | Encaps[Debug] | Encaps[Release] | Decaps[Debug] | Decaps[Release] |
|---------------------------------|---------------|-----------------|---------------|-----------------|---------------|-----------------|
| Raspberry Pi 3                  |               |                 |               |                 |               |                 |
| Raspberry Pi 4                  |               |                 |               |                 |               |                 |
| [ESP32-S3] [^1] [^2]            |               |                 |               |                 |               |                 |
| [STM32-L4R5xx] (our Nucleo-144) | 4445020       | 771501          | 5044052       | 839800          | 6134089       | 839800          |
| [ESP32-C6] [^3]                 |               |                 |               |                 |               |                 |
| [nRF52840-DK]                   | 5968523       | 764636          | 6806307       | 839812          | 8316331       | 1011669         |
| [nRF5340-DK]                    |               |                 |               |                 |               |                 |
| [nRF52-DK]                      |               |                 |               |                 |               |                 |
| - nRF52832                      | 5789064       | 762595          | 6579357       | 838838          | 7998480       | 1010106         |
| - nRF52810                      | ❌ [^5]       | ❌ [^4]         | ❌ [^5]       | ❌ [^4]         | ❌ [^5]       | ❌ [^4]         |


### ML-KEM 768

| Device                          | KeyGen[Debug] | KeyGen[Release] | Encaps[Debug] | Encaps[Release] | Decaps[Debug] | Decaps[Release] |
|---------------------------------|---------------|-----------------|---------------|-----------------|---------------|-----------------|
| Raspberry Pi 3                  |               |                 |               |                 |               |                 |
| Raspberry Pi 4                  |               |                 |               |                 |               |                 |
| [ESP32-S3] [^1] [^2]            |               |                 |               |                 |               |                 |
| [STM32-L4R5xx] (our Nucleo-144) | 7085443       | 1273471         | 7996675       | 1395000         | 9421249       | 1591459         |
| [ESP32-C6] [^3]                 |               |                 |               |                 |               |                 |
| [nRF52840-DK]                   | 9315152       | 1257679         | 10418524      | 1381088         | 12319554      | 1607698         |
| [nRF5340-DK]                    |               |                 |               |                 |               |                 |
| [nRF52-DK]                      |               |                 |               |                 |               |                 |
| - nRF52832                      | 9434994       | 1276466         | 10691113      | 1401091         | 12626256      | 1630202         |
| - nRF52810                      | ❌ [^5]       | ❌ [^4]         | ❌ [^5]       | ❌ [^4]         | ❌ [^5]       | ❌ [^4]         |


### ML-KEM 1024

| Device                          | KeyGen[Debug] | KeyGen[Release] | Encaps[Debug] | Encaps[Release] | Decaps[Debug] | Decaps[Release] |
|---------------------------------|---------------|-----------------|---------------|-----------------|---------------|-----------------|
| Raspberry Pi 3                  |               |                 |               |                 |               |                 |
| Raspberry Pi 4                  |               |                 |               |                 |               |                 |
| [ESP32-S3] [^1] [^2]            |               |                 |               |                 |               |                 |
| [STM32-L4R5xx] (our Nucleo-144) | 10981246      | 1991691         | 11988292      | 2129442         | 13756274      | 2371826         |
| [ESP32-C6] [^3]                 |               |                 |               |                 |               |                 |
| [nRF52840-DK]                   | 14_910_284    | 1_959_916       | 16_318_665    | 2_103_371       | 18_830_628    | 2_391_463       |
| [nRF5340-DK]                    |               |                 |               |                 |               |                 |
| [nRF52-DK]                      |               |                 |               |                 |               |                 |
| - nRF52832                      | 14886756      | 1951395         | 16021505      | 2094650         | 18385162      | 2381655         |
| - nRF52810                      | ❌ [^5]       | ❌ [^4]         | ❌ [^5]       | ❌ [^4]         | ❌ [^5]       | ❌ [^4]         |


## ML-DSA
### ML-DSA 44

| Device                          | KeyGen[Debug] | KeyGen[Release] | Sign[Debug] | Sign[Release] | Verify[Debug] | Verify[Release] |
|---------------------------------|---------------|-----------------|-------------|---------------|---------------|-----------------|
| Raspberry Pi 3                  |               |                 |             |               |               |                 |
| Raspberry Pi 4                  |               |                 |             |               |               |                 |
| [ESP32-S3] [^1] [^2]            |               |                 |             |               |               |                 |
| [STM32-L4R5xx] (our Nucleo-144) | 19524681      | 3476142         | 28743483    | 4825636       | 20929483      | 3695919         |
| [ESP32-C6] [^3]                 |               |                 |             |               |               |                 |
| [nRF52840-DK]                   | 25565997      | 3565042         | 37809350    | 4987219       | 27441288      | 3788007         |
| [nRF5340-DK]                    |               |                 |             |               |               |                 |
| [nRF52-DK]                      |               |                 |             |               |               |                 |
| - nRF52832                      | ❌ [^5]       | ❌ [^4]         | ❌ [^5]     | ❌ [^4]       | ❌ [^5]       | ❌ [^4]         |
| - nRF52810                      |               |                 |             |               |               |                 |

### ML-DSA 65

| Device                          | KeyGen[Debug] | KeyGen[Release] | Sign[Debug] | Sign[Release] | Verify[Debug] | Verify[Release] |
|---------------------------------|---------------|-----------------|-------------|---------------|---------------|-----------------|
| Raspberry Pi 3                  |               |                 |             |               |               |                 |
| Raspberry Pi 4                  |               |                 |             |               |               |                 |
| [ESP32-S3] [^1] [^2]            |               |                 |             |               |               |                 |
| [STM32-L4R5xx] (our Nucleo-144) | 36271715      | 6382246         | 47606417    | 7981373       | 37005196      | 6501876         |
| [ESP32-C6] [^3]                 |               |                 |             |               |               |                 |
| [nRF52840-DK]                   | 47073665      | 6638977         | 62247859    | 8364565       | 48188918      | 6767475         |
| [nRF5340-DK]                    |               |                 |             |               |               |                 |
| [nRF52-DK]                      |               |                 |             |               |               |                 |
| - nRF52832                      | ❌ [^5]       | ❌ [^6]         | ❌ [^5]     | ❌ [^6]       | ❌ [^5]       | ❌ [^6]         |
| - nRF52810                      |               |                 |             |               |               |                 |


### ML-DSA 87

| Device                          | KeyGen[Debug] | KeyGen[Release] | Sign[Debug] | Sign[Release] | Verify[Debug] | Verify[Release] |
|---------------------------------|---------------|-----------------|-------------|---------------|---------------|-----------------|
| Raspberry Pi 3                  |               |                 |             |               |               |                 |
| Raspberry Pi 4                  |               |                 |             |               |               |                 |
| [ESP32-S3] [^1] [^2]            |               |                 |             |               |               |                 |
| [STM32-L4R5xx] (our Nucleo-144) | 60053867      | 10633875        | 137335754   | 21909905      | 61676143      | 10794553        |
| [ESP32-C6] [^3]                 |               |                 |             |               |               |                 |
| [nRF52840-DK]                   | ❌ [^5]       | ❌ [^4]         | ❌ [^5]     | ❌ [^4]       | ❌ [^5]       | ❌ [^4]         |
| [nRF5340-DK]                    |               |                 |             |               |               |                 |
| [nRF52-DK]                      |               |                 |             |               |               |                 |
| - nRF52832                      | ❌ [^5]       | ❌ [^6]         | ❌ [^5]     | ❌ [^6]       | ❌ [^5]       | ❌ [^6]         |
| - nRF52810                      |               |                 |             |               |               |                 |


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
