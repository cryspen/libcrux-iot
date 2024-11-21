# `libcrux` on ESP32-C6

## Setup
You can follow these steps, replacing `--target
riscv32imc-unknown-none-elf` with `--target
riscv32imac-unknown-none-elf`:
<https://docs.esp-rs.org/no_std-training/02_2_software.html>

This means
```sh
rustup toolchain install stable --component rust-src --target riscv32imac-unknown-none-elf
```

to install the required rust build toolchain and

```sh
cargo install cargo-espflash espflash
```
for the ESP toolchain that flashes and communicates with the device.
    
## Running the example
With the device connected:
```sh
cargo run --release --bin mlkem
```
