# libcrux-iot
An IoT friendly, formally verified, crypto library based on libcrux.

The `nucleo-l4r5zi` crate is based on the app template found at [https://github.com/knurling-rs/app-template].

## Dependencies

#### 1. `flip-link`:

```console
$ cargo install flip-link
```

#### 2. Install the target resp. toolchain

You need the following target toolchains installed, by board:

| Board         | Target toolchain            |
|---------------|-----------------------------|
| nucleo-L4R5ZI | `thumbv7em-none-eabihf`     |

#### 3. `probe-rs`:

``` console
$ # make sure to install v0.2.0 or later
$ cargo install probe-rs --features cli
```

## Running Benchmarks

With the device attached, run
```console
$ cargo rrb mlkem
```
for a crude benchmark of ML-KEM 1024 and 

```console
$ cargo rrb mldsa
```
for a crude benchmark of ML-DSA 87.

Other parameter sets are available behind `mldsa44/65` and
`mlkem512/768` features.
