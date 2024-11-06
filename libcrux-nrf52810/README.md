# Libcrux ML-KEM / DSA on nRF52480

This setup is based on the app template found at [https://github.com/knurling-rs/app-template].

## Dependencies

#### 1. `flip-link`:

```console
$ cargo install flip-link
```

#### 2. `probe-rs`:

``` console
$ # make sure to install v0.2.0 or later
$ cargo install probe-rs --features cli
```


## Running Benchmarks

With the device attached, run
```console
$ cargo rb mlkem --release
```
for a crude benchmark of ML-KEM 1024 and 

```console
$ cargo rb mldsa_65 --release
```
for a crude benchmark of ML-DSA 65.
