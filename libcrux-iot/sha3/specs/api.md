# SHA3 Spec

## EQ-01 SHA3

The SHA3 functions implement the SHA3 function,
returning the SHA3 digest according to FIPS 202 of the corresponding length
if `data.len() <= u32::MAX`.

* `sha224`
* `sha256`
* `sha384`
* `sha512`

```rust
pub fn sha224(data: &[U8]) -> [U8; SHA3_224_DIGEST_SIZE];
pub fn sha256(data: &[U8]) -> [U8; SHA3_256_DIGEST_SIZE];
pub fn sha384(data: &[U8]) -> [U8; SHA3_384_DIGEST_SIZE];
pub fn sha512(data: &[U8]) -> [U8; SHA3_512_DIGEST_SIZE];
```

### EQ-01-01 SHA3-224

SHA-224 correctness

```rust
pub fn sha224(data: &[U8]) -> [U8; SHA3_224_DIGEST_SIZE];
```

### EQ-01-02 SHA3-256

SHA-256 correctness

```rust
pub fn sha256(data: &[U8]) -> [U8; SHA3_256_DIGEST_SIZE];
```

### EQ-01-03 SHA3-384

SHA-384 correctness

```rust
pub fn sha384(data: &[U8]) -> [U8; SHA3_384_DIGEST_SIZE];
```

### EQ-01-04 SHA3-512

SHA-512 correctness

```rust
pub fn sha512(data: &[U8]) -> [U8; SHA3_512_DIGEST_SIZE];
```


## EQ-02 SHAKE

`shake128`, and `shake256` functions implement the SHAKE function,
returning the SHAKE digest of the requested length according to FIPS 202 of the
corresponding length if `data.len() <= u32::MAX`.

```rust
pub fn shake128<const BYTES: usize>(data: &[U8]) -> [U8; BYTES];
pub fn shake256<const BYTES: usize>(data: &[U8]) -> [U8; BYTES];
```

### EQ-02-01 SHAKE128

SHAKE128 correctness

```rust
pub fn shake128<const BYTES: usize>(data: &[U8]) -> [U8; BYTES];
```

### EQ-02-02 SHAKE256

SHAKE256 correctness

```rust
pub fn shake256<const BYTES: usize>(data: &[U8]) -> [U8; BYTES];
```

## EQ-03 Incremental SHAKE

The incremental SHAKE API allows absorbing input in chunks and squeezing output in
multiple calls, following the XOF (eXtensible Output Function) sponge construction
from FIPS 202.

### EQ-03-01 SHAKE-128 Incremental

Incremental SHAKE-128 interface: initialize state, absorb input in chunks,
squeeze output of any requested length per FIPS 202.

### EQ-03-02 SHAKE-256 Incremental

Incremental SHAKE-256 interface: initialize state, absorb input in chunks,
squeeze output of any requested length per FIPS 202.
