//! # SHA3
//!
//! This crate implements the SHA3 family of hash functions as well as
//! the SHAKE-128 and SHAKE-256 extendable output functions (XOFs).
//!
//! The crate provides "one-shot" functions for computing digests, which
//! either return freshly allocated buffers or write to externally
//! provided digest buffers (`*_ema` variants, short for External Memory
//! Allocation).
//!
//! In addition, an incremental, input-buffering interface (i.e. `init`,
//! `absorb`, `absorb_final` and `squeeze` functions) is provided for the
//! SHAKE functions.
//!
//! ## Cargo Features
//!
//! The crate provides cargo features for different, application-specific
//! uses.
//!
//! ### `full-unroll`
//!
//! This feature fully unrolls some parts of the computation of the Keccak
//! permutation, whereas without this feature these computations are broken
//! into smaller pieces. Our measurements suggest that full unrolling is
//! beneficial for reducing cycles spent on the Keccak permutation, but
//! comes at the cost of increased stack usage.
//!
//! ### `unbuffered-xof`
//!
//! This exposes an additional, unbuffered interface to the SHAKE
//! APIs. This is useful for reducing memory usage in applications where
//! inputs are always fully absorbed immediately and only outputs of
//! lengths that are multiples of `RATE` are squeezed, e.g. in ML-KEM or
//! ML-DSA.
//!
//! ### `check-secret-independence`
//!
//! This feature enables compile-time checking of secret-independence of
//! arithmetic operations using the `libcrux-secrets` crate.
//!
//! *Note*: `libcrux-secrets` provides Rust source level assurance of
//! secret-independence on common architectures, but does not give hard
//! guarantees. In particular there are platforms where `libcrux-secrets`
//! assumptions about the safety of operations like multiplication do not
//! apply, such as e.g. ARM Cortex-M3.

// Below, some arrays are explicitly converted into slices by writing `out[..]`
// instead of `out` as a workaround for https://github.com/cryspen/hax/issues/1983

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

use libcrux_secrets::{Classify, U8};

mod keccak;
mod lane;
mod state;

/// Size in bytes of a SHA3 244 digest
pub const SHA3_224_DIGEST_SIZE: usize = 28;
/// Size in bytes of a SHA3 256 digest
pub const SHA3_256_DIGEST_SIZE: usize = 32;
/// Size in bytes of a SHA3 384 digest
pub const SHA3_384_DIGEST_SIZE: usize = 48;
/// Size in bytes of a SHA3 512 digest
pub const SHA3_512_DIGEST_SIZE: usize = 64;

/// The Digest Algorithm
#[cfg_attr(not(eurydice), derive(Copy, Clone, Debug, PartialEq))]
#[repr(u32)]
pub enum Algorithm {
    /// SHA3 224
    Sha224 = 1,

    /// SHA3 256
    Sha256 = 2,

    /// SHA3 384
    Sha384 = 3,

    /// SHA3 512
    Sha512 = 4,
}

impl From<u32> for Algorithm {
    fn from(v: u32) -> Algorithm {
        match v {
            1 => Algorithm::Sha224,
            2 => Algorithm::Sha256,
            3 => Algorithm::Sha384,
            4 => Algorithm::Sha512,
            _ => panic!(),
        }
    }
}

impl From<Algorithm> for u32 {
    fn from(v: Algorithm) -> u32 {
        match v {
            Algorithm::Sha224 => 1,
            Algorithm::Sha256 => 2,
            Algorithm::Sha384 => 3,
            Algorithm::Sha512 => 4,
        }
    }
}

/// Returns the size of a digest in bytes for a given [`Algorithm`].
pub const fn digest_size(mode: Algorithm) -> usize {
    match mode {
        Algorithm::Sha224 => SHA3_224_DIGEST_SIZE,
        Algorithm::Sha256 => SHA3_256_DIGEST_SIZE,
        Algorithm::Sha384 => SHA3_384_DIGEST_SIZE,
        Algorithm::Sha512 => SHA3_512_DIGEST_SIZE,
    }
}

/// Hashes using a particular [`Algorithm`] of the SHA3 family.
///
/// # Examples
#[cfg_attr(not(feature = "check-secret-independence"), doc = r#"```rust"#)]
#[cfg_attr(feature = "check-secret-independence", doc = r#"```rust,ignore"#)]
/// use libcrux_iot_sha3::{digest_size, hash, Algorithm};
///
/// let payload = b"Kecak is a Balinese dance.";
/// let digest: [u8; digest_size(Algorithm::Sha256)] = hash(Algorithm::Sha256, payload);
/// ```
pub fn hash<const LEN: usize>(algorithm: Algorithm, payload: &[U8]) -> [U8; LEN] {
    #[cfg(not(eurydice))]
    debug_assert!(payload.len() <= u32::MAX as usize);

    let mut out = [0u8; LEN].classify();
    #[cfg(hax)]
    match algorithm {
        Algorithm::Sha224 => sha224_ema(&mut out[..], payload),
        Algorithm::Sha256 => sha256_ema(&mut out[..], payload),
        Algorithm::Sha384 => sha384_ema(&mut out[..], payload),
        Algorithm::Sha512 => sha512_ema(&mut out[..], payload),
    }
    #[cfg(not(hax))]
    match algorithm {
        Algorithm::Sha224 => sha224_ema(&mut out, payload),
        Algorithm::Sha256 => sha256_ema(&mut out, payload),
        Algorithm::Sha384 => sha384_ema(&mut out, payload),
        Algorithm::Sha512 => sha512_ema(&mut out, payload),
    }
    out
}

pub use hash as sha3;

/// Returns SHA3-224 digest of input payload.
///
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
pub fn sha224(payload: &[U8]) -> [U8; SHA3_224_DIGEST_SIZE] {
    let mut out = [0u8; 28].classify();
    #[cfg(hax)]
    sha224_ema(&mut out[..], payload);
    #[cfg(not(hax))]
    sha224_ema(&mut out, payload);
    out
}

/// Writes SHA3-224 digest of input payload to externally allocated buffer.
///
/// Preconditions
/// - `payload` is at most `u32::MAX` bytes long
/// - `digest` is exactly [`SHA3_224_DIGEST_SIZE`] bytes long
pub fn sha224_ema(digest: &mut [U8], payload: &[U8]) {
    #[cfg(not(eurydice))]
    debug_assert!(payload.len() <= u32::MAX as usize);
    #[cfg(not(eurydice))]
    debug_assert!(digest.len() == SHA3_224_DIGEST_SIZE);

    keccakx1::<144, 0x06u8>(payload, digest);
}

/// Returns SHA3-256 digest of input payload.
///
/// Preconditions
/// - `payload` is at most `u32::MAX` bytes long
pub fn sha256(data: &[U8]) -> [U8; SHA3_256_DIGEST_SIZE] {
    let mut out = [0u8; 32].classify();
    #[cfg(hax)]
    sha256_ema(&mut out[..], data);
    #[cfg(not(hax))]
    sha256_ema(&mut out, data);
    out
}

/// Writes SHA3-256 digest of input payload to externally allocated buffer.
///
/// Preconditions
/// - `payload` is at most `u32::MAX` bytes long
/// - `digest` is exactly [`SHA3_256_DIGEST_SIZE`] bytes long
pub fn sha256_ema(digest: &mut [U8], payload: &[U8]) {
    #[cfg(not(eurydice))]
    debug_assert!(payload.len() <= u32::MAX as usize);
    #[cfg(not(eurydice))]
    debug_assert!(digest.len() == SHA3_256_DIGEST_SIZE);

    keccakx1::<136, 0x06u8>(payload, digest);
}

/// Returns SHA3-384 digest of input payload.
///
/// Preconditions
/// - `payload` is at most `u32::MAX` bytes long
pub fn sha384(data: &[U8]) -> [U8; SHA3_384_DIGEST_SIZE] {
    let mut out = [0u8; 48].classify();
    #[cfg(hax)]
    sha384_ema(&mut out[..], data);
    #[cfg(not(hax))]
    sha384_ema(&mut out, data);
    out
}

/// Writes SHA3-384 digest of input payload to externally allocated buffer.
///
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
/// - `digest` is exactly [`SHA3_384_DIGEST_SIZE`] bytes long
pub fn sha384_ema(digest: &mut [U8], payload: &[U8]) {
    #[cfg(not(eurydice))]
    debug_assert!(payload.len() <= u32::MAX as usize);
    #[cfg(not(eurydice))]
    debug_assert!(digest.len() == SHA3_384_DIGEST_SIZE);

    keccakx1::<104, 0x06u8>(payload, digest);
}

/// Returns SHA3-512 digest of input payload.
///
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
pub fn sha512(data: &[U8]) -> [U8; SHA3_512_DIGEST_SIZE] {
    let mut out = [0u8; 64].classify();
    #[cfg(hax)]
    sha512_ema(&mut out[..], data);
    #[cfg(not(hax))]
    sha512_ema(&mut out, data);
    out
}

/// Writes SHA3-512 digest of input payload to externally allocated buffer.
///
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
/// - `digest` is exactly [`SHA3_512_DIGEST_SIZE`] bytes long
pub fn sha512_ema(digest: &mut [U8], payload: &[U8]) {
    #[cfg(not(eurydice))]
    debug_assert!(payload.len() <= u32::MAX as usize);
    #[cfg(not(eurydice))]
    debug_assert!(digest.len() == SHA3_512_DIGEST_SIZE);

    keccakx1::<72, 0x06u8>(payload, digest);
}

/// Returns SHAKE-128 digest of input payload.
///
/// Preconditions:
/// - `BYTES` is at most `u32::MAX as usize`
pub fn shake128<const BYTES: usize>(data: &[U8]) -> [U8; BYTES] {
    let mut out = [0u8; BYTES].classify();
    #[cfg(hax)]
    keccakx1::<168, 0x1fu8>(data, &mut out[..]);
    #[cfg(not(hax))]
    keccakx1::<168, 0x1fu8>(data, &mut out);
    out
}

/// Writes SHAKE-128 digest of input payload to externally allocated buffer.
///
/// Writes `out.len()` bytes
///
/// Preconditions:
/// - `out` is at most `u32::MAX` bytes long
pub fn shake128_ema(out: &mut [U8], data: &[U8]) {
    keccakx1::<168, 0x1fu8>(data, out);
}

/// Returns SHA3-256 digest of input payload.
///
/// Preconditions:
/// - `BYTES` is at most `u32::MAX as usize`
pub fn shake256<const BYTES: usize>(data: &[U8]) -> [U8; BYTES] {
    let mut out = [0u8; BYTES].classify();
    #[cfg(hax)]
    keccakx1::<136, 0x1fu8>(data, &mut out[..]);
    #[cfg(not(hax))]
    keccakx1::<136, 0x1fu8>(data, &mut out);
    out
}

/// Writes SHA3-256 digest of input payload to externally allocated buffer.
///
/// Writes `out.len()` bytes.
///
/// Preconditions:
/// - `out` is at most `u32::MAX` bytes long
pub fn shake256_ema(out: &mut [U8], data: &[U8]) {
    keccakx1::<136, 0x1fu8>(data, out);
}

/// Incremental API for SHAKE XOFs
pub mod incremental {
    use libcrux_secrets::U8;

    /// An unbuffered XOF state.
    #[derive(Clone, Copy)]
    #[cfg_attr(not(eurydice), derive(Debug))]
    #[cfg(feature = "unbuffered-xof")]
    pub struct UnbufferedXofState {
        pub(crate) state: crate::state::KeccakState,
    }

    use crate::keccak::KeccakXofState;
    #[cfg(feature = "unbuffered-xof")]
    use crate::keccak::{
        absorb_final, squeeze_first_block, squeeze_first_five_blocks, squeeze_first_three_blocks,
        squeeze_next_block,
    };
    mod private {
        pub trait Sealed {}

        impl Sealed for super::Shake128Xof {}
        impl Sealed for super::Shake256Xof {}
    }

    /// Input-buffering SHAKE128 state
    pub struct Shake128Xof {
        state: KeccakXofState<168>,
    }

    /// Input-buffering SHAKE256 state
    pub struct Shake256Xof {
        state: KeccakXofState<136>,
    }

    /// Interface for an input-buffering Extendable Output Function
    /// (XOF)
    pub trait Xof<const RATE: usize>: private::Sealed {
        /// Create new buffered XOF state.
        ///
        /// The internal buffer is initialized as empty.
        fn new() -> Self;

        /// Absorb bytes from `input` into the buffered XOF state.
        ///
        /// The bytes from `input` are appended to the contents of the
        /// internal buffer and the internal XOF state is then updated
        /// with `RATE` bytes from this combined input at a time. If
        /// the length of the combined input is not a multiple of
        /// `RATE`, the remainder of length `< RATE` bytes is stored
        /// in the internal buffer.
        fn absorb(&mut self, input: &[U8]);

        /// Absorb bytes from `input` into the buffered XOF state and
        /// finalize for squeezing.
        ///
        /// The bytes from `input` are appended to the contents of the
        /// internal buffer and the internal XOF state is then updated
        /// with `RATE` bytes from this combined input at a time. If
        /// the length of the combined input is not a multiple of
        /// `RATE`, the remainder of length `< RATE` bytes is appended
        /// with the appropriate delimiter and padded into a
        /// `RATE`-size block before updating the internal XOF state
        /// with this final input block.
        fn absorb_final(&mut self, input: &[U8]);

        /// Squeeze bytes from a finalized XOF state into `out`.
        ///
        /// *Caution*: Output bytes are not buffered, meaning if a
        /// first call to `squeeze` provides a number of output bytes
        /// that is not evenly divided by `RATE`, a subsequent call to
        /// `squeeze` will return bytes starting from the next block
        /// of outputs generated by the internal permutation, **not**
        /// from the remainder of bytes that were not part of the
        /// output of the previous call.
        fn squeeze(&mut self, out: &mut [U8]);
    }

    impl Xof<168> for Shake128Xof {
        fn new() -> Self {
            Self {
                state: KeccakXofState::<168>::new(),
            }
        }

        fn absorb(&mut self, input: &[U8]) {
            self.state.absorb(input);
        }

        fn absorb_final(&mut self, input: &[U8]) {
            self.state.absorb_final::<0x1fu8>(input);
        }

        fn squeeze(&mut self, out: &mut [U8]) {
            self.state.squeeze(out);
        }
    }

    impl Xof<136> for Shake256Xof {
        fn new() -> Self {
            Self {
                state: KeccakXofState::<136>::new(),
            }
        }

        fn absorb(&mut self, input: &[U8]) {
            self.state.absorb(input);
        }

        fn absorb_final(&mut self, input: &[U8]) {
            self.state.absorb_final::<0x1fu8>(input);
        }

        /// Shake256 squeeze
        fn squeeze(&mut self, out: &mut [U8]) {
            self.state.squeeze(out);
        }
    }

    /// Create a new SHAKE-128 state object.
    #[inline(always)]
    #[cfg(feature = "unbuffered-xof")]
    pub fn shake128_init() -> UnbufferedXofState {
        UnbufferedXofState {
            state: crate::state::KeccakState::new(),
        }
    }

    /// Absorb
    #[cfg(feature = "unbuffered-xof")]
    pub fn shake128_absorb_final(s: &mut UnbufferedXofState, data0: &[U8]) {
        absorb_final::<168, 0x1fu8>(&mut s.state, data0, 0, data0.len());
    }

    /// Squeeze three blocks
    #[cfg(feature = "unbuffered-xof")]
    pub fn shake128_squeeze_first_three_blocks(s: &mut UnbufferedXofState, out0: &mut [U8]) {
        squeeze_first_three_blocks::<168>(&mut s.state, out0)
    }

    /// Squeeze five blocks
    #[cfg(feature = "unbuffered-xof")]
    pub fn shake128_squeeze_first_five_blocks(s: &mut UnbufferedXofState, out0: &mut [U8]) {
        squeeze_first_five_blocks::<168>(&mut s.state, out0)
    }

    /// Squeeze another block
    #[cfg(feature = "unbuffered-xof")]
    pub fn shake128_squeeze_next_block(s: &mut UnbufferedXofState, out0: &mut [U8]) {
        squeeze_next_block::<168>(&mut s.state, out0)
    }

    /// Create a new SHAKE-256 state object.
    #[inline(always)]
    #[cfg(feature = "unbuffered-xof")]
    pub fn shake256_init() -> UnbufferedXofState {
        UnbufferedXofState {
            state: crate::state::KeccakState::new(),
        }
    }

    /// Absorb some data for SHAKE-256 for the last time
    #[cfg(feature = "unbuffered-xof")]
    pub fn shake256_absorb_final(s: &mut UnbufferedXofState, data: &[U8]) {
        absorb_final::<136, 0x1fu8>(&mut s.state, data, 0, data.len());
    }

    /// Squeeze the first SHAKE-256 block
    #[cfg(feature = "unbuffered-xof")]
    pub fn shake256_squeeze_first_block(s: &mut UnbufferedXofState, out: &mut [U8]) {
        squeeze_first_block::<136>(&s.state, out)
    }

    /// Squeeze the next SHAKE-256 block
    #[cfg(feature = "unbuffered-xof")]
    pub fn shake256_squeeze_next_block(s: &mut UnbufferedXofState, out: &mut [U8]) {
        squeeze_next_block::<136>(&mut s.state, out)
    }
}

pub(crate) fn keccakx1<const RATE: usize, const DELIM: u8>(data: &[U8], out: &mut [U8]) {
    keccak::keccak::<RATE, DELIM>(data, out)
}

#[cfg(feature = "check-secret-independence")]
trait FromLeBytes<const N: usize>: Sized {
    fn from_le_bytes(bytes: [U8; N]) -> Self;
}

#[cfg(feature = "check-secret-independence")]
trait ToLeBytes<const N: usize>: Sized {
    fn to_le_bytes(self) -> [U8; N];
}
