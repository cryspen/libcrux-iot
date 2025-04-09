//! # SHA3
//!
//! A SHA3 implementation with optional simd optimisations.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

mod generic_keccak;
mod portable_keccak;
mod traits;

/// A SHA3 224 Digest
pub type Sha3_224Digest = [u8; 28];

/// A SHA3 256 Digest
pub type Sha3_256Digest = [u8; 32];

/// A SHA3 384 Digest
pub type Sha3_384Digest = [u8; 48];

/// A SHA3 512 Digest
pub type Sha3_512Digest = [u8; 64];

/// The Digest Algorithm.
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

/// Returns the output size of a digest.
pub const fn digest_size(mode: Algorithm) -> usize {
    match mode {
        Algorithm::Sha224 => 28,
        Algorithm::Sha256 => 32,
        Algorithm::Sha384 => 48,
        Algorithm::Sha512 => 64,
    }
}

/// SHA3
pub fn hash<const LEN: usize>(algorithm: Algorithm, payload: &[u8]) -> [u8; LEN] {
    debug_assert!(payload.len() <= u32::MAX as usize);

    let mut out = [0u8; LEN];
    match algorithm {
        Algorithm::Sha224 => portable::sha224(&mut out, payload),
        Algorithm::Sha256 => portable::sha256(&mut out, payload),
        Algorithm::Sha384 => portable::sha384(&mut out, payload),
        Algorithm::Sha512 => portable::sha512(&mut out, payload),
    }
    out
}

/// SHA3
pub use hash as sha3;

/// SHA3 224
#[inline(always)]
pub fn sha224(data: &[u8]) -> Sha3_224Digest {
    let mut out = [0u8; 28];
    sha224_ema(&mut out, data);
    out
}

/// SHA3 224
///
/// Preconditions:
/// - `digest.len() == 28`
#[inline(always)]
pub fn sha224_ema(digest: &mut [u8], payload: &[u8]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 28);

    portable::sha224(digest, payload)
}

/// SHA3 256
#[inline(always)]
pub fn sha256(data: &[u8]) -> Sha3_256Digest {
    let mut out = [0u8; 32];
    sha256_ema(&mut out, data);
    out
}

/// SHA3 256
#[inline(always)]
pub fn sha256_ema(digest: &mut [u8], payload: &[u8]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 32);

    portable::sha256(digest, payload)
}

/// SHA3 384
#[inline(always)]
pub fn sha384(data: &[u8]) -> Sha3_384Digest {
    let mut out = [0u8; 48];
    sha384_ema(&mut out, data);
    out
}

/// SHA3 384
#[inline(always)]
pub fn sha384_ema(digest: &mut [u8], payload: &[u8]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 48);

    portable::sha384(digest, payload)
}

/// SHA3 512
#[inline(always)]
pub fn sha512(data: &[u8]) -> Sha3_512Digest {
    let mut out = [0u8; 64];
    sha512_ema(&mut out, data);
    out
}

/// SHA3 512
#[inline(always)]
pub fn sha512_ema(digest: &mut [u8], payload: &[u8]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 64);

    portable::sha512(digest, payload)
}

/// SHAKE 128
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub fn shake128<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    portable::shake128(&mut out, data);
    out
}

/// SHAKE 128
///
/// Writes `out.len()` bytes.
#[inline(always)]
pub fn shake128_ema(out: &mut [u8], data: &[u8]) {
    portable::shake128(out, data);
}

/// SHAKE 256
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub fn shake256<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    portable::shake256(&mut out, data);
    out
}

/// SHAKE 256
///
/// Writes `out.len()` bytes.
#[inline(always)]
pub fn shake256_ema(out: &mut [u8], data: &[u8]) {
    portable::shake256(out, data);
}

//  === The portable instantiation === //

/// A portable SHA3 implementation without platform dependent optimisations.
pub mod portable {
    use super::*;
    use generic_keccak::KeccakState as GenericState;

    /// The Keccak state for the incremental API.
    #[derive(Clone, Copy, Debug)]
    pub struct KeccakState {
        state: GenericState<1, [u32; 2]>,
    }

    #[inline(always)]
    fn keccakx1<const RATE: usize, const DELIM: u8>(data: &[&[u8]; 1], out: [&mut [u8]; 1]) {
        // generic_keccak::keccak_xof::<1, u64, RATE, DELIM>(data, out);
        // or
        // generic_keccak::keccak::<1, u64, RATE, DELIM>(data, out);
        // or
        generic_keccak::keccak::<RATE, DELIM>(data, out);
    }

    /// A portable SHA3 224 implementation.
    #[inline(always)]
    pub fn sha224(digest: &mut [u8], data: &[u8]) {
        keccakx1::<144, 0x06u8>(&[data], [digest]);
    }

    /// A portable SHA3 256 implementation.
    #[inline(never)]
    pub fn sha256(digest: &mut [u8], data: &[u8]) {
        keccakx1::<136, 0x06u8>(&[data], [digest]);
    }

    /// A portable SHA3 384 implementation.
    #[inline(always)]
    pub fn sha384(digest: &mut [u8], data: &[u8]) {
        keccakx1::<104, 0x06u8>(&[data], [digest]);
    }

    /// A portable SHA3 512 implementation.
    #[inline(never)]
    pub fn sha512(digest: &mut [u8], data: &[u8]) {
        keccakx1::<72, 0x06u8>(&[data], [digest]);
    }

    /// A portable SHAKE128 implementation.
    #[inline(always)]
    pub fn shake128(digest: &mut [u8], data: &[u8]) {
        keccakx1::<168, 0x1fu8>(&[data], [digest]);
    }

    /// A portable SHAKE256 implementation.
    #[inline(never)]
    pub fn shake256(digest: &mut [u8], data: &[u8]) {
        keccakx1::<136, 0x1fu8>(&[data], [digest]);
    }

    /// An incremental API for SHAKE
    pub mod incremental {
        use generic_keccak::{
            absorb_final, squeeze_first_block, squeeze_first_five_blocks,
            squeeze_first_three_blocks, squeeze_next_block, KeccakXofState,
        };
        mod private {
            pub trait Sealed {}

            impl Sealed for super::Shake128Xof {}
            impl Sealed for super::Shake256Xof {}
        }
        use super::*;

        /// SHAKE128 Xof state
        pub struct Shake128Xof {
            state: KeccakXofState<168>,
        }

        /// SHAKE256 Xof state
        pub struct Shake256Xof {
            state: KeccakXofState<136>,
        }

        /// An XOF
        pub trait Xof<const RATE: usize>: private::Sealed {
            /// Create new absorb state
            fn new() -> Self;

            /// Absorb input
            fn absorb(&mut self, input: &[u8]);

            /// Absorb final input (may be empty)
            fn absorb_final(&mut self, input: &[u8]);

            /// Squeeze output bytes
            fn squeeze(&mut self, out: &mut [u8]);
        }

        impl Xof<168> for Shake128Xof {
            fn new() -> Self {
                Self {
                    state: KeccakXofState::<168>::new(),
                }
            }

            fn absorb(&mut self, input: &[u8]) {
                self.state.absorb(&[input]);
            }

            fn absorb_final(&mut self, input: &[u8]) {
                self.state.absorb_final::<0x1fu8>(&[input]);
            }

            /// Shake128 squeeze
            fn squeeze(&mut self, out: &mut [u8]) {
                self.state.squeeze([out]);
            }
        }

        /// Shake256 XOF in absorb state
        impl Xof<136> for Shake256Xof {
            /// Shake256 new state
            fn new() -> Self {
                Self {
                    state: KeccakXofState::<136>::new(),
                }
            }

            /// Shake256 absorb
            fn absorb(&mut self, input: &[u8]) {
                self.state.absorb(&[input]);
            }

            /// Shake256 absorb final
            fn absorb_final(&mut self, input: &[u8]) {
                self.state.absorb_final::<0x1fu8>(&[input]);
            }

            /// Shake256 squeeze
            fn squeeze(&mut self, out: &mut [u8]) {
                self.state.squeeze([out]);
            }
        }

        /// Create a new SHAKE-128 state object.
        #[inline(never)]
        pub fn shake128_init() -> KeccakState {
            KeccakState {
                state: GenericState::<1, [u32; 2]>::new(),
            }
        }

        /// Absorb
        #[inline(never)]
        pub fn shake128_absorb_final(s: &mut KeccakState, data0: &[u8]) {
            absorb_final::<168, 0x1fu8>(&mut s.state, &[data0], 0, data0.len());
        }

        /// Perform four rounds of the keccak permutation functions
        #[inline(never)]
        pub fn keccakf1660_4rounds(s: &mut KeccakState) {
            generic_keccak::keccakf1600_4rounds(&mut s.state);
        }

        /// Squeeze three blocks
        #[inline(always)]
        pub fn shake128_squeeze_first_three_blocks(s: &mut KeccakState, out0: &mut [u8]) {
            squeeze_first_three_blocks::<168>(&mut s.state, [out0])
        }

        /// Squeeze five blocks
        #[inline(always)]
        pub fn shake128_squeeze_first_five_blocks(s: &mut KeccakState, out0: &mut [u8]) {
            squeeze_first_five_blocks::<168>(&mut s.state, [out0])
        }

        /// Squeeze another block
        #[inline(never)]
        pub fn shake128_squeeze_next_block(s: &mut KeccakState, out0: &mut [u8]) {
            squeeze_next_block::<168>(&mut s.state, &mut [out0])
        }

        /// Create a new SHAKE-256 state object.
        #[inline(always)]
        pub fn shake256_init() -> KeccakState {
            KeccakState {
                state: GenericState::<1, [u32; 2]>::new(),
            }
        }

        /// Absorb some data for SHAKE-256 for the last time
        #[inline(always)]
        pub fn shake256_absorb_final(s: &mut KeccakState, data: &[u8]) {
            absorb_final::<136, 0x1fu8>(&mut s.state, &[data], 0, data.len());
        }

        /// Squeeze the first SHAKE-256 block
        #[inline(always)]
        pub fn shake256_squeeze_first_block(s: &mut KeccakState, out: &mut [u8]) {
            squeeze_first_block::<136>(&mut s.state, &mut [out])
        }

        /// Squeeze the next SHAKE-256 block
        #[inline(always)]
        pub fn shake256_squeeze_next_block(s: &mut KeccakState, out: &mut [u8]) {
            squeeze_next_block::<136>(&mut s.state, &mut [out])
        }
    }
}
