//! ML-KEM 768

use super::{constants::*, ind_cca::*, types::*, *};
use libcrux_secrets::U8;

const RANK: usize = 3;
const RANK_SQUARED: usize = RANK * RANK;
#[cfg(eurydice)]
const RANKED_BYTES_PER_RING_ELEMENT: usize = RANK * BITS_PER_RING_ELEMENT / 8;
const T_AS_NTT_ENCODED_SIZE: usize =
    (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const VECTOR_U_COMPRESSION_FACTOR: usize = 10;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_U_COMPRESSION_FACTOR>()
const C1_BLOCK_SIZE: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8;
// [hax]: hacspec/hacspec-v2#27 stealing error
//  serialized_len::<RANK, C1_BLOCK_SIZE>();
const C1_SIZE: usize = C1_BLOCK_SIZE * RANK;
const VECTOR_V_COMPRESSION_FACTOR: usize = 4;
// [hax]: hacspec/hacspec-v2#27 stealing error
//  block_len::<VECTOR_V_COMPRESSION_FACTOR>()
const C2_SIZE: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR) / 8;
const CPA_PKE_SECRET_KEY_SIZE: usize =
    (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE: usize = T_AS_NTT_ENCODED_SIZE + 32;
// These two are used in the hybrid kem. This could probably be improved.
const CPA_PKE_CIPHERTEXT_SIZE: usize = C1_SIZE + C2_SIZE;
pub(crate) const SECRET_KEY_SIZE: usize =
    CPA_PKE_SECRET_KEY_SIZE + CPA_PKE_PUBLIC_KEY_SIZE + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

const ETA1: usize = 2;
const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
const ETA2: usize = 2;
const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

const PRF_OUTPUT_SIZE1: usize = ETA1_RANDOMNESS_SIZE * RANK;
const PRF_OUTPUT_SIZE2: usize = ETA2_RANDOMNESS_SIZE * RANK;

const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE;

/// The ML-KEM 768 algorithms
pub struct MlKem768;

#[cfg(not(any(hax, eurydice)))]
crate::impl_kem_trait!(
    MlKem768,
    MlKem768PublicKey,
    MlKem768PrivateKey,
    MlKem768Ciphertext
);

// Provide the (packed) PQCP APIs
#[cfg(feature = "pqcp")]
crate::pqcp::pqcp_api!(
    "use libcrux_iot_ml_kem::mlkem768::pqcp::*;",
    MlKem768,
    " 768 "
);

/// An ML-KEM 768 Ciphertext
pub type MlKem768Ciphertext = MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE>;
/// An ML-KEM 768 Private key
pub type MlKem768PrivateKey = MlKemPrivateKey<SECRET_KEY_SIZE>;
/// An ML-KEM 768 Public key
pub type MlKem768PublicKey = MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE>;
/// An ML-KEM 768 Key pair
pub type MlKem768KeyPair = MlKemKeyPair<SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE>;

// Instantiate the different functions.
macro_rules! instantiate {
    ($modp:ident, $p:path, $doc:expr) => {
        #[doc = $doc]
        pub mod $modp {
            use super::*;
            use $p as p;

            /// Validate a public key.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_public_key(public_key: &MlKem768PublicKey) -> bool {
                p::validate_public_key::<RANK, CPA_PKE_PUBLIC_KEY_SIZE>(&public_key.value)
            }

            /// Validate a private key.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_private_key(
                private_key: &MlKem768PrivateKey,
                ciphertext: &MlKem768Ciphertext,
            ) -> bool {
                p::validate_private_key::<RANK, SECRET_KEY_SIZE, CPA_PKE_CIPHERTEXT_SIZE>(
                    private_key,
                    ciphertext,
                )
            }

            /// Validate the private key only.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_private_key_only(private_key: &MlKem768PrivateKey) -> bool {
                p::validate_private_key_only::<RANK, SECRET_KEY_SIZE>(private_key)
            }

            /// Generate ML-KEM 768 Key Pair
            pub fn generate_key_pair(
                randomness: [U8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKem768KeyPair {
                p::generate_keypair::<
                    RANK,
                    RANK_SQUARED,
                    CPA_PKE_SECRET_KEY_SIZE,
                    SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                >(&randomness)
            }

            /// Generate Kyber 768 Key Pair
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_generate_key_pair(
                randomness: [U8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKem768KeyPair {
                p::kyber_generate_keypair::<
                    RANK,
                    RANK_SQUARED,
                    CPA_PKE_SECRET_KEY_SIZE,
                    SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                >(&randomness)
            }

            /// Encapsulate ML-KEM 768
            ///
            /// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            pub fn encapsulate(
                public_key: &MlKem768PublicKey,
                randomness: [U8; SHARED_SECRET_SIZE],
            ) -> (MlKem768Ciphertext, MlKemSharedSecret) {
                p::encapsulate::<
                    RANK,
                    RANK_SQUARED,
                    CPA_PKE_CIPHERTEXT_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    T_AS_NTT_ENCODED_SIZE,
                    C1_SIZE,
                    C2_SIZE,
                    VECTOR_U_COMPRESSION_FACTOR,
                    VECTOR_V_COMPRESSION_FACTOR,
                    C1_BLOCK_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                    PRF_OUTPUT_SIZE2,
                >(public_key, &randomness)
            }

            /// Encapsulate Kyber 768
            ///
            /// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_encapsulate(
                public_key: &MlKem768PublicKey,
                randomness: [U8; SHARED_SECRET_SIZE],
            ) -> (MlKem768Ciphertext, MlKemSharedSecret) {
                p::kyber_encapsulate::<
                    RANK,
                    RANK_SQUARED,
                    CPA_PKE_CIPHERTEXT_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    T_AS_NTT_ENCODED_SIZE,
                    C1_SIZE,
                    C2_SIZE,
                    VECTOR_U_COMPRESSION_FACTOR,
                    VECTOR_V_COMPRESSION_FACTOR,
                    C1_BLOCK_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                    PRF_OUTPUT_SIZE2,
                >(public_key, &randomness)
            }

            /// Decapsulate ML-KEM 768
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
            pub fn decapsulate(
                private_key: &MlKem768PrivateKey,
                ciphertext: &MlKem768Ciphertext,
            ) -> MlKemSharedSecret {
                p::decapsulate::<
                    RANK,
                    RANK_SQUARED,
                    SECRET_KEY_SIZE,
                    CPA_PKE_SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    CPA_PKE_CIPHERTEXT_SIZE,
                    T_AS_NTT_ENCODED_SIZE,
                    C1_SIZE,
                    C2_SIZE,
                    VECTOR_U_COMPRESSION_FACTOR,
                    VECTOR_V_COMPRESSION_FACTOR,
                    C1_BLOCK_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                    PRF_OUTPUT_SIZE2,
                    IMPLICIT_REJECTION_HASH_INPUT_SIZE,
                >(private_key, ciphertext)
            }

            /// Decapsulate Kyber 768
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_decapsulate(
                private_key: &MlKem768PrivateKey,
                ciphertext: &MlKem768Ciphertext,
            ) -> MlKemSharedSecret {
                p::kyber_decapsulate::<
                    RANK,
                    RANK_SQUARED,
                    SECRET_KEY_SIZE,
                    CPA_PKE_SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    CPA_PKE_CIPHERTEXT_SIZE,
                    T_AS_NTT_ENCODED_SIZE,
                    C1_SIZE,
                    C2_SIZE,
                    VECTOR_U_COMPRESSION_FACTOR,
                    VECTOR_V_COMPRESSION_FACTOR,
                    C1_BLOCK_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                    PRF_OUTPUT_SIZE2,
                    IMPLICIT_REJECTION_HASH_INPUT_SIZE,
                >(private_key, ciphertext)
            }
        }
    };
}

// Instantiations

instantiate! {portable, ind_cca::instantiations::portable, "Portable ML-KEM 768"}

/// Validate a public key.
///
/// Returns `true` if valid, and `false` otherwise.
#[cfg(not(eurydice))]
pub fn validate_public_key(public_key: &MlKem768PublicKey) -> bool {
    multiplexing::validate_public_key::<RANK, CPA_PKE_PUBLIC_KEY_SIZE>(&public_key.value)
}

/// Validate a private key.
///
/// Returns `true` if valid, and `false` otherwise.
#[cfg(not(eurydice))]
pub fn validate_private_key(
    private_key: &MlKem768PrivateKey,
    ciphertext: &MlKem768Ciphertext,
) -> bool {
    multiplexing::validate_private_key::<RANK, SECRET_KEY_SIZE, CPA_PKE_CIPHERTEXT_SIZE>(
        private_key,
        ciphertext,
    )
}

/// Generate ML-KEM 768 Key Pair
///
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
///
/// This function returns an [`MlKem768KeyPair`].
#[cfg(not(eurydice))]
pub fn generate_key_pair(randomness: [U8; KEY_GENERATION_SEED_SIZE]) -> MlKem768KeyPair {
    multiplexing::generate_keypair::<
        RANK,
        RANK_SQUARED,
        CPA_PKE_SECRET_KEY_SIZE,
        SECRET_KEY_SIZE,
        CPA_PKE_PUBLIC_KEY_SIZE,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
    >(&randomness)
}

/// Encapsulate ML-KEM 768
///
/// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
#[cfg(not(eurydice))]
pub fn encapsulate(
    public_key: &MlKem768PublicKey,
    randomness: [U8; SHARED_SECRET_SIZE],
) -> (MlKem768Ciphertext, MlKemSharedSecret) {
    multiplexing::encapsulate::<
        RANK,
        RANK_SQUARED,
        CPA_PKE_CIPHERTEXT_SIZE,
        CPA_PKE_PUBLIC_KEY_SIZE,
        T_AS_NTT_ENCODED_SIZE,
        C1_SIZE,
        C2_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
        C1_BLOCK_SIZE,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
        PRF_OUTPUT_SIZE2,
    >(public_key, &randomness)
}

/// Decapsulate ML-KEM 768
///
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
#[cfg(not(eurydice))]
pub fn decapsulate(
    private_key: &MlKem768PrivateKey,
    ciphertext: &MlKem768Ciphertext,
) -> MlKemSharedSecret {
    multiplexing::decapsulate::<
        RANK,
        RANK_SQUARED,
        SECRET_KEY_SIZE,
        CPA_PKE_SECRET_KEY_SIZE,
        CPA_PKE_PUBLIC_KEY_SIZE,
        CPA_PKE_CIPHERTEXT_SIZE,
        T_AS_NTT_ENCODED_SIZE,
        C1_SIZE,
        C2_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
        C1_BLOCK_SIZE,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
        PRF_OUTPUT_SIZE2,
        IMPLICIT_REJECTION_HASH_INPUT_SIZE,
    >(private_key, ciphertext)
}

/// Randomized APIs
///
/// The functions in this module are equivalent to the one in the main module,
/// but sample their own randomness, provided a random number generator that
/// implements `CryptoRng`.
///
/// Decapsulation is not provided in this module as it does not require randomness.
#[cfg(all(not(eurydice), feature = "rand"))]
pub mod rand {
    use super::{
        MlKem768Ciphertext, MlKem768KeyPair, MlKem768PublicKey, MlKemSharedSecret,
        KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE,
    };
    use ::rand::CryptoRng;
    use libcrux_secrets::{Classify as _, DeclassifyRefMut as _};

    /// Generate ML-KEM 768 Key Pair
    ///
    /// The random number generator `rng` needs to implement `CryptoRng`
    /// to sample the required randomness internally.
    ///
    /// This function returns an [`MlKem768KeyPair`].
    pub fn generate_key_pair(rng: &mut impl CryptoRng) -> MlKem768KeyPair {
        let mut randomness = [0u8.classify(); KEY_GENERATION_SEED_SIZE];
        rng.fill_bytes(randomness.declassify_ref_mut());

        super::generate_key_pair(randomness)
    }

    /// Encapsulate ML-KEM 768
    ///
    /// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
    /// The input is a reference to an [`MlKem768PublicKey`].
    /// The random number generator `rng` needs to implement `CryptoRng`
    /// to sample the required randomness internally.
    pub fn encapsulate(
        public_key: &MlKem768PublicKey,
        rng: &mut impl CryptoRng,
    ) -> (MlKem768Ciphertext, MlKemSharedSecret) {
        let mut randomness = [0u8.classify(); SHARED_SECRET_SIZE];
        rng.fill_bytes(randomness.declassify_ref_mut());

        super::encapsulate(public_key, randomness)
    }
}

#[cfg(all(not(eurydice), feature = "kyber"))]
pub(crate) mod kyber {
    use super::*;

    /// The Kyber 768 algorithms
    pub struct Kyber768;

    crate::impl_kem_trait!(
        Kyber768,
        MlKem768PublicKey,
        MlKem768PrivateKey,
        MlKem768Ciphertext
    );

    /// Generate Kyber 768 Key Pair
    ///
    /// Generate a Kyber key pair. The input is a byte array of size
    /// [`KEY_GENERATION_SEED_SIZE`].
    ///
    /// This function returns an [`MlKem768KeyPair`].
    pub fn generate_key_pair(randomness: [U8; KEY_GENERATION_SEED_SIZE]) -> MlKem768KeyPair {
        multiplexing::kyber_generate_keypair::<
            RANK,
            RANK_SQUARED,
            CPA_PKE_SECRET_KEY_SIZE,
            SECRET_KEY_SIZE,
            CPA_PKE_PUBLIC_KEY_SIZE,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            PRF_OUTPUT_SIZE1,
        >(&randomness)
    }

    /// Encapsulate Kyber 768
    ///
    /// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
    /// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
    /// bytes of `randomness`.
    pub fn encapsulate(
        public_key: &MlKem768PublicKey,
        randomness: [U8; SHARED_SECRET_SIZE],
    ) -> (MlKem768Ciphertext, MlKemSharedSecret) {
        multiplexing::kyber_encapsulate::<
            RANK,
            RANK_SQUARED,
            CPA_PKE_CIPHERTEXT_SIZE,
            CPA_PKE_PUBLIC_KEY_SIZE,
            T_AS_NTT_ENCODED_SIZE,
            C1_SIZE,
            C2_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_V_COMPRESSION_FACTOR,
            C1_BLOCK_SIZE,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
            PRF_OUTPUT_SIZE1,
            PRF_OUTPUT_SIZE2,
        >(public_key, &randomness)
    }

    /// Decapsulate ML-KEM 768
    ///
    /// Generates an [`MlKemSharedSecret`].
    /// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
    pub fn decapsulate(
        private_key: &MlKem768PrivateKey,
        ciphertext: &MlKem768Ciphertext,
    ) -> MlKemSharedSecret {
        multiplexing::kyber_decapsulate::<
            RANK,
            RANK_SQUARED,
            SECRET_KEY_SIZE,
            CPA_PKE_SECRET_KEY_SIZE,
            CPA_PKE_PUBLIC_KEY_SIZE,
            CPA_PKE_CIPHERTEXT_SIZE,
            T_AS_NTT_ENCODED_SIZE,
            C1_SIZE,
            C2_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_V_COMPRESSION_FACTOR,
            C1_BLOCK_SIZE,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
            PRF_OUTPUT_SIZE1,
            PRF_OUTPUT_SIZE2,
            IMPLICIT_REJECTION_HASH_INPUT_SIZE,
        >(private_key, ciphertext)
    }
}

#[cfg(test)]
mod tests {
    use libcrux_secrets::{Classify as _, DeclassifyRefMut as _};
    use rand::{rngs::OsRng, TryRngCore};

    use super::{
        mlkem768::{generate_key_pair, validate_public_key},
        KEY_GENERATION_SEED_SIZE,
    };

    #[test]
    fn pk_validation() {
        let mut randomness = [0u8.classify(); KEY_GENERATION_SEED_SIZE];
        OsRng
            .try_fill_bytes(randomness.declassify_ref_mut())
            .unwrap();

        let key_pair = generate_key_pair(randomness);
        assert!(validate_public_key(&key_pair.pk));
    }
}
