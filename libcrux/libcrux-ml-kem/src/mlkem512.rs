//! ML-KEM 512
use super::{constants::*, ind_cca::*, types::*, *};

const RANK: usize = 2;
const RANK_SQUARED: usize = RANK * RANK;
#[cfg(eurydice)]
const RANKED_BYTES_PER_RING_ELEMENT: usize = RANK * BITS_PER_RING_ELEMENT / 8;
const T_AS_NTT_ENCODED_SIZE: usize =
    (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const VECTOR_U_COMPRESSION_FACTOR: usize = 10;
const C1_BLOCK_SIZE: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8;
const C1_SIZE: usize = C1_BLOCK_SIZE * RANK;
const VECTOR_V_COMPRESSION_FACTOR: usize = 4;
const C2_SIZE: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR) / 8;
const CPA_PKE_SECRET_KEY_SIZE: usize =
    (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE: usize = T_AS_NTT_ENCODED_SIZE + 32;
const CPA_PKE_CIPHERTEXT_SIZE: usize = C1_SIZE + C2_SIZE;

pub(crate) const SECRET_KEY_SIZE: usize =
    CPA_PKE_SECRET_KEY_SIZE + CPA_PKE_PUBLIC_KEY_SIZE + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

const ETA1: usize = 3;
const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
const ETA2: usize = 2;
const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

const PRF_OUTPUT_SIZE1: usize = ETA1_RANDOMNESS_SIZE * RANK;
const PRF_OUTPUT_SIZE2: usize = ETA2_RANDOMNESS_SIZE * RANK;

const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE;

/// An ML-KEM 512 Ciphertext
pub type MlKem512Ciphertext = MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE>;
/// An ML-KEM 512 Private key
pub type MlKem512PrivateKey = MlKemPrivateKey<SECRET_KEY_SIZE>;
/// An ML-KEM 512 Public key
pub type MlKem512PublicKey = MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE>;
/// An ML-KEM 512 Key pair
pub type MlKem512KeyPair = MlKemKeyPair<SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE>;

// Instantiate the different functions.
macro_rules! instantiate {
    ($modp:ident, $p:path, $vec:path, $doc:expr) => {
        #[doc = $doc]
        pub mod $modp {
            use super::*;
            use $p as p;

            /// Validate a public key.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_public_key(public_key: &MlKem512PublicKey) -> bool {
                p::validate_public_key::<RANK, CPA_PKE_PUBLIC_KEY_SIZE>(&public_key.value)
            }

            /// Validate a private key.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_private_key(
                private_key: &MlKem512PrivateKey,
                ciphertext: &MlKem512Ciphertext,
            ) -> bool {
                p::validate_private_key::<RANK, SECRET_KEY_SIZE, CPA_PKE_CIPHERTEXT_SIZE>(
                    private_key,
                    ciphertext,
                )
            }

            /// Validate the private key only.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_private_key_only(private_key: &MlKem512PrivateKey) -> bool {
                p::validate_private_key_only::<RANK, SECRET_KEY_SIZE>(private_key)
            }

            /// Generate ML-KEM 512 Key Pair
            pub fn generate_key_pair(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKem512KeyPair {
                p::generate_keypair::<
                    RANK,
                    RANK_SQUARED,
                    CPA_PKE_SECRET_KEY_SIZE,
                    SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                >(randomness)
            }

            /// Generate Kyber 512 Key Pair
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_generate_key_pair(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKem512KeyPair {
                p::kyber_generate_keypair::<
                    RANK,
                    RANK_SQUARED,
                    CPA_PKE_SECRET_KEY_SIZE,
                    SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                >(randomness)
            }
            /// Encapsulate ML-KEM 512
            ///
            /// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            pub fn encapsulate(
                public_key: &MlKem512PublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKem512Ciphertext, MlKemSharedSecret) {
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
                >(public_key, randomness)
            }

            /// Encapsulate Kyber 512
            ///
            /// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_encapsulate(
                public_key: &MlKem512PublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKem512Ciphertext, MlKemSharedSecret) {
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
                >(public_key, randomness)
            }

            /// Decapsulate ML-KEM 512
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
            pub fn decapsulate(
                private_key: &MlKem512PrivateKey,
                ciphertext: &MlKem512Ciphertext,
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

            /// Decapsulate Kyber 512
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_decapsulate(
                private_key: &MlKem512PrivateKey,
                ciphertext: &MlKem512Ciphertext,
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

instantiate! {portable, ind_cca::instantiations::portable, vector::portable::PortableVector, "Portable ML-KEM 512"}

/// Validate a public key.
///
/// Returns `true` if valid, and `false` otherwise.
#[cfg(not(eurydice))]
pub fn validate_public_key(public_key: &MlKem512PublicKey) -> bool {
    multiplexing::validate_public_key::<RANK, CPA_PKE_PUBLIC_KEY_SIZE>(&public_key.value)
}

/// Validate a private key.
///
/// Returns `true` if valid, and `false` otherwise.
#[cfg(not(eurydice))]
pub fn validate_private_key(
    private_key: &MlKem512PrivateKey,
    ciphertext: &MlKem512Ciphertext,
) -> bool {
    multiplexing::validate_private_key::<RANK, SECRET_KEY_SIZE, CPA_PKE_CIPHERTEXT_SIZE>(
        private_key,
        ciphertext,
    )
}

/// Generate ML-KEM 512 Key Pair
///
/// The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
///
/// This function returns an [`MlKem512KeyPair`].
#[cfg(not(eurydice))]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|res|
    fstar!(r#"let ((secret_key, public_key), valid) = Spec.MLKEM.Instances.mlkem512_generate_keypair $randomness in
        valid ==> (${res}.f_sk.f_value == secret_key /\ ${res}.f_pk.f_value == public_key)"#)
)]
pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> MlKem512KeyPair {
    multiplexing::generate_keypair::<
        RANK,
        RANK_SQUARED,
        CPA_PKE_SECRET_KEY_SIZE,
        SECRET_KEY_SIZE,
        CPA_PKE_PUBLIC_KEY_SIZE,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
    >(randomness)
}

/// Encapsulate ML-KEM 512
///
/// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
#[cfg(not(eurydice))]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|res|
    fstar!(r#"let ((ciphertext, shared_secret), valid) = Spec.MLKEM.Instances.mlkem512_encapsulate ${public_key}.f_value $randomness in
        let (res_ciphertext, res_shared_secret) = $res in
        valid ==> (res_ciphertext.f_value == ciphertext /\ res_shared_secret == shared_secret)"#)
)]
pub fn encapsulate(
    public_key: &MlKem512PublicKey,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKem512Ciphertext, MlKemSharedSecret) {
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
    >(public_key, randomness)
}

/// Decapsulate ML-KEM 512
///
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
#[cfg(not(eurydice))]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|res|
    fstar!(r#"let (shared_secret, valid) = Spec.MLKEM.Instances.mlkem512_decapsulate ${private_key}.f_value ${ciphertext}.f_value in
        valid ==> $res == shared_secret"#)
)]
pub fn decapsulate(
    private_key: &MlKem512PrivateKey,
    ciphertext: &MlKem512Ciphertext,
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
        MlKem512Ciphertext, MlKem512KeyPair, MlKem512PublicKey, MlKemSharedSecret,
        KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE,
    };
    use ::rand::CryptoRng;

    /// Generate ML-KEM 512 Key Pair
    ///
    /// The random number generator `rng` needs to implement
    /// `CryptoRng` to sample the required randomness internally.
    ///
    /// This function returns an [`MlKem512KeyPair`].
    pub fn generate_key_pair(rng: &mut impl CryptoRng) -> MlKem512KeyPair {
        let mut randomness = [0u8; KEY_GENERATION_SEED_SIZE];
        rng.fill_bytes(&mut randomness);

        super::generate_key_pair(randomness)
    }

    /// Encapsulate ML-KEM 512
    ///
    /// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
    /// The input is a reference to an [`MlKem512PublicKey`].
    /// The random number generator `rng` needs to implement `CryptoRng`
    /// to sample the required randomness internally.
    pub fn encapsulate(
        public_key: &MlKem512PublicKey,
        rng: &mut impl CryptoRng,
    ) -> (MlKem512Ciphertext, MlKemSharedSecret) {
        let mut randomness = [0u8; SHARED_SECRET_SIZE];
        rng.fill_bytes(&mut randomness);

        super::encapsulate(public_key, randomness)
    }
}

#[cfg(all(not(eurydice), feature = "kyber"))]
pub(crate) mod kyber {
    use super::*;

    /// Generate Kyber 512 Key Pair
    ///
    /// The input is a byte array of size
    /// [`KEY_GENERATION_SEED_SIZE`].
    ///
    /// This function returns an [`MlKem512KeyPair`].
    pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> MlKem512KeyPair {
        multiplexing::kyber_generate_keypair::<
            RANK,
            RANK_SQUARED,
            CPA_PKE_SECRET_KEY_SIZE,
            SECRET_KEY_SIZE,
            CPA_PKE_PUBLIC_KEY_SIZE,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            PRF_OUTPUT_SIZE1,
        >(randomness)
    }

    /// Encapsulate Kyber 512
    ///
    /// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
    /// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
    /// bytes of `randomness`.
    pub fn encapsulate(
        public_key: &MlKem512PublicKey,
        randomness: [u8; SHARED_SECRET_SIZE],
    ) -> (MlKem512Ciphertext, MlKemSharedSecret) {
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
        >(public_key, randomness)
    }

    /// Decapsulate Kyber 512
    ///
    /// Generates an [`MlKemSharedSecret`].
    /// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].

    pub fn decapsulate(
        private_key: &MlKem512PrivateKey,
        ciphertext: &MlKem512Ciphertext,
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
