macro_rules! instantiate {
    ($modp:ident, $vector:path, $hash:path) => {
        pub mod $modp {
            use crate::{
                MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey, MlKemSharedSecret,
                KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE,
            };
            use libcrux_secrets::U8;

            /// Portable generate key pair.
            #[hax_lib::requires(
                ((K == 2 && PRIVATE_KEY_SIZE == crate::mlkem512::SECRET_KEY_SIZE)
                    || (K == 3 && PRIVATE_KEY_SIZE == crate::mlkem768::SECRET_KEY_SIZE)
                    || (K == 4 && PRIVATE_KEY_SIZE == crate::mlkem1024::SECRET_KEY_SIZE)) &&
                K_SQUARED == K * K &&
                (ETA1 == 3 || ETA1 == 2) &&
                ETA1_RANDOMNESS_SIZE == 64 * ETA1 &&
                CPA_PRIVATE_KEY_SIZE == K * crate::constants::BYTES_PER_RING_ELEMENT &&
                PRF_OUTPUT_SIZE1 == K * ETA1_RANDOMNESS_SIZE &&
                PUBLIC_KEY_SIZE == K * crate::constants::BYTES_PER_RING_ELEMENT + 32
            )]
            pub(crate) fn generate_keypair<
                const K: usize,
                const K_SQUARED: usize,
                const CPA_PRIVATE_KEY_SIZE: usize,
                const PRIVATE_KEY_SIZE: usize,
                const PUBLIC_KEY_SIZE: usize,
                const ETA1: usize,
                const ETA1_RANDOMNESS_SIZE: usize,
                const PRF_OUTPUT_SIZE1: usize,
            >(
                randomness: &[U8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
                crate::ind_cca::generate_keypair::<
                    K,
                    K_SQUARED,
                    CPA_PRIVATE_KEY_SIZE,
                    PRIVATE_KEY_SIZE,
                    PUBLIC_KEY_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                    $vector,
                    $hash,
                    crate::variant::MlKem,
                >(randomness)
            }

            #[cfg(feature = "kyber")]
            pub(crate) fn kyber_generate_keypair<
                const K: usize,
                const K_SQUARED: usize,
                const CPA_PRIVATE_KEY_SIZE: usize,
                const PRIVATE_KEY_SIZE: usize,
                const PUBLIC_KEY_SIZE: usize,
                const ETA1: usize,
                const ETA1_RANDOMNESS_SIZE: usize,
                const PRF_OUTPUT_SIZE1: usize,
            >(
                randomness: &[U8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
                crate::ind_cca::generate_keypair::<
                    K,
                    K_SQUARED,
                    CPA_PRIVATE_KEY_SIZE,
                    PRIVATE_KEY_SIZE,
                    PUBLIC_KEY_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                    $vector,
                    $hash,
                    crate::variant::Kyber,
                >(randomness)
            }

            /// Public key validation
            #[hax_lib::requires(
                (K == 2 || K == 3 || K == 4) &&
                PUBLIC_KEY_SIZE == K * crate::constants::BYTES_PER_RING_ELEMENT + 32
            )]
            #[inline(always)]
            pub(crate) fn validate_public_key<
                const K: usize,
                const PUBLIC_KEY_SIZE: usize,
            >(
                public_key: &[u8; PUBLIC_KEY_SIZE],
            ) -> bool {
                crate::ind_cca::validate_public_key::<
                    K,
                    PUBLIC_KEY_SIZE,
                    $vector,
                >(public_key)
            }

            /// Private key validation
            #[hax_lib::requires(
                match K {
                    2 => SECRET_KEY_SIZE == crate::mlkem512::SECRET_KEY_SIZE,
                    3 => SECRET_KEY_SIZE == crate::mlkem768::SECRET_KEY_SIZE,
                    4 => SECRET_KEY_SIZE == crate::mlkem1024::SECRET_KEY_SIZE,
                    _ => false
                }
            )]
            #[inline(always)]
            pub(crate) fn validate_private_key<
                const K: usize,
                const SECRET_KEY_SIZE: usize,
                const CIPHERTEXT_SIZE: usize,
            >(
                private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
                ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
            ) -> bool {
                crate::ind_cca::validate_private_key::<K, SECRET_KEY_SIZE, CIPHERTEXT_SIZE, $hash>(
                    private_key,
                    ciphertext,
                )
            }

            /// Private key validation
            #[hax_lib::requires(
                match K {
                    2 => SECRET_KEY_SIZE == crate::mlkem512::SECRET_KEY_SIZE,
                    3 => SECRET_KEY_SIZE == crate::mlkem768::SECRET_KEY_SIZE,
                    4 => SECRET_KEY_SIZE == crate::mlkem1024::SECRET_KEY_SIZE,
                    _ => false
                }
            )]
            #[inline(always)]
            pub(crate) fn validate_private_key_only<
                const K: usize,
                const SECRET_KEY_SIZE: usize,
            >(
                private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
            ) -> bool {
                crate::ind_cca::validate_private_key_only::<K, SECRET_KEY_SIZE, $hash>(private_key)
            }

            /// Portable encapsulate
            #[cfg(feature = "kyber")]
            pub(crate) fn kyber_encapsulate<
                const K: usize,
                const K_SQUARED: usize,
                const CIPHERTEXT_SIZE: usize,
                const PUBLIC_KEY_SIZE: usize,
                const T_AS_NTT_ENCODED_SIZE: usize,
                const C1_SIZE: usize,
                const C2_SIZE: usize,
                const VECTOR_U_COMPRESSION_FACTOR: usize,
                const VECTOR_V_COMPRESSION_FACTOR: usize,
                const VECTOR_U_BLOCK_LEN: usize,
                const ETA1: usize,
                const ETA1_RANDOMNESS_SIZE: usize,
                const ETA2: usize,
                const ETA2_RANDOMNESS_SIZE: usize,
                const PRF_OUTPUT_SIZE1: usize,
                const PRF_OUTPUT_SIZE2: usize,
            >(
                public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
                randomness: &[U8; SHARED_SECRET_SIZE],
            ) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
                crate::ind_cca::encapsulate::<
                    K,
                    K_SQUARED,
                    CIPHERTEXT_SIZE,
                    PUBLIC_KEY_SIZE,
                    T_AS_NTT_ENCODED_SIZE,
                    C1_SIZE,
                    C2_SIZE,
                    VECTOR_U_COMPRESSION_FACTOR,
                    VECTOR_V_COMPRESSION_FACTOR,
                    VECTOR_U_BLOCK_LEN,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                    PRF_OUTPUT_SIZE1,
                    PRF_OUTPUT_SIZE2,
                    $vector,
                    $hash,
                    crate::variant::Kyber,
                >(public_key, randomness)
            }

            #[hax_lib::requires(
                (K == 2 || K == 3 || K == 4) &&
                K_SQUARED == K * K &&
                (ETA1 == 3 || ETA1 == 2) &&
                ETA1_RANDOMNESS_SIZE == 64 * ETA1 &&
                PRF_OUTPUT_SIZE1 == K * ETA1_RANDOMNESS_SIZE &&
                ETA2 == 2 &&
                ETA2_RANDOMNESS_SIZE == 64 * ETA2 &&
                PRF_OUTPUT_SIZE2 == K * ETA2_RANDOMNESS_SIZE &&
                ((VECTOR_U_COMPRESSION_FACTOR == 10 && C1_BLOCK_SIZE == crate::polynomial::VECTORS_IN_RING_ELEMENT * 20)
                    || (VECTOR_U_COMPRESSION_FACTOR == 11 && C1_BLOCK_SIZE == crate::polynomial::VECTORS_IN_RING_ELEMENT * 22)) &&
                (VECTOR_V_COMPRESSION_FACTOR == 4 && C2_SIZE == 128 ||
                    VECTOR_V_COMPRESSION_FACTOR == 5 && C2_SIZE == 160) &&
                C1_SIZE == K * C1_BLOCK_SIZE &&
                CIPHERTEXT_SIZE == C1_SIZE + C2_SIZE &&
                T_AS_NTT_ENCODED_SIZE == crate::constants::BYTES_PER_RING_ELEMENT * K &&
                PUBLIC_KEY_SIZE == T_AS_NTT_ENCODED_SIZE + 32
            )]
            pub(crate) fn encapsulate<
                const K: usize,
                const K_SQUARED: usize,
                const CIPHERTEXT_SIZE: usize,
                const PUBLIC_KEY_SIZE: usize,
                const T_AS_NTT_ENCODED_SIZE: usize,
                const C1_SIZE: usize,
                const C2_SIZE: usize,
                const VECTOR_U_COMPRESSION_FACTOR: usize,
                const VECTOR_V_COMPRESSION_FACTOR: usize,
                const C1_BLOCK_SIZE: usize,
                const ETA1: usize,
                const ETA1_RANDOMNESS_SIZE: usize,
                const ETA2: usize,
                const ETA2_RANDOMNESS_SIZE: usize,
                const PRF_OUTPUT_SIZE1: usize,
                const PRF_OUTPUT_SIZE2: usize,
            >(
                public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
                randomness: &[U8; SHARED_SECRET_SIZE],
            ) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
                crate::ind_cca::encapsulate::<
                    K,
                    K_SQUARED,
                    CIPHERTEXT_SIZE,
                    PUBLIC_KEY_SIZE,
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
                    $vector,
                    $hash,
                    crate::variant::MlKem,
                >(public_key, randomness)
            }

            /// Portable decapsulate
            #[cfg(feature = "kyber")]
            pub fn kyber_decapsulate<
                const K: usize,
                const K_SQUARED: usize,
                const SECRET_KEY_SIZE: usize,
                const CPA_SECRET_KEY_SIZE: usize,
                const PUBLIC_KEY_SIZE: usize,
                const CIPHERTEXT_SIZE: usize,
                const T_AS_NTT_ENCODED_SIZE: usize,
                const C1_SIZE: usize,
                const C2_SIZE: usize,
                const VECTOR_U_COMPRESSION_FACTOR: usize,
                const VECTOR_V_COMPRESSION_FACTOR: usize,
                const C1_BLOCK_SIZE: usize,
                const ETA1: usize,
                const ETA1_RANDOMNESS_SIZE: usize,
                const ETA2: usize,
                const ETA2_RANDOMNESS_SIZE: usize,
                const PRF_OUTPUT_SIZE1: usize,
                const PRF_OUTPUT_SIZE2: usize,
                const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize,
            >(
                private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
                ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
            ) -> MlKemSharedSecret {
                crate::ind_cca::decapsulate::<
                    K,
                    K_SQUARED,
                    SECRET_KEY_SIZE,
                    CPA_SECRET_KEY_SIZE,
                    PUBLIC_KEY_SIZE,
                    CIPHERTEXT_SIZE,
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
                    $vector,
                    $hash,
                    crate::variant::Kyber,
                >(private_key, ciphertext)
            }

            /// Portable decapsulate
            #[hax_lib::requires(
                (
                    K == 2 &&
                    SECRET_KEY_SIZE == crate::mlkem512::SECRET_KEY_SIZE &&
                    CPA_SECRET_KEY_SIZE == crate::mlkem512::CPA_PKE_SECRET_KEY_SIZE &&
                    PUBLIC_KEY_SIZE == crate::mlkem512::CPA_PKE_PUBLIC_KEY_SIZE
                    || K == 3 &&
                    SECRET_KEY_SIZE == crate::mlkem768::SECRET_KEY_SIZE &&
                    CPA_SECRET_KEY_SIZE == crate::mlkem768::CPA_PKE_SECRET_KEY_SIZE &&
                    PUBLIC_KEY_SIZE == crate::mlkem768::CPA_PKE_PUBLIC_KEY_SIZE
                    || K == 4 &&
                    SECRET_KEY_SIZE == crate::mlkem1024::SECRET_KEY_SIZE &&
                    CPA_SECRET_KEY_SIZE == crate::mlkem1024::CPA_PKE_SECRET_KEY_SIZE &&
                    PUBLIC_KEY_SIZE == crate::mlkem1024::CPA_PKE_PUBLIC_KEY_SIZE
                ) &&
                K_SQUARED == K * K &&
                (ETA1 == 3 || ETA1 == 2) &&
                ETA1_RANDOMNESS_SIZE == 64 * ETA1 &&
                PRF_OUTPUT_SIZE1 == K * ETA1_RANDOMNESS_SIZE &&
                ETA2 == 2 &&
                ETA2_RANDOMNESS_SIZE == 64 * ETA2 &&
                PRF_OUTPUT_SIZE2 == K * ETA2_RANDOMNESS_SIZE &&
                ((VECTOR_U_COMPRESSION_FACTOR == 10 && C1_BLOCK_SIZE == crate::polynomial::VECTORS_IN_RING_ELEMENT * 20)
                    || (VECTOR_U_COMPRESSION_FACTOR == 11 && C1_BLOCK_SIZE == crate::polynomial::VECTORS_IN_RING_ELEMENT * 22)) &&
                (VECTOR_V_COMPRESSION_FACTOR == 4 && C2_SIZE == 128 ||
                    VECTOR_V_COMPRESSION_FACTOR == 5 && C2_SIZE == 160) &&
                C1_SIZE == K * C1_BLOCK_SIZE &&
                CIPHERTEXT_SIZE == C1_SIZE + C2_SIZE &&
                T_AS_NTT_ENCODED_SIZE == crate::constants::BYTES_PER_RING_ELEMENT * K &&
                CIPHERTEXT_SIZE == K * 32 * VECTOR_U_COMPRESSION_FACTOR + 32 * VECTOR_V_COMPRESSION_FACTOR &&
                IMPLICIT_REJECTION_HASH_INPUT_SIZE == SHARED_SECRET_SIZE + CIPHERTEXT_SIZE
            )]
            pub fn decapsulate<
                const K: usize,
                const K_SQUARED: usize,
                const SECRET_KEY_SIZE: usize,
                const CPA_SECRET_KEY_SIZE: usize,
                const PUBLIC_KEY_SIZE: usize,
                const CIPHERTEXT_SIZE: usize,
                const T_AS_NTT_ENCODED_SIZE: usize,
                const C1_SIZE: usize,
                const C2_SIZE: usize,
                const VECTOR_U_COMPRESSION_FACTOR: usize,
                const VECTOR_V_COMPRESSION_FACTOR: usize,
                const C1_BLOCK_SIZE: usize,
                const ETA1: usize,
                const ETA1_RANDOMNESS_SIZE: usize,
                const ETA2: usize,
                const ETA2_RANDOMNESS_SIZE: usize,
                const PRF_OUTPUT_SIZE1: usize,
                const PRF_OUTPUT_SIZE2: usize,
                const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize,
            >(
                private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
                ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
            ) -> MlKemSharedSecret {
                crate::ind_cca::decapsulate::<
                    K,
                    K_SQUARED,
                    SECRET_KEY_SIZE,
                    CPA_SECRET_KEY_SIZE,
                    PUBLIC_KEY_SIZE,
                    CIPHERTEXT_SIZE,
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
                    $vector,
                    $hash,
                    crate::variant::MlKem,
                >(private_key, ciphertext)
            }
        }
    };
}

// Portable generic implementations.
instantiate! {portable, crate::vector::portable::PortableVector, crate::hash_functions::portable::PortableHash}
