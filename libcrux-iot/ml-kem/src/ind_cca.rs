use libcrux_secrets::{Classify as _, ClassifyRef as _, DeclassifyRef, U8};

use crate::{
    constant_time_ops::compare_ciphertexts_select_shared_secret_in_constant_time, constants::*,
    hash_functions::Hash, ind_cpa::serialize_public_key_mut, polynomial::PolynomialRingElement,
    serialize::deserialize_ring_elements_reduced, types::*, utils::into_padded_array, variant::*,
    vector::Operations,
};

/// Seed size for key generation
pub const KEY_GENERATION_SEED_SIZE: usize = CPA_PKE_KEY_GENERATION_SEED_SIZE + SHARED_SECRET_SIZE;

/// Seed size for encapsulation
pub const ENCAPS_SEED_SIZE: usize = SHARED_SECRET_SIZE;

// TODO: We should make this an actual type as opposed to alias so we can enforce
// some checks at the type level. This is being tracked in:
// https://github.com/cryspen/libcrux/issues/123
/// An ML-KEM shared secret.
///
/// A byte array of size [`SHARED_SECRET_SIZE`].
pub type MlKemSharedSecret = [U8; SHARED_SECRET_SIZE];

/// This module instantiates the functions in this file and multiplexes between
/// different implementations at runtime.
#[cfg(not(eurydice))]
pub(crate) mod multiplexing;

/// This module instantiates the functions in this file for each platform.
/// To use these, runtime checks must be performed before calling them.
pub(crate) mod instantiations;

/// Serialize the secret key.

#[hax_lib::requires(
    SERIALIZED_KEY_LEN == private_key.len() + public_key.len() + H_DIGEST_SIZE + implicit_rejection_value.len() &&
    (SERIALIZED_KEY_LEN == crate::mlkem512::SECRET_KEY_SIZE ||
        SERIALIZED_KEY_LEN == crate::mlkem768::SECRET_KEY_SIZE ||
        SERIALIZED_KEY_LEN == crate::mlkem1024::SECRET_KEY_SIZE)
)]
#[inline(always)]
fn serialize_kem_secret_key_mut<const K: usize, const SERIALIZED_KEY_LEN: usize, Hasher: Hash>(
    private_key: &[U8],
    public_key: &[u8],
    implicit_rejection_value: &[U8],
    serialized: &mut [U8; SERIALIZED_KEY_LEN],
) {
    let mut pointer = 0;
    serialized[pointer..pointer + private_key.len()].copy_from_slice(private_key);
    pointer += private_key.len();
    serialized[pointer..pointer + public_key.len()].copy_from_slice(public_key.classify_ref());
    pointer += public_key.len();
    Hasher::H(
        public_key.classify_ref(),
        &mut serialized[pointer..pointer + H_DIGEST_SIZE],
    );
    pointer += H_DIGEST_SIZE;
    serialized[pointer..pointer + implicit_rejection_value.len()]
        .copy_from_slice(implicit_rejection_value);
}

/// Validate an ML-KEM public key.
///
/// This implements the Modulus check in 7.2 2.
/// Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
/// `public_key` type.
#[hax_lib::requires(PUBLIC_KEY_SIZE == K * BYTES_PER_RING_ELEMENT + 32)]
#[inline(always)]
pub(crate) fn validate_public_key<
    const K: usize,
    const PUBLIC_KEY_SIZE: usize,
    Vector: Operations,
>(
    public_key: &[u8; PUBLIC_KEY_SIZE],
) -> bool {
    let mut deserialized_pk: [PolynomialRingElement<Vector>; K] =
        core::array::from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
    deserialize_ring_elements_reduced::<K, Vector>(
        &public_key[..ranked_bytes_per_ring_element(K)],
        &mut deserialized_pk,
    );
    let mut public_key_serialized = [0u8; PUBLIC_KEY_SIZE];
    let mut scratch = Vector::ZERO();
    serialize_public_key_mut::<K, PUBLIC_KEY_SIZE, Vector>(
        &deserialized_pk,
        &public_key[ranked_bytes_per_ring_element(K)..],
        &mut public_key_serialized,
        &mut scratch,
    );

    *public_key == public_key_serialized
}

/// Validate an ML-KEM private key.
///
/// This implements the Hash check in 7.3 3.
/// Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
/// and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
#[inline(always)]
pub(crate) fn validate_private_key<
    const K: usize,
    const SECRET_KEY_SIZE: usize,
    const CIPHERTEXT_SIZE: usize,
    Hasher: Hash,
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    _ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
) -> bool {
    validate_private_key_only::<K, SECRET_KEY_SIZE, Hasher>(private_key)
}

/// Validate an ML-KEM private key.
///
/// This implements the Hash check in 7.3 3.
#[inline(always)]
pub(crate) fn validate_private_key_only<
    const K: usize,
    const SECRET_KEY_SIZE: usize,
    Hasher: Hash,
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
) -> bool {
    // Eurydice can't access values directly on the types. We need to go to the
    // `value` directly.
    let mut t = [0u8.classify(); H_DIGEST_SIZE];
    // This slice of the ML-KEM private key is the ML-KEM
    // public key (see FIPS203, Algorithm 16, line 3), and thus public
    // information.
    Hasher::H(&private_key.value[384 * K..768 * K + 32], &mut t);
    // Declassification: This slice of the ML-KEM private key is the
    // hash of the ML-KEM public key (see FIPS203, Algorithm 16, line
    // 3), and thus public information
    let expected = private_key.value[768 * K + 32..768 * K + 64].declassify_ref();
    // Declassification: There are no secret values in this
    // comparison, see above.
    // XXX: We need `.as_slice()` here for Eurydice.
    t.as_slice().declassify_ref() == expected
}

/// Packed API
///
/// Generate a key pair.
///
/// Depending on the `Vector` and `Hasher` used, this requires different hardware
/// features
#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) &&
    K_SQUARED == K * K &&
    (ETA1 == 3 || ETA1 == 2) &&
    ETA1_RANDOMNESS_SIZE == 64 * ETA1 &&
    PRF_OUTPUT_SIZE1 == K * ETA1_RANDOMNESS_SIZE &&
    PRIVATE_KEY_SIZE == K * BYTES_PER_RING_ELEMENT &&
    PUBLIC_KEY_SIZE == K * BYTES_PER_RING_ELEMENT + 32
)]
#[inline(always)]
pub(crate) fn generate_keypair<
    const K: usize,
    const K_SQUARED: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const PRF_OUTPUT_SIZE1: usize,
    Vector: Operations,
    Hasher: Hash,
    Scheme: Variant,
>(
    randomness: &[U8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
    let ind_cpa_keypair_randomness = &randomness[0..CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let mut public_key = [0u8; PUBLIC_KEY_SIZE];
    let mut secret_key_serialized = [0u8.classify(); PRIVATE_KEY_SIZE];

    let mut ind_cpa_private_key = [0u8.classify(); CPA_PRIVATE_KEY_SIZE];
    let mut scratch = PolynomialRingElement::<Vector>::ZERO();
    let mut accumulator = [0i32.classify(); 256];
    let mut s_cache = [PolynomialRingElement::<Vector>::ZERO(); K];

    crate::ind_cpa::generate_keypair::<
        K,
        K_SQUARED,
        CPA_PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
        Vector,
        Hasher,
        Scheme,
    >(
        ind_cpa_keypair_randomness,
        &mut ind_cpa_private_key,
        &mut public_key,
        &mut scratch,
        &mut s_cache,
        &mut accumulator,
    );

    serialize_kem_secret_key_mut::<K, PRIVATE_KEY_SIZE, Hasher>(
        &ind_cpa_private_key,
        &public_key,
        implicit_rejection_value,
        &mut secret_key_serialized,
    );
    let private_key: MlKemPrivateKey<PRIVATE_KEY_SIZE> =
        MlKemPrivateKey::from(secret_key_serialized);

    MlKemKeyPair::from(private_key, MlKemPublicKey::from(public_key))
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
    T_AS_NTT_ENCODED_SIZE == BYTES_PER_RING_ELEMENT * K
)]
#[inline(always)]
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
    Vector: Operations,
    Hasher: Hash,
    Scheme: Variant,
>(
    public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
    randomness: &[U8; SHARED_SECRET_SIZE],
) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
    let mut processed_randomness = [0u8.classify(); 32];
    Scheme::entropy_preprocess::<K, Hasher>(randomness, &mut processed_randomness);
    let mut to_hash: [U8; 2 * H_DIGEST_SIZE] = into_padded_array(&processed_randomness);

    Hasher::H(
        // XXX: The more reasonable `public_key.as_slice().classify_ref()` does not go through Eurydice.
        public_key.value.classify().as_slice(),
        &mut to_hash[H_DIGEST_SIZE..],
    );

    let mut hashed = [0u8.classify(); G_DIGEST_SIZE];
    Hasher::G(&to_hash, &mut hashed);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    let mut ciphertext = [0u8; CIPHERTEXT_SIZE];
    let mut r_as_ntt: [PolynomialRingElement<Vector>; K] =
        core::array::from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
    let mut error_2 = PolynomialRingElement::<Vector>::ZERO();
    let mut scratch = Vector::ZERO();
    let mut accumulator = [0i32.classify(); 256];
    let mut cache = [PolynomialRingElement::<Vector>::ZERO(); K];
    let mut matrix_entry = PolynomialRingElement::<Vector>::ZERO();

    crate::ind_cpa::encrypt::<
        K,
        K_SQUARED,
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
        Vector,
        Hasher,
    >(
        public_key.as_slice(),
        &processed_randomness,
        pseudorandomness,
        &mut ciphertext,
        &mut matrix_entry,
        &mut r_as_ntt,
        &mut error_2,
        &mut scratch,
        &mut cache,
        &mut accumulator,
    );

    let ciphertext = MlKemCiphertext::from(ciphertext);
    let mut shared_secret_array = [0u8.classify(); 32];
    Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(
        shared_secret,
        &ciphertext.value,
        &mut shared_secret_array,
    );
    (ciphertext, shared_secret_array)
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
    T_AS_NTT_ENCODED_SIZE == BYTES_PER_RING_ELEMENT * K &&
    CIPHERTEXT_SIZE == K * 32 * VECTOR_U_COMPRESSION_FACTOR + 32 * VECTOR_V_COMPRESSION_FACTOR
)]
#[inline(always)]
pub(crate) fn decapsulate<
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
    Vector: Operations,
    Hasher: Hash,
    Scheme: Variant,
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
) -> MlKemSharedSecret {
    let (ind_cpa_secret_key, ind_cpa_public_key, ind_cpa_public_key_hash, implicit_rejection_value) =
        unpack_private_key::<CPA_SECRET_KEY_SIZE, PUBLIC_KEY_SIZE>(&private_key.value);

    let mut decrypted = [0u8.classify(); 32];
    let mut scratch = Vector::ZERO();
    let mut accumulator = [0i32.classify(); 256];

    crate::ind_cpa::decrypt::<
        K,
        CIPHERTEXT_SIZE,
        C1_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
        Vector,
    >(
        ind_cpa_secret_key,
        &ciphertext.value,
        &mut decrypted,
        &mut scratch,
        &mut accumulator,
    );

    let mut to_hash: [U8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ind_cpa_public_key_hash.classify_ref());

    let mut hashed = [0u8.classify(); G_DIGEST_SIZE];
    Hasher::G(&to_hash, &mut hashed);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    let mut to_hash: [U8; IMPLICIT_REJECTION_HASH_INPUT_SIZE] =
        into_padded_array(implicit_rejection_value);

    // XXX: The more reasonable `ciphertext.as_slice().classify_ref()` does not go through Eurydice.
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ciphertext.value.classify().as_slice());
    let mut implicit_rejection_shared_secret = [0u8.classify(); SHARED_SECRET_SIZE];
    Hasher::PRF::<SHARED_SECRET_SIZE>(&to_hash, &mut implicit_rejection_shared_secret);

    let mut expected_ciphertext = [0u8; CIPHERTEXT_SIZE];
    let mut r_as_ntt: [PolynomialRingElement<Vector>; K] =
        core::array::from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
    let mut error_2 = PolynomialRingElement::<Vector>::ZERO();

    let mut cache = [PolynomialRingElement::<Vector>::ZERO(); K];

    let mut matrix_entry = PolynomialRingElement::<Vector>::ZERO();

    crate::ind_cpa::encrypt::<
        K,
        K_SQUARED,
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
        Vector,
        Hasher,
    >(
        ind_cpa_public_key,
        &decrypted,
        pseudorandomness,
        &mut expected_ciphertext,
        &mut matrix_entry,
        &mut r_as_ntt,
        &mut error_2,
        &mut scratch,
        &mut cache,
        &mut accumulator,
    );

    let mut implicit_rejection_shared_secret_kdf = [0u8.classify(); SHARED_SECRET_SIZE];
    Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(
        &implicit_rejection_shared_secret,
        &ciphertext.value,
        &mut implicit_rejection_shared_secret_kdf,
    );
    let mut shared_secret_kdf = [0u8.classify(); SHARED_SECRET_SIZE];
    Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(
        shared_secret,
        &ciphertext.value,
        &mut shared_secret_kdf,
    );

    let mut shared_secret = [0u8.classify(); 32];
    compare_ciphertexts_select_shared_secret_in_constant_time(
        // XXX: The more reasonable `ciphertext.as_slice().classify_ref()` does not go through Eurydice.
        ciphertext.value.classify().as_slice(),
        expected_ciphertext.classify().as_slice(),
        &shared_secret_kdf,
        &implicit_rejection_shared_secret_kdf,
        &mut shared_secret,
    );
    shared_secret
}
