use crate::{
    constant_time_ops::compare_ciphertexts_select_shared_secret_in_constant_time,
    constants::{
        ranked_bytes_per_ring_element, CPA_PKE_KEY_GENERATION_SEED_SIZE, G_DIGEST_SIZE,
        H_DIGEST_SIZE, SHARED_SECRET_SIZE,
    },
    hash_functions::Hash,
    ind_cpa::serialize_public_key_mut,
    polynomial::PolynomialRingElement,
    serialize::deserialize_ring_elements_reduced,
    types::*,
    utils::into_padded_array,
    variant::*,
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
pub type MlKemSharedSecret = [u8; SHARED_SECRET_SIZE];

/// This module instantiates the functions in this file and multiplexes between
/// different implementations at runtime.
#[cfg(not(eurydice))]
pub(crate) mod multiplexing;

/// This module instantiates the functions in this file for each platform.
/// To use these, runtime checks must be performed before calling them.
pub(crate) mod instantiations;

/// Serialize the secret key.

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $SERIALIZED_KEY_LEN == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\
    ${private_key.len()} == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\
    ${public_key.len()} == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    ${implicit_rejection_value.len()} == Spec.MLKEM.v_SHARED_SECRET_SIZE"#))]
#[hax_lib::ensures(|result| fstar!(r#"${serialized}_future == Seq.append $private_key (
                                              Seq.append $public_key (
                                              Seq.append (Spec.Utils.v_H $public_key) 
                                                  $implicit_rejection_value))"#))]
fn serialize_kem_secret_key_mut<const K: usize, const SERIALIZED_KEY_LEN: usize, Hasher: Hash>(
    private_key: &[u8],
    public_key: &[u8],
    implicit_rejection_value: &[u8],
    serialized: &mut [u8; SERIALIZED_KEY_LEN],
) {
    let mut pointer = 0;
    serialized[pointer..pointer + private_key.len()].copy_from_slice(private_key);
    pointer += private_key.len();
    serialized[pointer..pointer + public_key.len()].copy_from_slice(public_key);
    pointer += public_key.len();
    Hasher::H(
        public_key,
        &mut serialized[pointer..pointer + H_DIGEST_SIZE],
    );
    pointer += H_DIGEST_SIZE;
    serialized[pointer..pointer + implicit_rejection_value.len()]
        .copy_from_slice(implicit_rejection_value);

    hax_lib::fstar!(
   "let open Spec.Utils in
    assert (Seq.slice serialized 0 (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K)) `Seq.equal` $private_key);
    assert (Seq.slice serialized (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K))
                            (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +! Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K)) `Seq.equal` $public_key);
    assert (Seq.slice serialized (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +!
                                            Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K))
                            (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +!
                                            Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K +!
                                            Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE))
            `Seq.equal` Libcrux_ml_kem.Hash_functions.f_H #$:Hasher #$K $public_key);
    assert (Seq.slice serialized (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +!
                                            Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K +!
                                            Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE))
                            (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +!
                                            Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K +!
                                            Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE +!
                                            Spec.MLKEM.v_SHARED_SECRET_SIZE))
            == $implicit_rejection_value);
    lemma_slice_append_4 serialized $private_key $public_key (Libcrux_ml_kem.Hash_functions.f_H #$:Hasher #$K $public_key) $implicit_rejection_value"
    );
}

/// Validate an ML-KEM public key.
///
/// This implements the Modulus check in 7.2 2.
/// Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
/// `public_key` type.
#[inline(always)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CCA_PUBLIC_KEY_SIZE $K"#))]
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
#[hax_lib::fstar::options("--z3rlimit 300")]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K"#))]
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
#[hax_lib::fstar::options("--z3rlimit 300")]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K"#))]
pub(crate) fn validate_private_key_only<
    const K: usize,
    const SECRET_KEY_SIZE: usize,
    Hasher: Hash,
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
) -> bool {
    // Eurydice can't access values directly on the types. We need to go to the
    // `value` directly.
    let mut t = [0u8; H_DIGEST_SIZE];
    Hasher::H(&private_key.value[384 * K..768 * K + 32], &mut t);
    let expected = &private_key.value[768 * K + 32..768 * K + 64];
    t == expected
}

/// Packed API
///
/// Generate a key pair.
///
/// Depending on the `Vector` and `Hasher` used, this requires different hardware
/// features
#[hax_lib::fstar::options("--z3rlimit 300")]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $CPA_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\
    $PRIVATE_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K"#))]
#[hax_lib::ensures(|result| fstar!(r#"let (expected, valid) = Spec.MLKEM.ind_cca_generate_keypair $K $randomness in
                                    valid ==> (${result}.f_sk.f_value, ${result}.f_pk.f_value) == expected"#))]
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
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
    let ind_cpa_keypair_randomness = &randomness[0..CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let mut public_key = [0u8; PUBLIC_KEY_SIZE];
    let mut secret_key_serialized = [0u8; PRIVATE_KEY_SIZE];

    let mut ind_cpa_private_key = [0u8; CPA_PRIVATE_KEY_SIZE];
    let mut scratch = PolynomialRingElement::<Vector>::ZERO();
    let mut accumulator = [0i32; 256];
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

#[hax_lib::fstar::options("--z3rlimit 300")]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\
    $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\
    $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\
    $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR  $K /\
    $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR  $K /\
    $C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
    $ETA2 == Spec.MLKEM.v_ETA2 $K /\
    $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K"#))]
#[hax_lib::ensures(|result| fstar!(r#"let (expected, valid) = Spec.MLKEM.ind_cca_encapsulate $K ${public_key}.f_value $randomness in
                                    valid ==> (${result}._1.f_value, ${result}._2) == expected"#))]
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
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
    let mut processed_randomness = [0u8; 32];
    Scheme::entropy_preprocess::<K, Hasher>(&randomness, &mut processed_randomness);
    let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&processed_randomness);

    hax_lib::fstar!(r#"eq_intro (Seq.slice $to_hash 0 32) $randomness"#);
    Hasher::H(public_key.as_slice(), &mut to_hash[H_DIGEST_SIZE..]);

    hax_lib::fstar!(
        "assert (Seq.slice to_hash 0 (v $H_DIGEST_SIZE) == $randomness);
        lemma_slice_append $to_hash $randomness (Spec.Utils.v_H ${public_key}.f_value);
        assert ($to_hash == concat $randomness (Spec.Utils.v_H ${public_key}.f_value))"
    );
    let mut hashed = [0u8; G_DIGEST_SIZE];
    Hasher::G(&to_hash, &mut hashed);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    let mut ciphertext = [0u8; CIPHERTEXT_SIZE];
    let mut r_as_ntt: [PolynomialRingElement<Vector>; K] =
        core::array::from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
    let mut error_2 = PolynomialRingElement::<Vector>::ZERO();
    let mut scratch = PolynomialRingElement::<Vector>::ZERO();
    let mut accumulator = [0i32; 256];
    let mut cache = [PolynomialRingElement::<Vector>::ZERO(); K];
    let mut t_as_ntt = [PolynomialRingElement::<Vector>::ZERO(); K];
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
        processed_randomness,
        pseudorandomness,
        &mut ciphertext,
        &mut matrix_entry,
        &mut t_as_ntt,
        &mut r_as_ntt,
        &mut error_2,
        &mut scratch,
        &mut cache,
        &mut accumulator,
    );

    let ciphertext = MlKemCiphertext::from(ciphertext);
    let mut shared_secret_array = [0u8; 32];
    Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(shared_secret, &ciphertext, &mut shared_secret_array);
    (ciphertext, shared_secret_array)
}

/// This code verifies on some machines, runs out of memory on others
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::fstar::options("--z3rlimit 500")]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\
    $CPA_SECRET_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\
    $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\
    $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\
    $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\
    $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR  $K /\
    $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR  $K /\
    $C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
    $ETA2 == Spec.MLKEM.v_ETA2 $K /\
    $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K /\
    $IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE $K"#))]
#[hax_lib::ensures(|result| fstar!(r#"let (expected, valid) = Spec.MLKEM.ind_cca_decapsulate $K ${private_key}.f_value ${ciphertext}.f_value in
                                    valid ==> $result == expected"#))]
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
    hax_lib::fstar!(
        r#"assert (v $CIPHERTEXT_SIZE == v $IMPLICIT_REJECTION_HASH_INPUT_SIZE - v $SHARED_SECRET_SIZE)"#
    );
    let (ind_cpa_secret_key, ind_cpa_public_key, ind_cpa_public_key_hash, implicit_rejection_value) =
        unpack_private_key::<CPA_SECRET_KEY_SIZE, PUBLIC_KEY_SIZE>(&private_key.value);

    hax_lib::fstar!(
        r#"assert ($ind_cpa_secret_key == slice ${private_key}.f_value (sz 0) $CPA_SECRET_KEY_SIZE);
        assert ($ind_cpa_public_key == slice ${private_key}.f_value $CPA_SECRET_KEY_SIZE ($CPA_SECRET_KEY_SIZE +! $PUBLIC_KEY_SIZE));
        assert ($ind_cpa_public_key_hash == slice ${private_key}.f_value ($CPA_SECRET_KEY_SIZE +! $PUBLIC_KEY_SIZE)
            ($CPA_SECRET_KEY_SIZE +! $PUBLIC_KEY_SIZE +! Spec.MLKEM.v_H_DIGEST_SIZE));
        assert ($implicit_rejection_value == slice ${private_key}.f_value ($CPA_SECRET_KEY_SIZE +! $PUBLIC_KEY_SIZE +! Spec.MLKEM.v_H_DIGEST_SIZE)
            (length ${private_key}.f_value))"#
    );
    let mut decrypted = [0u8; 32];
    let mut scratch = PolynomialRingElement::<Vector>::ZERO();
    let mut accumulator = [0i32; 256];

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

    let mut to_hash: [u8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
    hax_lib::fstar!(r#"eq_intro (Seq.slice $to_hash 0 32) $decrypted"#);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ind_cpa_public_key_hash);

    hax_lib::fstar!(
        r#"lemma_slice_append to_hash $decrypted $ind_cpa_public_key_hash;
        assert ($decrypted == Spec.MLKEM.ind_cpa_decrypt $K $ind_cpa_secret_key ${ciphertext}.f_value);
        assert ($to_hash == concat $decrypted $ind_cpa_public_key_hash)"#
    );
    let mut hashed = [0u8; G_DIGEST_SIZE];
    Hasher::G(&to_hash, &mut hashed);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    hax_lib::fstar!(
        r#"assert (($shared_secret , $pseudorandomness) == split $hashed $SHARED_SECRET_SIZE);
        assert (length $implicit_rejection_value = $SECRET_KEY_SIZE -! $CPA_SECRET_KEY_SIZE -! $PUBLIC_KEY_SIZE -! $H_DIGEST_SIZE);
        assert (length $implicit_rejection_value = Spec.MLKEM.v_SHARED_SECRET_SIZE);
        assert (Spec.MLKEM.v_SHARED_SECRET_SIZE <=. Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE $K)"#
    );
    let mut to_hash: [u8; IMPLICIT_REJECTION_HASH_INPUT_SIZE] =
        into_padded_array(implicit_rejection_value);
    hax_lib::fstar!(r#"eq_intro (Seq.slice $to_hash 0 32) $implicit_rejection_value"#);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ciphertext.as_ref());
    hax_lib::fstar!(
        "assert_norm (pow2 32 == 0x100000000);
        assert (v (sz 32) < pow2 32);
        assert (i4.f_PRF_pre (sz 32) $to_hash);
        lemma_slice_append $to_hash $implicit_rejection_value ${ciphertext}.f_value"
    );
    let mut implicit_rejection_shared_secret = [0u8; SHARED_SECRET_SIZE];
    Hasher::PRF::<32>(&to_hash, &mut implicit_rejection_shared_secret);

    hax_lib::fstar!(
        "assert ($implicit_rejection_shared_secret == Spec.Utils.v_PRF (sz 32) $to_hash);
        assert (Seq.length $ind_cpa_public_key == v $PUBLIC_KEY_SIZE)"
    );
    let mut expected_ciphertext = [0u8; CIPHERTEXT_SIZE];
    let mut r_as_ntt: [PolynomialRingElement<Vector>; K] =
        core::array::from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
    let mut error_2 = PolynomialRingElement::<Vector>::ZERO();

    let mut cache = [PolynomialRingElement::<Vector>::ZERO(); K];
    let mut t_as_ntt = [PolynomialRingElement::<Vector>::ZERO(); K];

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
        decrypted,
        pseudorandomness,
        &mut expected_ciphertext,
        &mut matrix_entry,
        &mut t_as_ntt,
        &mut r_as_ntt,
        &mut error_2,
        &mut scratch,
        &mut cache,
        &mut accumulator,
    );

    let mut implicit_rejection_shared_secret_kdf = [0u8; SHARED_SECRET_SIZE];
    Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(
        &implicit_rejection_shared_secret,
        ciphertext,
        &mut implicit_rejection_shared_secret_kdf,
    );
    let mut shared_secret_kdf = [0u8; SHARED_SECRET_SIZE];
    Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(shared_secret, ciphertext, &mut shared_secret_kdf);

    let mut shared_secret = [0u8; 32];
    compare_ciphertexts_select_shared_secret_in_constant_time(
        ciphertext.as_ref(),
        &expected_ciphertext,
        &shared_secret_kdf,
        &implicit_rejection_shared_secret_kdf,
        &mut shared_secret,
    );
    shared_secret
}
