//! Spec-internal property tests for `hacspec_ml_kem`.
//!
//! These tests exercise the spec without any reference to a concrete
//! implementation. They check that the spec itself is self-consistent:
//! serialization roundtrips, NTT/iNTT roundtrips, CBD ranges, and
//! IND-CPA encrypt/decrypt roundtrip.
//!
//! Spec ↔ impl byte equality is asserted on the impl side
//! (`libcrux-iot/ml-kem/tests/cross_spec.rs`) — keeping these spec-only
//! tests here means the spec crate is portable (no `libcrux_iot_*` deps).

// ---------------------------------------------------------------------------
// Layer 1: Serialization / Compression (spec-side unit tests)
// ---------------------------------------------------------------------------

mod serialization {
    use hacspec_ml_kem::compress::*;
    use hacspec_ml_kem::parameters::*;
    use hacspec_ml_kem::serialize::*;

    /// byte_encode then byte_decode is identity for d < 12.
    #[test]
    fn byte_encode_decode_roundtrip() {
        for d in [1usize, 4, 5, 10, 11] {
            let poly: Polynomial = createi(|i| FieldElement::new((i as u16 * 7 + 3) % (1u16 << d)));
            match d {
                1 => {
                    let encoded = byte_encode::<32, 256>(poly, 1);
                    let decoded = byte_decode::<32, 256>(&encoded, 1);
                    assert_eq!(poly, decoded, "roundtrip failed for d=1");
                }
                4 => {
                    let encoded = byte_encode::<128, 1024>(poly, 4);
                    let decoded = byte_decode::<128, 1024>(&encoded, 4);
                    assert_eq!(poly, decoded, "roundtrip failed for d=4");
                }
                5 => {
                    let encoded = byte_encode::<160, 1280>(poly, 5);
                    let decoded = byte_decode::<160, 1280>(&encoded, 5);
                    assert_eq!(poly, decoded, "roundtrip failed for d=5");
                }
                10 => {
                    let encoded = byte_encode::<320, 2560>(poly, 10);
                    let decoded = byte_decode::<320, 2560>(&encoded, 10);
                    assert_eq!(poly, decoded, "roundtrip failed for d=10");
                }
                11 => {
                    let encoded = byte_encode::<352, 2816>(poly, 11);
                    let decoded = byte_decode::<352, 2816>(&encoded, 11);
                    assert_eq!(poly, decoded, "roundtrip failed for d=11");
                }
                _ => unreachable!(),
            }
        }
    }

    /// byte_encode(12) then byte_decode(12) reduces mod q.
    #[test]
    fn byte_encode_decode_12_roundtrip() {
        let poly: Polynomial = createi(|i| FieldElement::new((i as u16 * 13) % FIELD_MODULUS));
        let encoded = byte_encode::<384, 3072>(poly, 12);
        let decoded = byte_decode::<384, 3072>(&encoded, 12);
        assert_eq!(poly, decoded);
    }

    /// compress then decompress roundtrip preserves identity on decompressed values.
    #[test]
    fn compress_decompress_roundtrip() {
        for d in [1usize, 4, 5, 10, 11] {
            let upper = 1u16 << d;
            let poly: Polynomial = createi(|i| FieldElement::new((i as u16) % upper));
            let compressed = compress(poly, d);
            let decompressed = decompress(compressed, d);
            let recompressed = compress(decompressed, d);
            assert_eq!(
                compressed, recompressed,
                "compress(decompress(x)) != x for d={d}"
            );
        }
    }

    /// compress_then_serialize_message roundtrip.
    #[test]
    fn message_serialize_roundtrip() {
        let msg_bytes = [0xABu8; 32];
        let poly = deserialize_then_decompress_message(&msg_bytes);
        let reencoded = compress_then_serialize_message(poly);
        assert_eq!(msg_bytes, reencoded);
    }
}

// ---------------------------------------------------------------------------
// Layer 2: NTT (spec-side unit tests)
// ---------------------------------------------------------------------------

mod ntt_tests {
    use hacspec_ml_kem::invert_ntt::ntt_inverse;
    use hacspec_ml_kem::ntt::*;
    use hacspec_ml_kem::parameters::*;

    /// NTT then inverse NTT is identity.
    #[test]
    fn ntt_roundtrip() {
        for seed in [0u16, 42, 1000] {
            let poly: Polynomial = createi(|i| {
                FieldElement::new(((i as u16).wrapping_mul(seed).wrapping_add(7)) % FIELD_MODULUS)
            });
            let ntt_poly = vector_ntt([poly])[0];
            let recovered = ntt_inverse(ntt_poly);
            assert_eq!(poly, recovered, "NTT roundtrip failed for seed={seed}");
        }
    }

    /// NTT multiplication corresponds to polynomial multiplication.
    /// Test: NTT(1) * NTT(1) should yield NTT(1) since 1*1=1 in R_q.
    #[test]
    fn ntt_multiply_one_times_one() {
        let mut one = [FieldElement::new(0); 256];
        one[0] = FieldElement::new(1);

        let one_ntt = vector_ntt([one])[0];
        let product_ntt = multiply_ntts(&one_ntt, &one_ntt);
        let product = ntt_inverse(product_ntt);

        assert_eq!(product, one, "1 * 1 should equal 1");
    }
}

// ---------------------------------------------------------------------------
// Layer 3: Sampling (spec-side unit tests)
// ---------------------------------------------------------------------------

mod sampling_tests {
    use hacspec_ml_kem::parameters::*;
    use hacspec_ml_kem::sampling::*;

    /// CBD with eta=2: all coefficients should be in {0, 1, 2, 3327, 3328}.
    #[test]
    fn cbd_eta2_range() {
        let bytes = [0x55u8; 128]; // deterministic pattern
        let poly = sample_poly_cbd::<128, 1024>(2, &bytes);
        for (i, coeff) in poly.iter().enumerate() {
            assert!(
                coeff.val <= 2 || coeff.val >= FIELD_MODULUS - 2,
                "CBD eta=2 coefficient {} out of range: {}",
                i,
                coeff.val
            );
        }
    }

    /// CBD with eta=3: all coefficients should be in {0,1,2,3, 3326,3327,3328}.
    #[test]
    fn cbd_eta3_range() {
        let bytes = [0xAAu8; 192]; // deterministic pattern
        let poly = sample_poly_cbd::<192, 1536>(3, &bytes);
        for (i, coeff) in poly.iter().enumerate() {
            assert!(
                coeff.val <= 3 || coeff.val >= FIELD_MODULUS - 3,
                "CBD eta=3 coefficient {} out of range: {}",
                i,
                coeff.val
            );
        }
    }

    /// Rejection sampling: all-zero input should produce all-zero polynomial.
    #[test]
    fn rejection_sampling_zeros() {
        let bytes = [0u8; 840];
        let poly = sample_ntt::<70, 560, 840, 6720>(bytes).unwrap();
        for coeff in poly.iter() {
            assert_eq!(coeff.val, 0);
        }
    }
}

// ---------------------------------------------------------------------------
// Layer 4: IND-CPA (spec-side unit tests via byte comparison)
// ---------------------------------------------------------------------------

mod ind_cpa_tests {
    use hacspec_ml_kem::{self as spec, *};

    /// IND-CPA encrypt then decrypt roundtrip (spec-only, verifying spec correctness).
    #[test]
    fn spec_encrypt_decrypt_roundtrip() {
        let seed = [42u8; 32];
        let (ek, dk) = spec::ind_cpa::generate_keypair::<
            3,
            { ML_KEM_768_EK_SIZE },
            { ML_KEM_768_DK_PKE_SIZE },
        >(&ML_KEM_768, &seed)
        .unwrap();

        let message = [0xABu8; 32];
        let randomness = [0xCDu8; 32];
        let ct = spec::ind_cpa::encrypt::<
            3,
            { ML_KEM_768_U_SIZE },
            { ML_KEM_768_V_SIZE },
            { ML_KEM_768_CT_SIZE },
        >(&ML_KEM_768, &ek, &message, &randomness)
        .unwrap();

        let decrypted = spec::ind_cpa::decrypt::<3>(&ML_KEM_768, &dk, &ct);
        assert_eq!(decrypted, message);
    }
}
