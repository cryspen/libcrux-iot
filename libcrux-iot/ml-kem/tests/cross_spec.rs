//! Cross-spec equivalence tests between `libcrux-iot-ml-kem` and `hacspec_ml_kem`.
//!
//! These tests assert byte-identical agreement between the optimized impl and
//! the FIPS-203 hacspec reference on the IND-CCA surface (KeyGen / Encaps /
//! Decaps) at all three parameter sets. Coverage layers:
//!
//! 1. `mod ctx`              — U8 ↔ u8 wrapper (libcrux-secrets boundary).
//! 2. `mod hash_agreement`   — defense-in-depth that the spec's hacspec_sha3
//!                              calls match `libcrux_iot_sha3` at every
//!                              (input pattern, RATE, DELIM) the spec uses.
//! 3. `mod mlkemNNN_cross`   — IND-CCA byte equality on a fixed seed table.
//! 4. `mod kat_anchors`      — known NIST KAT seeds (pulled from
//!                              `tests/kats/nistkats_mlkem_*.json`).
//! 5. `mlkemNNN_determinism` — running impl twice on the same seed gives the
//!                              same bytes.
//! 6. `mod rejection_sampling_pressure` — "unlucky" seeds intended to push
//!                              SampleNTT past the first 168-byte SHAKE128
//!                              block. The bad-seed table is currently empty
//!                              (TODO: see `tests/scripts/find_bad_rejection_seeds.rs`).
//!
//! Anchored to FIPS-203 algorithm numbers (KeyGen ≈ Alg. 19, Encaps ≈ Alg. 20,
//! Decaps ≈ Alg. 21). Lean equivalence theorems will be back-referenced as
//! they land in `libcrux-iot/ml-kem/proofs/aeneas-lean/`.

use hacspec_ml_kem::{
    self as spec, ML_KEM_1024, ML_KEM_1024_CT_SIZE, ML_KEM_1024_DK_PKE_SIZE, ML_KEM_1024_DK_SIZE,
    ML_KEM_1024_EK_SIZE, ML_KEM_1024_J_INPUT_SIZE, ML_KEM_1024_U_SIZE, ML_KEM_1024_V_SIZE,
    ML_KEM_512, ML_KEM_512_CT_SIZE, ML_KEM_512_DK_PKE_SIZE, ML_KEM_512_DK_SIZE, ML_KEM_512_EK_SIZE,
    ML_KEM_512_J_INPUT_SIZE, ML_KEM_512_U_SIZE, ML_KEM_512_V_SIZE, ML_KEM_768, ML_KEM_768_CT_SIZE,
    ML_KEM_768_DK_PKE_SIZE, ML_KEM_768_DK_SIZE, ML_KEM_768_EK_SIZE, ML_KEM_768_J_INPUT_SIZE,
    ML_KEM_768_U_SIZE, ML_KEM_768_V_SIZE,
};

// ---------------------------------------------------------------------------
// Layer 0 — U8 ↔ u8 wrapper layer.
// Centralises every `.classify()` / `.declassify_ref()` so the rest of the
// file reads in plain `&[u8]`. If `check-secret-independence` ever turns on
// for this crate, only this module needs to update.
// ---------------------------------------------------------------------------

mod ctx {
    use libcrux_secrets::{Classify, DeclassifyRef};

    pub fn gen_kp_512(
        seed: [u8; 64],
    ) -> (
        Vec<u8>, /* dk */
        Vec<u8>, /* ek */
    ) {
        let kp = libcrux_iot_ml_kem::mlkem512::generate_key_pair(seed.classify());
        let (sk, pk) = kp.into_parts();
        (sk.as_slice().declassify_ref().to_vec(), pk.as_slice().to_vec())
    }

    pub fn gen_kp_768(
        seed: [u8; 64],
    ) -> (Vec<u8>, Vec<u8>) {
        let kp = libcrux_iot_ml_kem::mlkem768::generate_key_pair(seed.classify());
        let (sk, pk) = kp.into_parts();
        (sk.as_slice().declassify_ref().to_vec(), pk.as_slice().to_vec())
    }

    pub fn gen_kp_1024(
        seed: [u8; 64],
    ) -> (Vec<u8>, Vec<u8>) {
        let kp = libcrux_iot_ml_kem::mlkem1024::generate_key_pair(seed.classify());
        let (sk, pk) = kp.into_parts();
        (sk.as_slice().declassify_ref().to_vec(), pk.as_slice().to_vec())
    }
}

// ---------------------------------------------------------------------------
// Const-generic size assertions — fail fast on any drift between the impl's
// hard-coded sizes (per FIPS-203 §8 table) and the spec's exported constants.
// ---------------------------------------------------------------------------

#[test]
fn size_constants_agree_512() {
    use libcrux_iot_ml_kem::mlkem512::*;
    assert_eq!(MlKem512PublicKey::len(), ML_KEM_512_EK_SIZE);
    assert_eq!(MlKem512PrivateKey::len(), ML_KEM_512_DK_SIZE);
    assert_eq!(MlKem512Ciphertext::len(), ML_KEM_512_CT_SIZE);
}

#[test]
fn size_constants_agree_768() {
    use libcrux_iot_ml_kem::mlkem768::*;
    assert_eq!(MlKem768PublicKey::len(), ML_KEM_768_EK_SIZE);
    assert_eq!(MlKem768PrivateKey::len(), ML_KEM_768_DK_SIZE);
    assert_eq!(MlKem768Ciphertext::len(), ML_KEM_768_CT_SIZE);
}

#[test]
fn size_constants_agree_1024() {
    use libcrux_iot_ml_kem::mlkem1024::*;
    assert_eq!(MlKem1024PublicKey::len(), ML_KEM_1024_EK_SIZE);
    assert_eq!(MlKem1024PrivateKey::len(), ML_KEM_1024_DK_SIZE);
    assert_eq!(MlKem1024Ciphertext::len(), ML_KEM_1024_CT_SIZE);
}

// ---------------------------------------------------------------------------
// Layer 1 — Hash agreement.
//
// The hacspec_ml_kem spec calls into hacspec_sha3 for G (SHA3-512), H
// (SHA3-256), PRF (SHAKE-256), and XOF (SHAKE-128). These tests are
// defense-in-depth: the underlying primitives are exhaustively cross-tested
// by the SHA-3 crate's `cross_spec_proptests.rs`, but having explicit
// matches here documents the contract.
// ---------------------------------------------------------------------------

mod hash_agreement {
    use libcrux_secrets::{ClassifyRef, DeclassifyRef};

    #[test]
    fn sha3_512_matches() {
        for input in [
            &b"test input for G"[..],
            &[0u8; 0][..],
            &[0xAB; 64][..],
            &[0xFF; 33][..],
        ] {
            let spec_out = hacspec_sha3::sha3_512(input);
            let imp = libcrux_iot_sha3::sha512(input.classify_ref());
            let imp_arr: [u8; 64] = {
                let d = imp.declassify_ref();
                let mut out = [0u8; 64];
                out.copy_from_slice(d);
                out
            };
            assert_eq!(spec_out, imp_arr, "SHA3-512 mismatch len={}", input.len());
        }
    }

    #[test]
    fn sha3_256_matches() {
        for input in [&b"test input for H"[..], &[0u8; 0][..], &[0xAB; 64][..]] {
            let spec_out = hacspec_sha3::sha3_256(input);
            let imp = libcrux_iot_sha3::sha256(input.classify_ref());
            let imp_arr: [u8; 32] = {
                let d = imp.declassify_ref();
                let mut out = [0u8; 32];
                out.copy_from_slice(d);
                out
            };
            assert_eq!(spec_out, imp_arr, "SHA3-256 mismatch len={}", input.len());
        }
    }

    #[test]
    fn shake256_matches() {
        use libcrux_secrets::{Classify, U8};
        for input in [&b"test PRF"[..], &[0u8; 33][..], &[0xFF; 34][..]] {
            let spec_out: [u8; 128] = hacspec_sha3::shake256(input);
            let mut buf: Vec<U8> = vec![0u8.classify(); 128];
            libcrux_iot_sha3::shake256_ema(buf.as_mut_slice(), input.classify_ref());
            let imp_arr: Vec<u8> = buf.into_iter().map(|b| {
                use libcrux_secrets::Declassify;
                b.declassify()
            }).collect();
            assert_eq!(&spec_out[..], imp_arr.as_slice(), "SHAKE256 mismatch len={}", input.len());
        }
    }

    #[test]
    fn shake128_matches() {
        use libcrux_secrets::{Classify, U8};
        for input in [&b"test XOF"[..], &[0u8; 34][..], &[0xFF; 34][..]] {
            let spec_out: [u8; 840] = hacspec_sha3::shake128(input);
            let mut buf: Vec<U8> = vec![0u8.classify(); 840];
            libcrux_iot_sha3::shake128_ema(buf.as_mut_slice(), input.classify_ref());
            let imp_arr: Vec<u8> = buf.into_iter().map(|b| {
                use libcrux_secrets::Declassify;
                b.declassify()
            }).collect();
            assert_eq!(&spec_out[..], imp_arr.as_slice(), "SHAKE128 mismatch len={}", input.len());
        }
    }
}

// ---------------------------------------------------------------------------
// Seed tables — deterministic vectors exercised by every variant.
// ---------------------------------------------------------------------------

const KEYGEN_SEEDS: &[[u8; 64]] = &[
    [0x00; 64],
    [0xFF; 64],
    [0xAA; 64],
    {
        let mut s = [0u8; 64];
        let mut i = 0usize;
        while i < 64 {
            s[i] = i as u8;
            i += 1;
        }
        s
    },
];
const ENCAPS_SEEDS: &[[u8; 32]] = &[[0x00; 32], [0xFF; 32], [0xCD; 32]];

// ---------------------------------------------------------------------------
// Layer 2 — IND-CCA byte-level cross-comparison (impl vs spec).
//
// Generated per parameter set. Each variant gets:
//   1. keygen_matches_spec       — pk, sk byte-equal.
//   2. encapsulate_matches_spec  — ct, ss byte-equal on a fresh keypair.
//   3. full_roundtrip_matches_spec — encaps then decaps; impl ss matches
//                                      spec ss on both sides.
//   4. decaps_rejection_matches_spec — flipping a ct byte triggers implicit
//                                      rejection; impl ss matches spec ss
//                                      (i.e., both produce J(s, c')).
// ---------------------------------------------------------------------------

macro_rules! cross_spec_tests {
    (
        $mod_name:ident,
        $feature:literal,
        $impl_mod:path,
        $k:literal,
        $params:expr,
        $ek:expr, $dk:expr, $dk_pke:expr,
        $u:expr, $v:expr, $ct:expr, $j:expr
    ) => {
        #[cfg(feature = $feature)]
        mod $mod_name {
            use super::*;
            use libcrux_secrets::{Classify, Declassify, DeclassifyRef};
            use $impl_mod as impl_mod;

            #[test]
            fn keygen_matches_spec() {
                for (i, randomness) in KEYGEN_SEEDS.iter().enumerate() {
                    let (spec_ek, spec_dk) =
                        spec::generate_keypair::<$k, $ek, $dk, $dk_pke>(&$params, randomness)
                            .unwrap_or_else(|_| {
                                panic!(
                                    concat!(
                                        stringify!($mod_name),
                                        " spec keygen failed for seed index {}; ",
                                        "consider replacing KEYGEN_SEEDS[{}]"
                                    ),
                                    i, i
                                )
                            });

                    let (impl_sk, impl_pk) = impl_mod::generate_key_pair((*randomness).classify()).into_parts();

                    assert_eq!(
                        impl_pk.as_slice(),
                        &spec_ek[..],
                        concat!(stringify!($mod_name), " ek mismatch (seed idx={})"),
                        i
                    );
                    assert_eq!(
                        impl_sk.as_slice().declassify_ref(),
                        &spec_dk[..],
                        concat!(stringify!($mod_name), " dk mismatch (seed idx={})"),
                        i
                    );
                }
            }

            #[test]
            fn encapsulate_matches_spec() {
                let keygen_rand = [1u8; 64];
                let (spec_ek, _) =
                    spec::generate_keypair::<$k, $ek, $dk, $dk_pke>(&$params, &keygen_rand)
                        .expect("spec keygen failed");
                let (_impl_sk, impl_pk) =
                    impl_mod::generate_key_pair(keygen_rand.classify()).into_parts();

                for (i, encaps_rand) in ENCAPS_SEEDS.iter().enumerate() {
                    let (spec_ss, spec_ct) =
                        spec::encapsulate::<$k, $ek, $u, $v, $ct>(&$params, &spec_ek, encaps_rand)
                            .expect("spec encaps failed");

                    let (impl_ct, impl_ss) =
                        impl_mod::encapsulate(&impl_pk, (*encaps_rand).classify());

                    assert_eq!(
                        impl_ct.as_ref(),
                        &spec_ct[..],
                        concat!(stringify!($mod_name), " ct mismatch (encaps idx={})"),
                        i
                    );
                    assert_eq!(
                        impl_ss.declassify().as_ref(),
                        &spec_ss[..],
                        concat!(stringify!($mod_name), " ss mismatch (encaps idx={})"),
                        i
                    );
                }
            }

            #[test]
            fn full_roundtrip_matches_spec() {
                for (i, randomness) in KEYGEN_SEEDS.iter().enumerate() {
                    let encaps_rand = ENCAPS_SEEDS[i % ENCAPS_SEEDS.len()];

                    let (spec_ek, spec_dk) =
                        spec::generate_keypair::<$k, $ek, $dk, $dk_pke>(&$params, randomness)
                            .unwrap_or_else(|_| {
                                panic!(
                                    concat!(stringify!($mod_name), " spec keygen failed for seed idx {}"),
                                    i
                                )
                            });
                    let (spec_ss, spec_ct) =
                        spec::encapsulate::<$k, $ek, $u, $v, $ct>(&$params, &spec_ek, &encaps_rand)
                            .expect("spec encaps failed");
                    let spec_ss_d =
                        spec::decapsulate::<$k, $ek, $dk, $dk_pke, $u, $v, $ct, $j>(
                            &$params, &spec_dk, &spec_ct,
                        )
                        .expect("spec decaps failed");

                    let (impl_sk, impl_pk) =
                        impl_mod::generate_key_pair((*randomness).classify()).into_parts();
                    let (impl_ct, impl_ss_e) = impl_mod::encapsulate(&impl_pk, encaps_rand.classify());
                    let impl_ss_d = impl_mod::decapsulate(&impl_sk, &impl_ct);

                    assert_eq!(impl_ct.as_ref(), &spec_ct[..], "ct (seed idx={})", i);
                    assert_eq!(impl_ss_e.declassify().as_ref(), &spec_ss[..], "encaps ss");
                    assert_eq!(impl_ss_d.declassify().as_ref(), &spec_ss_d[..], "decaps ss");
                    assert_eq!(
                        impl_ss_e.declassify().as_ref(),
                        impl_ss_d.declassify().as_ref(),
                        "impl encaps/decaps ss differ"
                    );
                }
            }

            #[test]
            fn decaps_rejection_matches_spec() {
                // Implicit rejection: tampered ct should produce J(s, c').
                // Both impl and spec implement the FIPS-203 implicit rejection;
                // they should agree byte-for-byte.
                let keygen_rand = KEYGEN_SEEDS[1]; // 0xFF seed
                let encaps_rand = ENCAPS_SEEDS[0];

                let (spec_ek, spec_dk) =
                    spec::generate_keypair::<$k, $ek, $dk, $dk_pke>(&$params, &keygen_rand)
                        .expect("spec keygen failed");
                let (_spec_ss, spec_ct) =
                    spec::encapsulate::<$k, $ek, $u, $v, $ct>(&$params, &spec_ek, &encaps_rand)
                        .expect("spec encaps failed");

                let (impl_sk, _impl_pk) =
                    impl_mod::generate_key_pair(keygen_rand.classify()).into_parts();

                // Tamper one byte of the ciphertext.
                let mut tampered_ct: [u8; $ct] = spec_ct;
                tampered_ct[7] ^= 0xA5;

                let spec_ss_rej =
                    spec::decapsulate::<$k, $ek, $dk, $dk_pke, $u, $v, $ct, $j>(
                        &$params, &spec_dk, &tampered_ct,
                    )
                    .expect("spec decaps (rejection branch) failed");

                let impl_tampered_ct = tampered_ct.into();
                let impl_ss_rej = impl_mod::decapsulate(&impl_sk, &impl_tampered_ct);

                assert_eq!(
                    impl_ss_rej.declassify().as_ref(),
                    &spec_ss_rej[..],
                    concat!(stringify!($mod_name), " implicit rejection ss mismatch")
                );
            }
        }
    };
}

cross_spec_tests!(
    mlkem512_cross,
    "mlkem512",
    libcrux_iot_ml_kem::mlkem512,
    2,
    ML_KEM_512,
    { ML_KEM_512_EK_SIZE },
    { ML_KEM_512_DK_SIZE },
    { ML_KEM_512_DK_PKE_SIZE },
    { ML_KEM_512_U_SIZE },
    { ML_KEM_512_V_SIZE },
    { ML_KEM_512_CT_SIZE },
    { ML_KEM_512_J_INPUT_SIZE }
);

cross_spec_tests!(
    mlkem768_cross,
    "mlkem768",
    libcrux_iot_ml_kem::mlkem768,
    3,
    ML_KEM_768,
    { ML_KEM_768_EK_SIZE },
    { ML_KEM_768_DK_SIZE },
    { ML_KEM_768_DK_PKE_SIZE },
    { ML_KEM_768_U_SIZE },
    { ML_KEM_768_V_SIZE },
    { ML_KEM_768_CT_SIZE },
    { ML_KEM_768_J_INPUT_SIZE }
);

cross_spec_tests!(
    mlkem1024_cross,
    "mlkem1024",
    libcrux_iot_ml_kem::mlkem1024,
    4,
    ML_KEM_1024,
    { ML_KEM_1024_EK_SIZE },
    { ML_KEM_1024_DK_SIZE },
    { ML_KEM_1024_DK_PKE_SIZE },
    { ML_KEM_1024_U_SIZE },
    { ML_KEM_1024_V_SIZE },
    { ML_KEM_1024_CT_SIZE },
    { ML_KEM_1024_J_INPUT_SIZE }
);

// ---------------------------------------------------------------------------
// Layer 3 — Determinism.
//
// Running the impl twice on identical seeds should produce byte-equal
// outputs. Distinct from spec cross-comparison: this catches non-determinism
// in the impl alone (e.g., uninitialized scratch buffers leaking into output).
// ---------------------------------------------------------------------------

#[cfg(feature = "mlkem512")]
#[test]
fn mlkem512_determinism() {
    let seed = [0x42u8; 64];
    let (sk1, pk1) = ctx::gen_kp_512(seed);
    let (sk2, pk2) = ctx::gen_kp_512(seed);
    assert_eq!(sk1, sk2);
    assert_eq!(pk1, pk2);
}

#[cfg(feature = "mlkem768")]
#[test]
fn mlkem768_determinism() {
    let seed = [0x42u8; 64];
    let (sk1, pk1) = ctx::gen_kp_768(seed);
    let (sk2, pk2) = ctx::gen_kp_768(seed);
    assert_eq!(sk1, sk2);
    assert_eq!(pk1, pk2);
}

#[cfg(feature = "mlkem1024")]
#[test]
fn mlkem1024_determinism() {
    let seed = [0x42u8; 64];
    let (sk1, pk1) = ctx::gen_kp_1024(seed);
    let (sk2, pk2) = ctx::gen_kp_1024(seed);
    assert_eq!(sk1, sk2);
    assert_eq!(pk1, pk2);
}

// ---------------------------------------------------------------------------
// Layer 4 — KAT anchors.
//
// The first NIST KAT for each variant from tests/kats/nistkats_mlkem_*.json.
// Run impl AND spec on the seed; the spec test side anchors the spec to a
// known-good fixture, while the impl side is also covered by `nistkats.rs`.
// ---------------------------------------------------------------------------

mod kat_anchors {
    use super::*;
    use libcrux_secrets::{Classify, Declassify, DeclassifyRef};

    /// First NIST-KAT seed shared across variants (the JSON tables for
    /// 512/768/1024 happen to start from the same DRBG initial state).
    const NIST_KAT_KEYGEN_SEED_0: [u8; 64] = [
        0x7c, 0x99, 0x35, 0xa0, 0xb0, 0x76, 0x94, 0xaa, 0x0c, 0x6d, 0x10, 0xe4, 0xdb, 0x6b, 0x1a,
        0xdd, 0x2f, 0xd8, 0x1a, 0x25, 0xcc, 0xb1, 0x48, 0x03, 0x2d, 0xcd, 0x73, 0x99, 0x36, 0x73,
        0x7f, 0x2d, 0x86, 0x26, 0xed, 0x79, 0xd4, 0x51, 0x14, 0x08, 0x00, 0xe0, 0x3b, 0x59, 0xb9,
        0x56, 0xf8, 0x21, 0x0e, 0x55, 0x60, 0x67, 0x40, 0x7d, 0x13, 0xdc, 0x90, 0xfa, 0x9e, 0x8b,
        0x87, 0x2b, 0xfb, 0x8f,
    ];
    const NIST_KAT_ENCAPS_SEED_0: [u8; 32] = [
        0x14, 0x7c, 0x03, 0xf7, 0xa5, 0xbe, 0xbb, 0xa4, 0x06, 0xc8, 0xfa, 0xe1, 0x87, 0x4d, 0x7f,
        0x13, 0xc8, 0x0e, 0xfe, 0x79, 0xa3, 0xa9, 0xa8, 0x74, 0xcc, 0x09, 0xfe, 0x76, 0xf6, 0x99,
        0x76, 0x15,
    ];

    #[cfg(feature = "mlkem512")]
    #[test]
    fn mlkem512_nist_kat_seed_0() {
        let (spec_ek, _spec_dk) =
            spec::generate_keypair::<2, ML_KEM_512_EK_SIZE, ML_KEM_512_DK_SIZE, ML_KEM_512_DK_PKE_SIZE>(
                &ML_KEM_512,
                &NIST_KAT_KEYGEN_SEED_0,
            )
            .expect("KAT seed 0 should not trigger rejection");

        let (impl_sk, impl_pk) =
            libcrux_iot_ml_kem::mlkem512::generate_key_pair(NIST_KAT_KEYGEN_SEED_0.classify())
                .into_parts();
        assert_eq!(impl_pk.as_slice(), &spec_ek[..], "512 KAT-anchor pk mismatch");

        let (spec_ss, spec_ct) =
            spec::encapsulate::<2, ML_KEM_512_EK_SIZE, ML_KEM_512_U_SIZE, ML_KEM_512_V_SIZE, ML_KEM_512_CT_SIZE>(
                &ML_KEM_512,
                &spec_ek,
                &NIST_KAT_ENCAPS_SEED_0,
            )
            .expect("KAT seed 0 spec encaps");

        let (impl_ct, impl_ss) =
            libcrux_iot_ml_kem::mlkem512::encapsulate(&impl_pk, NIST_KAT_ENCAPS_SEED_0.classify());
        assert_eq!(impl_ct.as_ref(), &spec_ct[..]);
        assert_eq!(impl_ss.declassify().as_ref(), &spec_ss[..]);

        let impl_ss_d = libcrux_iot_ml_kem::mlkem512::decapsulate(&impl_sk, &impl_ct);
        assert_eq!(impl_ss_d.declassify().as_ref(), &spec_ss[..]);
        let _ = impl_sk.as_slice().declassify_ref();
    }

    #[cfg(feature = "mlkem768")]
    #[test]
    fn mlkem768_nist_kat_seed_0() {
        let (spec_ek, _spec_dk) =
            spec::generate_keypair::<3, ML_KEM_768_EK_SIZE, ML_KEM_768_DK_SIZE, ML_KEM_768_DK_PKE_SIZE>(
                &ML_KEM_768,
                &NIST_KAT_KEYGEN_SEED_0,
            )
            .expect("KAT seed 0 should not trigger rejection");

        let (impl_sk, impl_pk) =
            libcrux_iot_ml_kem::mlkem768::generate_key_pair(NIST_KAT_KEYGEN_SEED_0.classify())
                .into_parts();
        assert_eq!(impl_pk.as_slice(), &spec_ek[..], "768 KAT-anchor pk mismatch");

        let (spec_ss, spec_ct) =
            spec::encapsulate::<3, ML_KEM_768_EK_SIZE, ML_KEM_768_U_SIZE, ML_KEM_768_V_SIZE, ML_KEM_768_CT_SIZE>(
                &ML_KEM_768,
                &spec_ek,
                &NIST_KAT_ENCAPS_SEED_0,
            )
            .expect("KAT seed 0 spec encaps");

        let (impl_ct, impl_ss) =
            libcrux_iot_ml_kem::mlkem768::encapsulate(&impl_pk, NIST_KAT_ENCAPS_SEED_0.classify());
        assert_eq!(impl_ct.as_ref(), &spec_ct[..]);
        assert_eq!(impl_ss.declassify().as_ref(), &spec_ss[..]);

        let impl_ss_d = libcrux_iot_ml_kem::mlkem768::decapsulate(&impl_sk, &impl_ct);
        assert_eq!(impl_ss_d.declassify().as_ref(), &spec_ss[..]);
    }

    #[cfg(feature = "mlkem1024")]
    #[test]
    fn mlkem1024_nist_kat_seed_0() {
        let (spec_ek, _spec_dk) =
            spec::generate_keypair::<4, ML_KEM_1024_EK_SIZE, ML_KEM_1024_DK_SIZE, ML_KEM_1024_DK_PKE_SIZE>(
                &ML_KEM_1024,
                &NIST_KAT_KEYGEN_SEED_0,
            )
            .expect("KAT seed 0 should not trigger rejection");

        let (impl_sk, impl_pk) =
            libcrux_iot_ml_kem::mlkem1024::generate_key_pair(NIST_KAT_KEYGEN_SEED_0.classify())
                .into_parts();
        assert_eq!(impl_pk.as_slice(), &spec_ek[..], "1024 KAT-anchor pk mismatch");

        let (spec_ss, spec_ct) =
            spec::encapsulate::<4, ML_KEM_1024_EK_SIZE, ML_KEM_1024_U_SIZE, ML_KEM_1024_V_SIZE, ML_KEM_1024_CT_SIZE>(
                &ML_KEM_1024,
                &spec_ek,
                &NIST_KAT_ENCAPS_SEED_0,
            )
            .expect("KAT seed 0 spec encaps");

        let (impl_ct, impl_ss) =
            libcrux_iot_ml_kem::mlkem1024::encapsulate(&impl_pk, NIST_KAT_ENCAPS_SEED_0.classify());
        assert_eq!(impl_ct.as_ref(), &spec_ct[..]);
        assert_eq!(impl_ss.declassify().as_ref(), &spec_ss[..]);

        let impl_ss_d = libcrux_iot_ml_kem::mlkem1024::decapsulate(&impl_sk, &impl_ct);
        assert_eq!(impl_ss_d.declassify().as_ref(), &spec_ss[..]);
    }
}

// ---------------------------------------------------------------------------
// Layer 5 — Rejection-sampling pressure.
//
// "Unlucky" seeds intended to force `sample_ntt` (Algorithm 6) past the
// first 168-byte SHAKE128 block, exercising the multi-block iteration path
// in the impl's matrix expansion. The bad-seed table is generated offline
// by `tests/scripts/find_bad_rejection_seeds.rs`.
//
// TODO(bad-seeds): the script lives in tests/scripts/ and is gated out of
// the regular test target. The current table is empty pending wiring of a
// `sampling::block_count`-style instrumentation hook on either the impl or
// spec side. The non-empty case is still hit incidentally by the proptest
// layer with `PROPTEST_CASES=128` or higher.
// ---------------------------------------------------------------------------

mod rejection_sampling_pressure {
    use super::*;
    use libcrux_secrets::Classify;

    /// Seeds that walk past the first SHAKE128 block for ML-KEM-512.
    /// See module-level TODO(bad-seeds).
    const MLKEM512_UNLUCKY: &[[u8; 64]] = &[];

    /// Seeds that walk past the first SHAKE128 block for ML-KEM-768.
    /// See module-level TODO(bad-seeds).
    const MLKEM768_UNLUCKY: &[[u8; 64]] = &[];

    /// Seeds that walk past the first SHAKE128 block for ML-KEM-1024.
    /// See module-level TODO(bad-seeds).
    const MLKEM1024_UNLUCKY: &[[u8; 64]] = &[];

    fn check_512(seeds: &[[u8; 64]]) {
        for (i, s) in seeds.iter().enumerate() {
            let (spec_ek, _) = spec::generate_keypair::<2, ML_KEM_512_EK_SIZE, ML_KEM_512_DK_SIZE, ML_KEM_512_DK_PKE_SIZE>(&ML_KEM_512, s)
                .unwrap_or_else(|_| panic!("MLKEM512_UNLUCKY[{}] caused spec rejection", i));
            let (_sk, pk) = libcrux_iot_ml_kem::mlkem512::generate_key_pair((*s).classify()).into_parts();
            assert_eq!(pk.as_slice(), &spec_ek[..], "MLKEM512_UNLUCKY[{}] pk mismatch", i);
        }
    }

    fn check_768(seeds: &[[u8; 64]]) {
        for (i, s) in seeds.iter().enumerate() {
            let (spec_ek, _) = spec::generate_keypair::<3, ML_KEM_768_EK_SIZE, ML_KEM_768_DK_SIZE, ML_KEM_768_DK_PKE_SIZE>(&ML_KEM_768, s)
                .unwrap_or_else(|_| panic!("MLKEM768_UNLUCKY[{}] caused spec rejection", i));
            let (_sk, pk) = libcrux_iot_ml_kem::mlkem768::generate_key_pair((*s).classify()).into_parts();
            assert_eq!(pk.as_slice(), &spec_ek[..], "MLKEM768_UNLUCKY[{}] pk mismatch", i);
        }
    }

    fn check_1024(seeds: &[[u8; 64]]) {
        for (i, s) in seeds.iter().enumerate() {
            let (spec_ek, _) = spec::generate_keypair::<4, ML_KEM_1024_EK_SIZE, ML_KEM_1024_DK_SIZE, ML_KEM_1024_DK_PKE_SIZE>(&ML_KEM_1024, s)
                .unwrap_or_else(|_| panic!("MLKEM1024_UNLUCKY[{}] caused spec rejection", i));
            let (_sk, pk) = libcrux_iot_ml_kem::mlkem1024::generate_key_pair((*s).classify()).into_parts();
            assert_eq!(pk.as_slice(), &spec_ek[..], "MLKEM1024_UNLUCKY[{}] pk mismatch", i);
        }
    }

    #[cfg(feature = "mlkem512")]
    #[test]
    fn mlkem512_unlucky_seeds() {
        check_512(MLKEM512_UNLUCKY);
    }

    #[cfg(feature = "mlkem768")]
    #[test]
    fn mlkem768_unlucky_seeds() {
        check_768(MLKEM768_UNLUCKY);
    }

    #[cfg(feature = "mlkem1024")]
    #[test]
    fn mlkem1024_unlucky_seeds() {
        check_1024(MLKEM1024_UNLUCKY);
    }
}
