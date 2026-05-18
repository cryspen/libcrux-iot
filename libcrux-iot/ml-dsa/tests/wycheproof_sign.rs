// This module tests the implementation against the Wycheproof signing
// test vectors contained in [libcrux-kats](https://github.com/cryspen/libcrux/tree/main/crates/testing/kats).
//
// This set of test vectors does not cover the pre-hashed variants of
// ML-DSA.

use libcrux_iot_ml_dsa::{
    ml_dsa_44::{self, MLDSA44SigningKey},
    ml_dsa_65::{self, MLDSA65SigningKey},
    ml_dsa_87::{self, MLDSA87SigningKey},
    MLDSAKeyPair, MLDSASigningKey, SigningError,
};
use libcrux_kats::wycheproof::mldsa::{sign_noseed_schema, sign_seed_schema, ParameterSet};
use libcrux_secrets::Classify as _;

macro_rules! wycheproof_sign_test {
    ($name:ident, $test_name:expr, $signing_key_type:ty, $sign:expr, $generate:expr, $verify:expr) => {
        mod $name {
            use super::*;
            #[test]
            fn noseed() {
                use sign_noseed_schema::*;
                let katfile_serialized = MlDsaSignTestsNoSeed::load($test_name);

                let signing_randomness = [0u8; 32];

                for test_group in katfile_serialized.test_groups {
                    let signing_key_bytes = test_group.private_key;
                    if signing_key_bytes.len() != <$signing_key_type>::len() {
                        // If the signing key size in the KAT does not match the
                        // signing key size in our implementation, ensure that the KAT
                        // key has a corresponding flag set staring that its length is incorrect.
                        //
                        // This flag is set on the child `tests` object.
                        assert_eq!(test_group.tests.len(), 1);
                        assert!(test_group.tests[0]
                            .flags
                            .contains(&Flag::IncorrectPrivateKeyLength));

                        continue;
                    }
                    let signing_key = MLDSASigningKey::new(
                        <[u8; _]>::try_from(signing_key_bytes).unwrap().classify(),
                    );

                    for test in test_group.tests {
                        let message = test.msg;
                        let context = test.ctx;

                        if test.flags.contains(&Flag::InvalidPrivateKey) {
                            // We do not perform validation of s1/s2 during signing. This is
                            // not required by FIPS 204 or FIPS 140-3.
                            // Additional context: https://github.com/pq-code-package/mldsa-native/pull/1003
                            continue;
                        }

                        let signature = $sign(
                            &signing_key,
                            &message,
                            &context,
                            signing_randomness.classify(),
                        );

                        if let Err(SigningError::ContextTooLongError) = signature {
                            assert!(test.result == TestResult::Invalid)
                        }

                        if test.result == TestResult::Valid {
                            assert_eq!(signature.unwrap().as_slice(), test.sig.as_slice());
                        }
                    }
                }
            }
            #[test]
            fn with_seed() {
                use sign_seed_schema::*;
                let katfile_serialized = MlDsaSignTestsWithSeed::load($test_name);

                let signing_randomness = [0u8; 32];

                for test_group in katfile_serialized.test_groups {
                    let MLDSAKeyPair {
                        signing_key,
                        verification_key,
                    } = $generate(test_group.private_seed.classify());

                    for test in test_group.tests {
                        let message = test.msg;
                        let context = test.ctx;

                        let signature = $sign(
                            &signing_key,
                            &message,
                            &context,
                            signing_randomness.classify(),
                        );

                        if let Err(SigningError::ContextTooLongError) = signature {
                            assert!(test.result == TestResult::Invalid)
                        }

                        if let Ok(signature) = signature {
                            if test.result == TestResult::Valid {
                                // check that the signature matches the expected signature
                                assert_eq!(signature.as_slice(), test.sig.as_slice());
                            } else if test.result == TestResult::Invalid {
                                // if a signature is generated, but it is invalid,
                                // check that our own implementation agrees with this judgement,
                                let verification_result =
                                    $verify(&verification_key, &message, &context, &signature);
                                assert!(verification_result.is_err());
                            }
                        }
                    }
                }
            }
        }
    };
}

// 44

wycheproof_sign_test!(
    wycheproof_sign_44,
    ParameterSet::MlDsa44,
    MLDSA44SigningKey,
    ml_dsa_44::sign,
    ml_dsa_44::generate_key_pair,
    ml_dsa_44::verify
);

wycheproof_sign_test!(
    wycheproof_sign_44_portable,
    ParameterSet::MlDsa44,
    MLDSA44SigningKey,
    ml_dsa_44::portable::sign,
    ml_dsa_44::generate_key_pair,
    ml_dsa_44::verify
);

// 65

wycheproof_sign_test!(
    wycheproof_sign_65,
    ParameterSet::MlDsa65,
    MLDSA65SigningKey,
    ml_dsa_65::sign,
    ml_dsa_65::generate_key_pair,
    ml_dsa_65::verify
);

wycheproof_sign_test!(
    wycheproof_sign_65_portable,
    ParameterSet::MlDsa65,
    MLDSA65SigningKey,
    ml_dsa_65::portable::sign,
    ml_dsa_65::generate_key_pair,
    ml_dsa_65::verify
);

// 87

wycheproof_sign_test!(
    wycheproof_sign_87,
    ParameterSet::MlDsa87,
    MLDSA87SigningKey,
    ml_dsa_87::sign,
    ml_dsa_87::generate_key_pair,
    ml_dsa_87::verify
);

wycheproof_sign_test!(
    wycheproof_sign_87_portable,
    ParameterSet::MlDsa87,
    MLDSA87SigningKey,
    ml_dsa_87::portable::sign,
    ml_dsa_87::generate_key_pair,
    ml_dsa_87::verify
);
