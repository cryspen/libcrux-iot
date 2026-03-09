use libcrux_iot_ml_dsa::{ml_dsa_44, ml_dsa_65, ml_dsa_87};
use libcrux_secrets::{Classify as _, U8};
use rand::{rngs::OsRng, Rng, RngCore};
fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}
fn random_message() -> Vec<u8> {
    let mut rng = OsRng;

    let mut length = [0u8; 2];
    rng.try_fill_bytes(&mut length).unwrap();
    let length = ((length[1] as u16) << 8) | length[0] as u16;

    let mut message = Vec::with_capacity(length.into());
    rng.try_fill_bytes(&mut message).unwrap();

    message
}

fn modify_signing_key<const SIGNING_KEY_SIZE: usize>(signing_key: &mut [U8; SIGNING_KEY_SIZE]) {
    let option = rand::thread_rng().gen_range(0..2);

    let position = match option {
        // Change the seed used for generating A
        0 => rand::thread_rng().gen_range(0..32),

        // Change the verification key hash
        1 => rand::thread_rng().gen_range(64..128),

        // TODO: Changing s1, s2, and t0 could still result in valid
        // signatures. Look into this further.
        _ => unreachable!(),
    };

    let random_byte = {
        let byte = random_array::<1>()[0];

        if byte == 0 {
            byte + 1
        } else {
            byte
        }
    };

    signing_key[position] ^= random_byte;
}

macro_rules! impl_consistency_test {
    ($name:ident, $key_gen:expr, $sign:expr, $verify:expr) => {
        #[test]
        fn $name() {
            let key_generation_seed = random_array();
            let signing_randomness = random_array();

            let message = random_message();

            let key_pair = $key_gen(key_generation_seed.classify());

            let signature = $sign(
                &key_pair.signing_key,
                &message,
                b"",
                signing_randomness.classify(),
            )
            .expect("Rejection sampling failure probability is < 2⁻¹²⁸");

            $verify(&key_pair.verification_key, &message, b"", &signature)
                .expect("Verification should pass since the signature was honestly generated");
        }
    };
}

macro_rules! impl_modified_signing_key_test {
    ($name:ident, $key_gen:expr, $signing_key_size:expr, $sign:expr, $verify:expr) => {
        #[test]
        fn $name() {
            let key_generation_seed = random_array();
            let signing_randomness = random_array();

            let message = random_message();

            let mut key_pair = $key_gen(key_generation_seed.classify());

            modify_signing_key::<{ $signing_key_size }>(key_pair.signing_key.as_ref_mut());

            let signature = $sign(
                &key_pair.signing_key,
                &message,
                b"",
                signing_randomness.classify(),
            )
            .expect("Rejection sampling failure probability is < 2⁻¹²⁸");

            assert!($verify(&key_pair.verification_key, &message, b"", &signature).is_err());
        }
    };
}

// 44

impl_consistency_test!(
    consistency_44,
    ml_dsa_44::generate_key_pair,
    ml_dsa_44::sign,
    ml_dsa_44::verify
);

impl_modified_signing_key_test!(
    modified_signing_key_44,
    ml_dsa_44::generate_key_pair,
    ml_dsa_44::MLDSA44SigningKey::len(),
    ml_dsa_44::sign,
    ml_dsa_44::verify
);

impl_consistency_test!(
    consistency_44_portable,
    ml_dsa_44::portable::generate_key_pair,
    ml_dsa_44::portable::sign,
    ml_dsa_44::portable::verify
);

impl_modified_signing_key_test!(
    modified_signing_key_44_portable,
    ml_dsa_44::portable::generate_key_pair,
    ml_dsa_44::MLDSA44SigningKey::len(),
    ml_dsa_44::portable::sign,
    ml_dsa_44::portable::verify
);

// 65

impl_consistency_test!(
    consistency_65,
    ml_dsa_65::generate_key_pair,
    ml_dsa_65::sign,
    ml_dsa_65::verify
);

impl_modified_signing_key_test!(
    modified_signing_key_65,
    ml_dsa_65::generate_key_pair,
    ml_dsa_65::MLDSA65SigningKey::len(),
    ml_dsa_65::sign,
    ml_dsa_65::verify
);

// 87

impl_consistency_test!(
    consistency_87,
    ml_dsa_87::generate_key_pair,
    ml_dsa_87::sign,
    ml_dsa_87::verify
);

impl_modified_signing_key_test!(
    modified_signing_key_87,
    ml_dsa_87::generate_key_pair,
    ml_dsa_87::MLDSA87SigningKey::len(),
    ml_dsa_87::sign,
    ml_dsa_87::verify
);

#[test]
#[rustfmt::skip]
fn bad_hint() {
    let message = [42u8; 5];
    let context = b"";

    let keypair = ml_dsa_65::generate_key_pair([0u8; 32]);

    // For ML-DSA-65, the signature layout is:
    //   bytes   0.. 48: commitment hash (COMMITMENT_HASH_SIZE = 48)
    //   bytes  48..3248: signer response (COLUMNS_IN_A=5 * GAMMA1_RING_ELEMENT_SIZE=640)
    //   bytes 3248..3309: hint (MAX_ONES_IN_HINT=55 indices + ROWS_IN_A=6 counters)
    //
    // The hint check happens before the commitment hash comparison in
    // verify_internal, so the commitment hash and signer response bytes
    // do not matter for this test.
    //
    // The bad hint has the last row counter set to 56 > MAX_ONES_IN_HINT (55).
    //
    // With the fix (current_true_hints_seen > max_ones_in_hint):
    //   56 > 55 → MalformedHintError ✓
    //
    // With the bug (previous_true_hints_seen > max_ones_in_hint):
    //   previous = 51, 51 > 55? No → passes. The loop reads j = 51..56, i.e.
    //   hint_serialized[51..56] = [1, 2, 3, 4, 9], where 9 = counter[0].
    //   All accesses are within bounds and values are strictly increasing,
    //   so no other check catches the error. The hint is considered valid and
    //   verification proceeds to the commitment hash comparison, which fails
    //   with CommitmentHashesDontMatchError.
    //
    // Row 5 indices [1,2,3,4] are chosen to be less than counter[0]=9 so
    // that the sequence [1,2,3,4, 9] seen by the buggy loop is strictly
    // increasing, bypassing the monotonicity check.
    let mut sig_bytes = [0u8; 3309];
    sig_bytes[3248..3309].copy_from_slice(&[
        // hint indices (MAX_ONES_IN_HINT = 55 bytes), monotonically increasing within each row
        1,  2,  3,  4,  5,  6,  7,  8,  9,                          // row 0:  9 hints
        1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11,                 // row 1: 11 hints
        1,  2,  3,  4,  5,  6,  7,  8,  9,  10,                     // row 2: 10 hints
        1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 13, 14,     // row 3: 14 hints
        1,  2,  3,  4,  5,  6,  7,                                   // row 4:  7 hints
        1,  2,  3,  4,                                               // row 5:  4 hints
        // cumulative counters per row (ROWS_IN_A = 6 bytes)
        9,  20, 30, 44, 51,
        56, // counter[5] = 56 > MAX_ONES_IN_HINT (55) — caught by fix, bypassed by bug
    ]);

    let signature = ml_dsa_65::MLDSA65Signature::new(sig_bytes);
    let result = ml_dsa_65::verify(&keypair.verification_key, &message, context, &signature);
    eprintln!("result: {result:?}");
    assert!(matches!(
        result,
        Err(libcrux_iot_ml_dsa::VerificationError::MalformedHintError),
    ));
}

#[test]
#[rustfmt::skip]
fn bad_hint_out_of_bounds() {
    let message = [42u8; 5];
    let context = b"";

    let keypair = ml_dsa_65::generate_key_pair([0u8; 32]);

    // As a variation on the test in `bad_hint`, the faulty hint decoding logic can also be used to cause an out-of-bounds memory access during hint decoding by setting the final value of the serialized hint slice to a value greater than the length of the serialized hint slice.
    let mut sig_bytes = [0u8; 3309];
    sig_bytes[3248..3309].copy_from_slice(&[
        // hint indices (MAX_ONES_IN_HINT = 55 bytes), monotonically increasing within each row
        1,  2,  3,  4,  5,  6,  7,  8,  9,                          // row 0:  9 hints
        1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11,                 // row 1: 11 hints
        1,  2,  3,  4,  5,  6,  7,  8,  9,  10,                     // row 2: 10 hints
        1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 13, 14,     // row 3: 14 hints
        1,  2,  3,  4,  5,  6,  7,                                   // row 4:  7 hints
        1,  2,  3,  4,                                               // row 5:  4 hints
        // cumulative counters per row (ROWS_IN_A = 6 bytes)
        9,  20, 30, 44, 51,
        62, // counter[5] = 62 > MAX_ONES_IN_HINT (55) — caught by fix, bypassed by bug
    ]);

    let signature = ml_dsa_65::MLDSA65Signature::new(sig_bytes);
    let result = ml_dsa_65::verify(&keypair.verification_key, &message, context, &signature);
    eprintln!("result: {result:?}");
    assert!(matches!(
        result,
        Err(libcrux_iot_ml_dsa::VerificationError::MalformedHintError),
    ));
}
