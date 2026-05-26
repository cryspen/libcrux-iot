use libcrux_iot_sha3::*;
use libcrux_secrets::{ClassifyRef as _, DeclassifyRef as _, U8};

macro_rules! sha3_test {
    ($test_name:ident, $kats_fn:path, $digest_len:expr, $algorithm:expr) => {
        #[test]
        #[allow(non_snake_case)]
        fn $test_name() {
            let tv = $kats_fn();
            let test_cnt = tv.tests.len();
            assert!(test_cnt > 0, "Empty test vector file");
            for (i, test) in tv.tests.iter().enumerate() {
                let my_digest: [U8; $digest_len] =
                    sha3($algorithm, test.msg[0..test.msg_length / 8].classify_ref());
                assert_eq!(
                    my_digest.declassify_ref(),
                    &test.digest[..],
                    "test {i}: digest mismatch"
                );
            }
            eprintln!("Ran {test_cnt} tests for {}", stringify!($test_name));
        }
    };
}

sha3_test!(
    SHA3_224ShortMsg,
    libcrux_kats::sha3::sha3_224_short,
    SHA3_224_DIGEST_SIZE,
    Algorithm::Sha224
);
sha3_test!(
    SHA3_224LongMsg,
    libcrux_kats::sha3::sha3_224_long,
    SHA3_224_DIGEST_SIZE,
    Algorithm::Sha224
);
sha3_test!(
    SHA3_256ShortMsg,
    libcrux_kats::sha3::sha3_256_short,
    SHA3_256_DIGEST_SIZE,
    Algorithm::Sha256
);
sha3_test!(
    SHA3_256LongMsg,
    libcrux_kats::sha3::sha3_256_long,
    SHA3_256_DIGEST_SIZE,
    Algorithm::Sha256
);
sha3_test!(
    SHA3_384ShortMsg,
    libcrux_kats::sha3::sha3_384_short,
    SHA3_384_DIGEST_SIZE,
    Algorithm::Sha384
);
sha3_test!(
    SHA3_384LongMsg,
    libcrux_kats::sha3::sha3_384_long,
    SHA3_384_DIGEST_SIZE,
    Algorithm::Sha384
);
sha3_test!(
    SHA3_512ShortMsg,
    libcrux_kats::sha3::sha3_512_short,
    SHA3_512_DIGEST_SIZE,
    Algorithm::Sha512
);
sha3_test!(
    SHA3_512LongMsg,
    libcrux_kats::sha3::sha3_512_long,
    SHA3_512_DIGEST_SIZE,
    Algorithm::Sha512
);

macro_rules! shake_test {
    ($test_name:ident, $kats_fn:path, $shake:expr) => {
        #[test]
        #[allow(non_snake_case)]
        fn $test_name() {
            let _ = pretty_env_logger::try_init();
            let tv = $kats_fn();
            let test_cnt = tv.tests.len();
            assert!(test_cnt > 0, "Empty test vector file");
            for (i, test) in tv.tests.iter().enumerate() {
                let mut my_digest = vec![U8(0); test.digest.len()];
                $shake(
                    &mut my_digest,
                    test.msg[0..test.msg_length / 8].classify_ref(),
                );
                assert_eq!(my_digest.declassify_ref(), &test.digest[..], "test {i}: digest mismatch");
            }
            eprintln!("Ran {test_cnt} tests for {}", stringify!($test_name));
        }
    };
}

shake_test!(
    SHAKE128ShortMsg,
    libcrux_kats::sha3::shake128_short,
    shake128_ema
);
shake_test!(
    SHAKE128LongMsg,
    libcrux_kats::sha3::shake128_long,
    shake128_ema
);
shake_test!(
    SHAKE256ShortMsg,
    libcrux_kats::sha3::shake256_short,
    shake256_ema
);
shake_test!(
    SHAKE256LongMsg,
    libcrux_kats::sha3::shake256_long,
    shake256_ema
);

macro_rules! shake_vo_test {
    ($test_name:ident, $kats_fn:path, $shake:expr) => {
        #[test]
        #[allow(non_snake_case)]
        fn $test_name() {
            let _ = pretty_env_logger::try_init();
            let tv = $kats_fn();
            let test_cnt = tv.tests.len();
            assert!(test_cnt > 0, "Empty test vector file");
            for (i, test) in tv.tests.iter().enumerate() {
                let mut my_digest = vec![U8(0); test.digest.len()];
                $shake(
                    &mut my_digest,
                    test.msg[0..tv.header.input_length / 8].classify_ref(),
                );
                assert_eq!(my_digest.declassify_ref(), &test.digest[..], "test {i}: digest mismatch");
            }
            eprintln!("Ran {test_cnt} tests for {}", stringify!($test_name));
        }
    };
}

shake_vo_test!(
    SHAKE128VariableOut,
    libcrux_kats::sha3::shake128_variable_out,
    shake128_ema
);
shake_vo_test!(
    SHAKE256VariableOut,
    libcrux_kats::sha3::shake256_variable_out,
    shake256_ema
);

macro_rules! shake_vo_test_incremental {
    ($name:ident, $kats_fn:path, $shake:ty) => {
        #[test]
        #[allow(non_snake_case)]
        fn $name() {
            use libcrux_iot_sha3::incremental::Xof;
            let _ = pretty_env_logger::try_init();
            let tv = $kats_fn();
            let test_cnt = tv.tests.len();
            assert!(test_cnt > 0, "Empty test vector file");
            for (i, test) in tv.tests.iter().enumerate() {
                let mut my_digest = vec![U8(0); test.digest.len()];
                let mut shake = <$shake>::new();
                shake.absorb_final(test.msg[0..tv.header.input_length / 8].classify_ref());
                shake.squeeze(&mut my_digest);
                assert_eq!(my_digest.declassify_ref(), &test.digest[..], "test {i}: digest mismatch");
            }
            eprintln!("Ran {test_cnt} tests for {}", stringify!($name));
        }
    };
}

shake_vo_test_incremental!(
    SHAKE128VariableOut_incremental,
    libcrux_kats::sha3::shake128_variable_out,
    libcrux_iot_sha3::incremental::Shake128Xof
);
shake_vo_test_incremental!(
    SHAKE256VariableOut_incremental,
    libcrux_kats::sha3::shake256_variable_out,
    libcrux_iot_sha3::incremental::Shake256Xof
);
