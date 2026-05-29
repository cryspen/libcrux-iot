/// CAVP (Cryptographic Algorithm Validation Program) tests.
///
/// Uses libcrux-kats for test vectors and validates our SHA-3/SHAKE implementation
/// against each test case.
use hacspec_sha3::*;

// ---------------------------------------------------------------------------
// SHA3 CAVP tests
// ---------------------------------------------------------------------------

macro_rules! sha3_cavp_test {
    ($name:ident, $kats_fn:path, $hash_fn:ident) => {
        #[test]
        fn $name() {
            let tv = $kats_fn();
            let test_cnt = tv.tests.len();
            assert!(test_cnt > 0, "Empty test vector file");
            for (i, tc) in tv.tests.iter().enumerate() {
                let msg = &tc.msg[..tc.msg_length / 8];
                let digest = $hash_fn(msg);
                assert_eq!(
                    &digest[..],
                    &tc.digest[..],
                    "test case {i} failed (msg_len={} bits)",
                    tc.msg_length
                );
            }
            eprintln!("Ran {test_cnt} tests for {}", stringify!($name));
        }
    };
}

sha3_cavp_test!(sha3_224_short_msg, libcrux_kats::sha3::sha3_224_short, sha3_224);
sha3_cavp_test!(sha3_224_long_msg, libcrux_kats::sha3::sha3_224_long, sha3_224);
sha3_cavp_test!(sha3_256_short_msg, libcrux_kats::sha3::sha3_256_short, sha3_256);
sha3_cavp_test!(sha3_256_long_msg, libcrux_kats::sha3::sha3_256_long, sha3_256);
sha3_cavp_test!(sha3_384_short_msg, libcrux_kats::sha3::sha3_384_short, sha3_384);
sha3_cavp_test!(sha3_384_long_msg, libcrux_kats::sha3::sha3_384_long, sha3_384);
sha3_cavp_test!(sha3_512_short_msg, libcrux_kats::sha3::sha3_512_short, sha3_512);
sha3_cavp_test!(sha3_512_long_msg, libcrux_kats::sha3::sha3_512_long, sha3_512);

// ---------------------------------------------------------------------------
// SHAKE CAVP tests (short/long message, fixed output length)
// ---------------------------------------------------------------------------

macro_rules! shake_cavp_test {
    ($name:ident, $kats_fn:path, $shake_fn:ident, $output_len:expr) => {
        #[test]
        fn $name() {
            let tv = $kats_fn();
            let test_cnt = tv.tests.len();
            assert!(test_cnt > 0, "Empty test vector file");
            for (i, tc) in tv.tests.iter().enumerate() {
                let msg = &tc.msg[..tc.msg_length / 8];
                let digest = $shake_fn::<$output_len>(msg);
                assert_eq!(
                    &digest[..],
                    &tc.digest[..],
                    "test case {i} failed (msg_len={} bits)",
                    tc.msg_length
                );
            }
            eprintln!("Ran {test_cnt} tests for {}", stringify!($name));
        }
    };
}

// SHAKE128 ShortMsg/LongMsg: [Outputlen = 128] → 16 bytes
shake_cavp_test!(shake128_short_msg, libcrux_kats::sha3::shake128_short, shake128, 16);
shake_cavp_test!(shake128_long_msg, libcrux_kats::sha3::shake128_long, shake128, 16);

// SHAKE256 ShortMsg/LongMsg: [Outputlen = 256] → 32 bytes
shake_cavp_test!(shake256_short_msg, libcrux_kats::sha3::shake256_short, shake256, 32);
shake_cavp_test!(shake256_long_msg, libcrux_kats::sha3::shake256_long, shake256, 32);

// ---------------------------------------------------------------------------
// SHAKE Variable Output Length CAVP tests
//
// These tests have variable output lengths per test case. Since our API uses
// const generics, we compute a max-size output and compare the prefix.
// SHAKE is an XOF so the first N bytes of shake(msg, K) match shake(msg, N)
// for any K >= N.
// ---------------------------------------------------------------------------

// SHAKE128 VariableOut: max output = 1120 bits = 140 bytes
#[test]
fn shake128_variable_out() {
    let tv = libcrux_kats::sha3::shake128_variable_out();
    let test_cnt = tv.tests.len();
    assert!(test_cnt > 0, "Empty test vector file");
    for (i, tc) in tv.tests.iter().enumerate() {
        let msg = &tc.msg[..tv.header.input_length / 8];
        let full_output = shake128::<140>(msg);
        let expected_len = tc.digest.len();
        assert_eq!(
            &full_output[..expected_len],
            &tc.digest[..],
            "test case {i} failed (output_len={expected_len} bytes)",
        );
    }
    eprintln!("Ran {test_cnt} tests for shake128_variable_out");
}

// SHAKE256 VariableOut: max output = 2000 bits = 250 bytes
#[test]
fn shake256_variable_out() {
    let tv = libcrux_kats::sha3::shake256_variable_out();
    let test_cnt = tv.tests.len();
    assert!(test_cnt > 0, "Empty test vector file");
    for (i, tc) in tv.tests.iter().enumerate() {
        let msg = &tc.msg[..tv.header.input_length / 8];
        let full_output = shake256::<250>(msg);
        let expected_len = tc.digest.len();
        assert_eq!(
            &full_output[..expected_len],
            &tc.digest[..],
            "test case {i} failed (output_len={expected_len} bytes)",
        );
    }
    eprintln!("Ran {test_cnt} tests for shake256_variable_out");
}
