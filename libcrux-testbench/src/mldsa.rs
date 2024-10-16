use libcrux_iot_testutil::DefmtInfoLogger;
use libcrux_iot_testutil::*;
extern crate alloc;
use alloc::string::String;
use alloc::vec;

use libcrux_ml_dsa::ml_dsa_65;

struct MLDSABenchState {
    randomness_gen: [u8; 32],
    keypair: ml_dsa_65::MLDSA65KeyPair,
    signing_randomness: [u8; 32],
    message: [u8; 1024],
    signature: ml_dsa_65::MLDSA65Signature,
}

fn bench_keygen<L: EventLogger>(_l: &mut L, state: &MLDSABenchState) -> Result<(), String> {
    let _pair = ml_dsa_65::generate_key_pair(state.randomness_gen);
    Ok(())
}

fn bench_sign<L: EventLogger>(_l: &mut L, state: &MLDSABenchState) -> Result<(), String> {
    let _signature = ml_dsa_65::sign(
        &state.keypair.signing_key,
        &state.message,
        b"",
        state.signing_randomness,
    );
    Ok(())
}

fn bench_verify<L: EventLogger>(_l: &mut L, state: &MLDSABenchState) -> Result<(), String> {
    let _ = ml_dsa_65::verify(
        &state.keypair.verification_key,
        &state.message,
        b"",
        &state.signature,
    );

    Ok(())
}

pub fn run_benchmarks() {
    // set up the test suite
    let test_cases = [
        TestCase::new("bench_keygen", bench_keygen),
        TestCase::new("bench_sign", bench_sign),
        TestCase::new("bench_verify", bench_verify),
    ];

    let test_suite = TestSuite::new(&test_cases);

    // set up the test config
    let test_config = TestConfig {
        core_freq: 4_000_000,
        only_names: vec!["bench_keygen", "bench_sign", "bench_verify"],
        early_abort: false,
        benchmark_runs: 1,
    };

    // prepare the state for the benchmarked functions
    let randomness_gen = [1u8; 32];
    let keypair = ml_dsa_65::generate_key_pair(randomness_gen);
    let signing_randomness = [4u8; 32];
    let message = [5u8; 1024];
    let signature =
        ml_dsa_65::sign(&keypair.signing_key, &message, b"", signing_randomness).unwrap();

    let state = MLDSABenchState {
        randomness_gen,
        keypair,
        signing_randomness,
        message,
        signature,
    };

    // run the benchmark
    let mut logger = DefmtInfoLogger;
    let _ = test_suite.benchmark(&mut logger, &test_config, &state);
}

