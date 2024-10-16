use libcrux_iot_testutil::DefmtInfoLogger;
use libcrux_iot_testutil::*;
extern crate alloc;
use alloc::string::String;
use alloc::vec;

#[cfg(feature = "mlkem512")]
use libcrux_ml_kem::mlkem512 as mlkem;
#[cfg(feature = "mlkem512")]
type MlKemPublicKey = mlkem::MlKem512PublicKey;
#[cfg(feature = "mlkem512")]
type MlKemPrivateKey = mlkem::MlKem512PrivateKey;
#[cfg(feature = "mlkem512")]
type MlKemCiphertext = mlkem::MlKem512Ciphertext;

#[cfg(feature = "mlkem768")]
use libcrux_ml_kem::mlkem768 as mlkem;
#[cfg(feature = "mlkem768")]
type MlKemPublicKey = mlkem::MlKem768PublicKey;
#[cfg(feature = "mlkem768")]
type MlKemPrivateKey = mlkem::MlKem768PrivateKey;
#[cfg(feature = "mlkem768")]
type MlKemCiphertext = mlkem::MlKem768Ciphertext;

#[cfg(feature = "mlkem1024")]
use libcrux_ml_kem::mlkem1024 as mlkem;
#[cfg(feature = "mlkem1024")]
type MlKemPublicKey = mlkem::MlKem1024PublicKey;
#[cfg(feature = "mlkem1024")]
type MlKemPrivateKey = mlkem::MlKem1024PrivateKey;
#[cfg(feature = "mlkem1024")]
type MlKemCiphertext = mlkem::MlKem1024Ciphertext;

struct MlKemBenchState<'a> {
    randomness_gen: [u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE],
    public_key: &'a MlKemPublicKey,
    private_key: &'a MlKemPrivateKey,
    randomness_encaps: [u8; libcrux_ml_kem::ENCAPS_SEED_SIZE],
    ciphertext: MlKemCiphertext,
}

fn bench_keygen<L: EventLogger>(_l: &mut L, state: &MlKemBenchState) -> Result<(), String> {
    let _pair = mlkem::generate_key_pair(state.randomness_gen);
    Ok(())
}

fn bench_encaps<L: EventLogger>(_l: &mut L, state: &MlKemBenchState) -> Result<(), String> {
    let _ = mlkem::encapsulate(&state.public_key, state.randomness_encaps);
    Ok(())
}

fn bench_decaps<L: EventLogger>(_l: &mut L, state: &MlKemBenchState) -> Result<(), String> {
    let _ = mlkem::decapsulate(&state.private_key, &state.ciphertext);

    Ok(())
}

pub fn run_benchmarks() {
    // set up the test suite
    let test_cases = [
        TestCase::new("bench_keygen", bench_keygen),
        TestCase::new("bench_encaps", bench_encaps),
        TestCase::new("bench_decaps", bench_decaps),
    ];

    let test_suite = TestSuite::new("ML-KEM Benchmark", &test_cases);

    // set up the test config
    let test_config = TestConfig {
        core_freq: 4_000_000,
        only_names: vec!["bench_keygen", "bench_encaps", "bench_decaps"],
        early_abort: false,
        benchmark_runs: 1,
    };

    // prepare the state for the benchmarked functions
    let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
    let pair = mlkem::generate_key_pair(randomness_gen);
    let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
    let (ciphertext, _shared_secret) = mlkem::encapsulate(pair.public_key(), randomness_encaps);
    let state = MlKemBenchState {
        randomness_gen,
        public_key: pair.public_key(),
        private_key: pair.private_key(),
        randomness_encaps,
        ciphertext,
    };

    // run the benchmark
    let mut logger = DefmtInfoLogger;
    let _ = test_suite.benchmark(&mut logger, &test_config, &state);
}
