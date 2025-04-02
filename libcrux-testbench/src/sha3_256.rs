use libcrux_iot_testutil::DefmtInfoLogger;
use libcrux_iot_testutil::*;
extern crate alloc;
use alloc::string::String;

struct Sha3BenchState {
    roundfn_block: libcrux_sha3::portable::KeccakState,
    sha256_out: [u8; 32],
    sha256_in: [u8; 32],
}

fn bench_roundfn<L: EventLogger>(_l: &mut L, state: &mut Sha3BenchState) -> Result<(), String> {
    Ok(core::hint::black_box(libcrux_sha3::portable::keccak1600(
        &mut state.roundfn_block,
    )))
}

fn bench_sha3_256<L: EventLogger>(_l: &mut L, state: &mut Sha3BenchState) -> Result<(), String> {
    Ok(core::hint::black_box(libcrux_sha3::portable::sha256(
        &mut state.sha256_out,
        &state.sha256_in,
    )))
}

pub fn run_benchmarks<P: platform::Platform>(test_config: TestConfig<P>) {
    // set up the test suite
    let test_cases = [
        TestCase::new("bench_roundfn", bench_roundfn),
        TestCase::new("bench_sha3_256", bench_sha3_256),
    ];

    let test_suite = TestSuite::new("SHA3 Benchmark", &test_cases);

    // prepare the state for the benchmarked functions
    let mut state = Sha3BenchState {
        roundfn_block: libcrux_sha3::portable::incremental::shake128_init(),
        sha256_out: [0; 32],
        sha256_in: [1; 32],
    };

    // run the benchmark
    let mut logger = DefmtInfoLogger;
    let _ = test_suite.benchmark(&mut logger, &test_config, &mut state);
}
