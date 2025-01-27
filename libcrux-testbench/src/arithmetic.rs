use libcrux_iot_testutil::DefmtInfoLogger;
use libcrux_iot_testutil::*;
extern crate alloc;
use alloc::string::String;

fn bench_montgomery<L: EventLogger>(_l: &mut L, state: &()) -> Result<(), String> {
    libcrux_ml_kem::vector::portable::arithmetic::montgomery_multiply_fe_by_fer(1i16, 12i16);
    Ok(())
}

fn bench_plantard<L: EventLogger>(_l: &mut L, state: &()) -> Result<(), String> {
    libcrux_ml_kem::vector::portable::arithmetic::plantard_multiply_single_coeff(2, 4);
    Ok(())
}

pub fn run_benchmarks<P: platform::Platform>(test_config: TestConfig<P>) {
    // set up the test suite
    let test_cases = [
        TestCase::new("bench_montgomery", bench_montgomery),
        TestCase::new("bench_plantard", bench_plantard),
    ];

    let test_suite = TestSuite::new("Arithmetic Benchmark", &test_cases);

    // run the benchmark
    let mut logger = DefmtInfoLogger;
    let _ = test_suite.benchmark(&mut logger, &test_config, &());
}
