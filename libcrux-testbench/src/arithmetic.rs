use libcrux_iot_testutil::DefmtInfoLogger;
use libcrux_iot_testutil::*;
extern crate alloc;
use alloc::string::String;

fn bench_montgomery<L: EventLogger>(_l: &mut L, state: &BenchState) -> Result<(), String> {
    core::hint::black_box( libcrux_ml_kem::vector::portable::ntt::ntt_layer_1_step(state.portable, 1, 2, 3, 4));

    Ok(())
}

fn bench_plantard<L: EventLogger>(_l: &mut L, state: &BenchState) -> Result<(), String> {
    let packed = libcrux_ml_kem::cortex_m::vector::PackedVector::from(state.portable);
    core::hint::black_box( libcrux_ml_kem::cortex_m::arithmetic::ntt_layer_1_step(packed, 1, 2, 3, 4));

    Ok(())
}

// TODO: Put vecs in state
struct BenchState{
    portable: libcrux_ml_kem::vector::portable::vector_type::PortableVector,
    packed: libcrux_ml_kem::cortex_m::vector::PackedVector
}

pub fn run_benchmarks<P: platform::Platform>(test_config: TestConfig<P>) {
    // set up the test suite
    let test_cases = [
        TestCase::new("bench_montgomery", bench_montgomery),
        TestCase::new("bench_plantard", bench_plantard),
    ];

    let test_suite = TestSuite::new("Arithmetic Benchmark", &test_cases);

    let portable = libcrux_ml_kem::vector::portable::vector_type::from_i16_array(&[2;16]);
    let packed = libcrux_ml_kem::cortex_m::vector::PackedVector::from(portable);
    ;
    let state = BenchState {
        portable,
        packed
    };
    
    // run the benchmark
    let mut logger = DefmtInfoLogger;
    let _ = test_suite.benchmark(&mut logger, &test_config, &state);
}
