use libcrux_iot_testutil::DefmtInfoLogger;
use libcrux_iot_testutil::*;
extern crate alloc;
use alloc::string::String;
use libcrux_ml_kem::{
    cortex_m::{
        arithmetic::{ntt_layer_1_step, plantard_double_ct, plantard_double_ct_reference},
        vector::PackedVector,
    },
    polynomial::PolynomialRingElement,
    ntt::ntt_vector_u,
    vector::portable::vector_type::{from_i16_array, PortableVector},
};

fn bench_montgomery<L: EventLogger>(_l: &mut L, state: &mut BenchState) -> Result<(), String> {
    core::hint::black_box(libcrux_ml_kem::vector::portable::ntt::ntt_layer_1_step(
        state.portable,
        1,
        2,
        3,
        4,
    ));

    Ok(())
}

fn bench_plantard<L: EventLogger>(_l: &mut L, state: &mut BenchState) -> Result<(), String> {
    // let packed = libcrux_ml_kem::cortex_m::vector::PackedVector::from(state.portable);
    // core::hint::black_box(ntt_layer_1_step(
    //     state.packed,
    //     1,
    //     2,
    //     3,
    //     4,
    //     plantard_double_ct_reference,
    // ));

    Ok(())
}

fn bench_portable_ntt<L: EventLogger>(_l: &mut L, state: &mut BenchState) -> Result<(), String> {
    core::hint::black_box(ntt_vector_u::<10, PortableVector>(&mut state.ring_element_portable));
    Ok(())
}

fn bench_plantard_ntt<L: EventLogger>(_l: &mut L, state: &mut BenchState) -> Result<(), String> {
    core::hint::black_box(libcrux_ml_kem::cortex_m::ntt(&mut state.ring_element_flat));
    Ok(())
}

struct BenchState {
    ring_element_portable: PolynomialRingElement<PortableVector>,
    ring_element_flat: [i16; 256],
    portable: PortableVector,
    packed: PackedVector,
}

pub fn run_benchmarks<P: platform::Platform>(test_config: TestConfig<P>) {
    // set up the test suite
    let test_cases = [
        // TestCase::new("bench_montgomery", bench_montgomery),
        // TestCase::new("bench_plantard", bench_plantard),
        TestCase::new("bench_portable_ntt", bench_portable_ntt),
        TestCase::new("bench_plantard_ntt", bench_plantard_ntt),
        
    ];

    let test_suite = TestSuite::new("Arithmetic Benchmark", &test_cases);

    let portable = libcrux_ml_kem::vector::portable::vector_type::from_i16_array(&[2; 16]);
    let packed = PackedVector::from(portable);

    let ring_element_flat = [
        56, 673, -456, 430, -940, -706, 1269, 1635, 1261, -1125, 1480, 1031, 895, -811, 299, 1663,
        -856, -21, -166, 614, -1149, 1519, -1364, -1233, -80, -1164, 153, 124, -304, -399, 1537,
        1151, -1173, -1125, 365, -78, -771, -646, 474, -42, -737, 709, 287, -1554, -735, 1639, 928,
        -925, -417, -653, 1537, 1283, -1110, 388, -1221, -1588, 574, 1111, -1369, -552, -392, -777,
        -572, 1481, -506, 348, -1494, -1483, -1057, 543, 1664, 220, 691, -541, -1588, 405, -362,
        747, 172, -1548, -1134, 1062, 315, 634, 1310, -1454, -993, -422, -914, -46, -544, -1618,
        1465, -721, 1300, 1361, -244, -558, -553, -78, -836, 1642, 22, -463, 730, 593, 1593, 271,
        -267, 703, 1151, 1618, -1275, 51, 25, -1137, 1014, 169, 228, 627, 998, -264, -1238, -645,
        -779, 1120, -617, 1487, 1334, 1518, 1105, -771, 1567, 1419, 14, 1495, 182, -302, -1078,
        -1655, 1613, -1578, -375, 694, -1276, -1396, -1238, 630, 597, -1548, 1219, 1135, 53, 1575,
        1062, -1533, 1388, 806, -349, 394, 1405, -304, -963, -923, 1318, 5, 862, 1205, -1005, 222,
        349, -853, -578, 1014, -1648, -1653, -1400, -1043, 1215, 1573, 361, 246, 1155, 214, 605,
        1014, -1452, -1038, 1366, -1233, -107, 1289, 648, 1046, -1586, -534, -567, 60, -1147, 1029,
        -1578, 1596, -1267, 1251, 1536, 253, 218, 221, 194, 1242, 1366, -1056, 1071, -346, -1503,
        -1611, -1088, 648, -195, 393, -1444, -1116, 1563, -443, -252, -495, -907, -305, -785,
        -1285, 664, -1463, 644, -854, 677, 1217, 1312, 71, 3, 312, 896, 595, 16, -1078, -1377,
        1101, -979, -1430, 401, -709, 1067, -415, -638, 1211, 1177, -1021,
    ];

    let ring_element_portable = libcrux_ml_kem::polynomial::from_i16_array(&ring_element_flat);
    let mut state = BenchState { portable, packed, ring_element_flat, ring_element_portable};

    // run the benchmark
    let mut logger = DefmtInfoLogger;
    let _ = test_suite.benchmark(&mut logger, &test_config, &mut state);
}
