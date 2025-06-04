#![no_main]
#![no_std]

use board::cycle_counter::CycleCounter;
use board::init::setup_cycle_counter;

use libcrux_nucleo_l4r5zi::{self as board, init::ClockConfig}; // global logger + panicking-behavior + memory layout

#[cortex_m_rt::entry]
fn main() -> ! {
    // Set up the system clock.
    let clock_config = ClockConfig::CycleBenchmark;
    board::init::setup_clock(clock_config);

    setup_cycle_counter();

    let mut sk = [0u8; libcrux_pqm4::KYBER_SECRETKEYBYTES as usize];
    let mut pk = [0u8; libcrux_pqm4::KYBER_PUBLICKEYBYTES as usize];

    let mut ct = [0u8; libcrux_pqm4::KYBER_CIPHERTEXTBYTES as usize];
    let mut ss_enc = [0u8; libcrux_pqm4::KYBER_SSBYTES as usize];
    let mut ss_dec = [0u8; libcrux_pqm4::KYBER_SSBYTES as usize];

    let start = CycleCounter::start_measurement();
    core::hint::black_box(unsafe {
        libcrux_pqm4::crypto_kem_keypair(&raw mut pk[0], &raw mut sk[0]);
    });
    CycleCounter::end_measurement("pqm4: Generate Key Pair ML-KEM 1024", start);

    let start = CycleCounter::start_measurement();
    core::hint::black_box(unsafe {
        libcrux_pqm4::crypto_kem_enc(&raw mut ct[0], &raw mut ss_enc[0], &raw const pk[0]);
    });
    CycleCounter::end_measurement("pqm4: Encapsulate ML-KEM 1024", start);

    let start = CycleCounter::start_measurement();
    core::hint::black_box(unsafe {
        libcrux_pqm4::crypto_kem_dec(&raw mut ss_dec[0], &raw const ct[0], &raw const sk[0]);
    });
    CycleCounter::end_measurement("pqm4: Decapsulate ML-KEM 1024", start);

    let mut sha3_output = [0u8; 64];
    let sha3_input = [1, 2, 3, 4];
    unsafe {
        libcrux_pqm4::sha3_512(&raw mut sha3_output[0], &raw const sha3_input[0], 4);
    }
    defmt::println!("SHA3-512([1,2,3,4]): {=[u8]}", sha3_output);

    let mut sha3_state = [1u64; 25];
    let start = CycleCounter::start_measurement();
    unsafe {
        core::hint::black_box(libcrux_pqm4::KeccakF1600_StatePermute_4Rounds(
            core::hint::black_box(sha3_state.as_mut_ptr()),
        ));
    }
    CycleCounter::end_measurement("pqm4: KeccakF1600_StatePermute_4Rounds", start);

    let mut sha3_state = libcrux_sha3::portable::incremental::shake128_init();
    let start = CycleCounter::start_measurement();
    core::hint::black_box(libcrux_sha3::portable::incremental::keccakf1660_4rounds(
        core::hint::black_box(&mut sha3_state),
    ));
    CycleCounter::end_measurement("libcrux: keccakf1600_4rounds", start);

    assert_eq!(ss_enc, ss_dec);

    board::exit()
}
