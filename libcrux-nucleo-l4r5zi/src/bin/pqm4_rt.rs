#![no_main]
#![no_std]

#[cortex_m_rt::entry]
fn main() -> ! {
    #[cfg(feature = "realtime")]
    {
        use libcrux_nucleo_l4r5zi::{self as board, init::ClockConfig, real_time::Timer}; // global logger + panicking-behavior + memory layout

        // Set up the system clock.
        let clock_config = ClockConfig::Fast;
        board::init::setup_clock(clock_config);

        let mut sk = [0u8; libcrux_pqm4::KYBER_SECRETKEYBYTES as usize];
        let mut pk = [0u8; libcrux_pqm4::KYBER_PUBLICKEYBYTES as usize];

        let mut ct = [0u8; libcrux_pqm4::KYBER_CIPHERTEXTBYTES as usize];
        let mut ss_enc = [0u8; libcrux_pqm4::KYBER_SSBYTES as usize];
        let mut ss_dec = [0u8; libcrux_pqm4::KYBER_SSBYTES as usize];

        let start = Timer::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::crypto_kem_keypair(&raw mut pk[0], &raw mut sk[0]);
        });
        Timer::end_measurement("pqm4: Generate Key Pair ML-KEM 1024", start);

        let start = Timer::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::crypto_kem_enc(&raw mut ct[0], &raw mut ss_enc[0], &raw const pk[0]);
        });
        Timer::end_measurement("pqm4: Encapsulate ML-KEM 1024", start);

        let start = Timer::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::crypto_kem_dec(&raw mut ss_dec[0], &raw const ct[0], &raw const sk[0]);
        });
        Timer::end_measurement("pqm4: Decapsulate ML-KEM 1024", start);

        assert_eq!(ss_enc, ss_dec);
    }
    board::exit()
}
