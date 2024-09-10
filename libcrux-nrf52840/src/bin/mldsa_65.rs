#![no_main]
#![no_std]

use libcrux_ml_dsa::ml_dsa_65;
use libcrux_nrf52840 as _; // global logger + panicking-behavior + memory layout
use nrf52840_hal as hal;

// Resolution in µs
const RTC_RESOLUTION: f32 = 30.517;

#[cortex_m_rt::entry]
fn main() -> ! {
    let board = hal::pac::Peripherals::take().unwrap();

    let clock = nrf52840_hal::clocks::Clocks::new(board.CLOCK);
    clock.start_lfclk();

    let rtc = nrf52840_hal::rtc::Rtc::new(board.RTC0, 0).unwrap();

    let key_generation_seed = [3u8; 32];
    defmt::println!("Generating 100 key pairs");
    let counter_start = rtc.get_counter();
    rtc.enable_counter();
    for _ in 0..100 {
        let _ = ml_dsa_65::generate_key_pair(key_generation_seed);
    }
    rtc.disable_counter();
    let counter_end = rtc.get_counter();
    let counter_keygen_total = counter_end - counter_start;
    let counter_keygen_avg = counter_keygen_total as f32 / 100.0;
    let time_keygen_avg = counter_keygen_avg * RTC_RESOLUTION;
    defmt::println!(
        "Took {=f32} µs to generate key pair on average",
        time_keygen_avg
    );

    let signing_randomness = [4u8; 32];
    let message = [5u8; 1024];

    let keypair = ml_dsa_65::generate_key_pair(key_generation_seed);

    defmt::println!("Signing 1024 bytes 100 times.");
    let counter_start = rtc.get_counter();
    rtc.enable_counter();
    for _ in 0..100 {
        let _ = ml_dsa_65::sign(&keypair.signing_key, &message, signing_randomness);
    }
    rtc.disable_counter();
    let counter_end = rtc.get_counter();
    let counter_sign_total = counter_end - counter_start;
    let counter_sign_avg = counter_sign_total as f32 / 100.0;
    let time_sign_avg = counter_sign_avg * RTC_RESOLUTION;
    defmt::println!("Took {=f32} µs to sign on average", time_sign_avg);

    let signature = ml_dsa_65::sign(&keypair.signing_key, &message, signing_randomness);

    defmt::println!("Verifying 100 times.");
    let counter_start = rtc.get_counter();
    rtc.enable_counter();
    for _ in 0..100 {
        let _ = ml_dsa_65::verify(&keypair.verification_key, &message, &signature).unwrap();
    }
    let counter_end = rtc.get_counter();
    let counter_verify_total = counter_end - counter_start;
    let counter_verify_avg = counter_verify_total as f32 / 100.0;
    let time_verify_avg = counter_verify_avg * RTC_RESOLUTION;
    defmt::println!("Took {=f32} µs to verify on average", time_verify_avg);

    libcrux_nrf52840::exit()
}
