#![no_main]
#![no_std]

use libcrux_ml_kem::mlkem1024 as mlkem;
use libcrux_nrf52840 as _; // global logger + panicking-behavior + memory layout
use nrf52840_hal as hal;

// Resolution in µs
const RTC_RESOLUTION: f32 = 30.517;

#[cortex_m_rt::entry]
fn main() -> ! {
    let board = hal::pac::Peripherals::take().unwrap();
    defmt::println!("Starting main!");

    let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];

    let clock = nrf52840_hal::clocks::Clocks::new(board.CLOCK);
    clock.start_lfclk();

    let rtc = nrf52840_hal::rtc::Rtc::new(board.RTC0, 0).unwrap();

    defmt::println!("Generating 100 key pairs");
    let counter_start = rtc.get_counter();
    rtc.enable_counter();
    for _ in 0..100 {
        let _ = mlkem::generate_key_pair(randomness_gen);
    }
    rtc.disable_counter();
    let counter_end = rtc.get_counter();
    let counter_keygen_total = counter_end - counter_start;
    let counter_keygen_avg = counter_keygen_total as f32/ 100.0;
    let time_keygen_avg = counter_keygen_avg * RTC_RESOLUTION;
    defmt::println!("Took {=f32} µs to generate key pair on average", time_keygen_avg);

    let pair = mlkem::generate_key_pair(randomness_gen);
    let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
    defmt::println!("Encapsulating 100 times.");
    let counter_start = rtc.get_counter();
    rtc.enable_counter();
    for _ in 0..100 {
        let _ = mlkem::encapsulate(pair.public_key(), randomness_encaps);
    }
    rtc.disable_counter();
    let counter_end = rtc.get_counter();
    let counter_encaps_total = counter_end - counter_start;
    let counter_encaps_avg = counter_encaps_total as f32/ 100.0;
    let time_encaps_avg = counter_encaps_avg * RTC_RESOLUTION;
    defmt::println!("Took {=f32} µs to encapsulate on average", time_encaps_avg);

    let (ct, ss) = mlkem::encapsulate(pair.public_key(), randomness_encaps);

    defmt::println!("Decapsulating 100 times.");
    let counter_start = rtc.get_counter();
    rtc.enable_counter();
    for _ in 0..100 {
        let _ = mlkem::decapsulate(pair.private_key(), &ct);
    }
    let counter_end = rtc.get_counter();
    let counter_decaps_total = counter_end - counter_start;
    let counter_decaps_avg = counter_decaps_total as f32/ 100.0;
    let time_decaps_avg = counter_decaps_avg * RTC_RESOLUTION;
    defmt::println!("Took {=f32} µs to decapsulate on average", time_decaps_avg);


    let ss_decaps = mlkem::decapsulate(pair.private_key(), &ct);
    assert_eq!(ss, ss_decaps);

    libcrux_nrf52840::exit()
}
