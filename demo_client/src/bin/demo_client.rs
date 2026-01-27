#![no_std]
#![no_main]

use defmt::{panic, *};
use defmt_rtt as _; // global logger
use embassy_executor::Spawner;
use embassy_futures::join::join;
use embassy_stm32::rng::{Instance as RngInstance, Rng};
use embassy_stm32::usb::{Driver, Instance as UsbInstance};
use embassy_stm32::{Config, bind_interrupts, peripherals, rng, usb};
use embassy_usb::Builder;
use embassy_usb::class::cdc_acm::{CdcAcmClass, State};
use embassy_usb::driver::EndpointError;
use libcrux_iot_ml_dsa::ml_dsa_65::{self, MLDSA65Signature, MLDSA65VerificationKey};
use libcrux_iot_ml_kem::mlkem768::{MlKem768Ciphertext, MlKem768PublicKey};
use panic_probe as _;

// TODO: Update this counter and send it over encrypted under the
// shared secret, every time a message arrives.
// use core::sync::atomic::AtomicUsize;
// static COUNTER: AtomicUsize = AtomicUsize::new(0);

const VK: [u8; 1952] = [
    31, 37, 215, 153, 90, 137, 0, 82, 53, 54, 125, 134, 105, 73, 18, 130, 2, 190, 25, 213, 70, 233,
    166, 249, 140, 165, 134, 91, 115, 196, 53, 21, 165, 79, 75, 211, 138, 252, 52, 238, 222, 114,
    137, 176, 19, 159, 28, 48, 224, 189, 151, 30, 56, 69, 90, 228, 160, 157, 81, 114, 117, 45, 140,
    75, 130, 68, 206, 143, 231, 254, 133, 38, 112, 242, 68, 155, 37, 144, 161, 78, 94, 17, 207,
    186, 116, 253, 190, 15, 101, 195, 58, 18, 98, 103, 177, 18, 190, 239, 246, 31, 58, 108, 185,
    220, 206, 154, 41, 112, 208, 170, 16, 38, 254, 44, 153, 151, 203, 122, 155, 22, 78, 188, 56,
    132, 68, 53, 114, 85, 85, 125, 35, 136, 48, 154, 80, 66, 120, 238, 67, 203, 205, 26, 63, 39,
    90, 37, 55, 114, 170, 26, 167, 88, 16, 102, 248, 217, 42, 189, 94, 115, 154, 135, 62, 73, 108,
    113, 79, 255, 79, 231, 202, 1, 46, 42, 107, 108, 187, 119, 52, 8, 198, 202, 237, 25, 155, 126,
    70, 108, 255, 222, 28, 64, 100, 35, 11, 107, 238, 215, 183, 240, 88, 53, 33, 167, 215, 121,
    106, 39, 211, 221, 167, 60, 69, 116, 205, 188, 12, 22, 167, 190, 42, 199, 24, 242, 149, 154,
    235, 29, 78, 107, 147, 164, 201, 43, 158, 201, 13, 191, 67, 167, 38, 11, 32, 207, 203, 50, 101,
    66, 66, 51, 93, 133, 55, 177, 231, 95, 103, 222, 200, 103, 174, 83, 133, 28, 126, 142, 157, 58,
    152, 200, 48, 1, 194, 10, 8, 21, 62, 9, 255, 168, 30, 98, 93, 40, 104, 136, 177, 80, 240, 24,
    161, 177, 72, 1, 212, 30, 8, 247, 137, 143, 233, 113, 166, 154, 113, 64, 9, 116, 128, 49, 193,
    251, 103, 183, 182, 181, 159, 152, 121, 65, 108, 136, 100, 4, 8, 115, 192, 11, 249, 23, 64,
    189, 79, 147, 34, 7, 59, 23, 59, 98, 47, 238, 184, 108, 149, 125, 196, 65, 156, 196, 125, 4,
    176, 72, 191, 65, 242, 58, 155, 95, 251, 53, 166, 168, 56, 247, 241, 174, 72, 217, 227, 53, 30,
    153, 76, 180, 43, 217, 105, 241, 123, 197, 80, 164, 89, 10, 27, 173, 164, 60, 132, 204, 21,
    222, 191, 52, 115, 68, 241, 196, 255, 65, 201, 41, 185, 89, 34, 29, 19, 176, 159, 243, 0, 98,
    159, 78, 150, 51, 11, 90, 104, 31, 95, 40, 65, 122, 35, 187, 97, 229, 121, 108, 107, 244, 77,
    35, 62, 203, 201, 1, 215, 54, 63, 77, 21, 118, 232, 233, 168, 225, 193, 5, 119, 144, 117, 78,
    37, 51, 128, 174, 108, 110, 14, 141, 226, 149, 216, 192, 55, 139, 232, 160, 14, 98, 72, 249,
    118, 177, 190, 126, 109, 151, 150, 226, 245, 22, 88, 163, 67, 113, 194, 67, 164, 205, 203, 251,
    26, 28, 134, 204, 44, 216, 66, 105, 233, 247, 5, 93, 171, 121, 70, 30, 94, 226, 177, 106, 255,
    202, 106, 59, 55, 17, 146, 47, 168, 49, 28, 177, 253, 125, 155, 115, 18, 28, 227, 146, 51, 195,
    214, 52, 239, 107, 115, 46, 172, 183, 87, 147, 216, 22, 87, 50, 164, 133, 151, 216, 62, 4, 163,
    132, 87, 28, 95, 241, 84, 228, 191, 7, 147, 66, 107, 214, 13, 238, 212, 57, 188, 193, 170, 250,
    232, 181, 253, 174, 248, 126, 44, 86, 51, 227, 18, 134, 147, 44, 147, 255, 44, 194, 182, 187,
    213, 142, 14, 183, 12, 142, 9, 183, 0, 204, 218, 134, 173, 181, 21, 204, 22, 211, 226, 161,
    216, 188, 77, 95, 181, 165, 79, 91, 188, 127, 113, 7, 167, 237, 81, 14, 190, 85, 46, 181, 78,
    113, 147, 180, 69, 112, 135, 231, 187, 128, 100, 242, 5, 169, 231, 159, 156, 12, 218, 235, 76,
    12, 18, 166, 36, 182, 171, 54, 153, 62, 238, 72, 154, 95, 114, 99, 194, 244, 185, 196, 253, 77,
    193, 236, 1, 70, 18, 17, 4, 55, 141, 103, 14, 172, 102, 96, 63, 173, 19, 83, 2, 39, 156, 250,
    219, 202, 29, 104, 151, 98, 8, 239, 123, 172, 43, 245, 252, 231, 60, 112, 41, 63, 129, 233, 52,
    128, 215, 216, 52, 38, 222, 192, 174, 157, 246, 189, 195, 143, 118, 83, 100, 24, 11, 15, 68,
    13, 94, 87, 129, 136, 212, 191, 252, 61, 30, 80, 251, 50, 138, 117, 71, 9, 127, 98, 33, 79,
    180, 223, 253, 27, 142, 15, 51, 152, 47, 68, 111, 116, 7, 78, 210, 199, 181, 7, 142, 126, 10,
    60, 207, 17, 0, 216, 245, 143, 88, 8, 202, 29, 174, 52, 237, 66, 203, 162, 38, 1, 8, 88, 109,
    119, 130, 65, 83, 140, 48, 186, 79, 193, 53, 79, 25, 20, 242, 62, 49, 127, 141, 76, 159, 216,
    16, 172, 122, 167, 207, 242, 5, 169, 55, 173, 122, 57, 160, 248, 38, 180, 158, 53, 215, 44, 96,
    180, 3, 248, 91, 32, 148, 144, 131, 169, 114, 247, 108, 207, 160, 45, 245, 48, 26, 88, 82, 106,
    81, 60, 251, 50, 209, 63, 54, 6, 17, 56, 117, 178, 96, 200, 175, 138, 143, 236, 145, 239, 53,
    132, 153, 225, 103, 227, 110, 105, 170, 101, 63, 95, 54, 235, 224, 51, 39, 103, 134, 30, 211,
    141, 104, 144, 153, 240, 70, 242, 174, 76, 42, 185, 26, 151, 85, 191, 140, 64, 54, 31, 100,
    155, 62, 196, 65, 40, 152, 76, 148, 146, 17, 32, 103, 82, 38, 157, 173, 66, 242, 11, 17, 179,
    111, 224, 51, 128, 153, 250, 78, 150, 31, 10, 110, 30, 105, 56, 78, 29, 117, 0, 117, 176, 176,
    172, 122, 196, 194, 187, 105, 167, 124, 0, 99, 155, 27, 12, 255, 220, 45, 215, 217, 114, 133,
    131, 124, 234, 236, 205, 186, 207, 127, 248, 161, 95, 172, 245, 160, 204, 57, 149, 13, 227,
    209, 54, 63, 73, 174, 74, 251, 223, 166, 44, 56, 83, 25, 86, 124, 186, 139, 102, 200, 229, 136,
    181, 89, 129, 9, 181, 149, 30, 130, 154, 152, 174, 39, 81, 234, 96, 194, 89, 215, 17, 191, 114,
    169, 182, 159, 165, 22, 118, 111, 2, 54, 196, 121, 245, 214, 144, 50, 211, 39, 12, 225, 189,
    45, 2, 103, 247, 30, 41, 58, 148, 141, 226, 40, 106, 68, 195, 49, 232, 212, 23, 245, 125, 200,
    219, 17, 206, 180, 3, 148, 21, 112, 164, 246, 157, 82, 2, 168, 94, 45, 76, 61, 47, 168, 127,
    225, 136, 138, 80, 70, 8, 239, 126, 51, 191, 223, 161, 203, 63, 218, 38, 58, 170, 82, 81, 106,
    89, 151, 152, 3, 64, 213, 216, 148, 88, 116, 223, 12, 162, 247, 137, 232, 30, 149, 227, 195,
    203, 125, 126, 234, 82, 212, 140, 220, 45, 239, 194, 15, 99, 19, 157, 192, 94, 180, 186, 52,
    33, 15, 167, 80, 244, 250, 135, 45, 128, 137, 111, 48, 104, 208, 46, 136, 189, 92, 243, 157,
    130, 230, 95, 208, 177, 121, 150, 128, 43, 248, 98, 34, 124, 237, 81, 243, 224, 24, 30, 214,
    175, 199, 75, 141, 175, 176, 150, 208, 81, 77, 102, 245, 77, 221, 148, 176, 75, 235, 222, 119,
    235, 188, 30, 62, 201, 36, 60, 96, 39, 231, 98, 121, 113, 66, 155, 210, 179, 16, 189, 149, 241,
    21, 16, 145, 93, 146, 90, 66, 7, 73, 229, 77, 104, 82, 195, 156, 254, 232, 65, 93, 18, 173,
    190, 203, 111, 30, 214, 90, 106, 95, 117, 210, 121, 133, 214, 10, 112, 12, 19, 182, 39, 163,
    144, 63, 144, 247, 133, 190, 240, 224, 157, 10, 210, 164, 186, 76, 45, 88, 222, 83, 120, 109,
    46, 149, 165, 30, 251, 248, 5, 247, 162, 19, 28, 165, 129, 6, 82, 56, 222, 22, 193, 92, 229,
    10, 253, 17, 182, 149, 49, 114, 222, 102, 63, 121, 204, 219, 18, 82, 38, 47, 189, 194, 161, 11,
    191, 207, 189, 143, 135, 70, 130, 86, 150, 121, 62, 9, 106, 102, 92, 3, 94, 96, 108, 62, 91,
    217, 175, 115, 107, 133, 8, 81, 174, 149, 206, 36, 75, 83, 50, 34, 23, 254, 55, 53, 41, 178,
    163, 58, 156, 34, 25, 35, 135, 164, 98, 113, 220, 41, 146, 113, 233, 211, 65, 229, 144, 164,
    192, 163, 181, 202, 214, 157, 24, 160, 48, 85, 70, 211, 141, 149, 41, 6, 27, 88, 101, 181, 186,
    253, 245, 160, 64, 197, 145, 14, 154, 171, 25, 121, 85, 211, 41, 35, 73, 106, 121, 138, 127,
    82, 89, 18, 164, 77, 123, 155, 180, 4, 45, 134, 152, 250, 101, 6, 252, 248, 5, 216, 106, 26,
    152, 76, 59, 40, 118, 19, 0, 175, 135, 53, 21, 130, 11, 196, 79, 253, 42, 234, 197, 223, 80,
    106, 154, 143, 73, 18, 91, 49, 186, 143, 211, 232, 48, 72, 140, 72, 60, 194, 159, 31, 134, 236,
    155, 0, 50, 202, 246, 27, 190, 134, 73, 66, 156, 0, 170, 148, 195, 88, 73, 188, 140, 124, 10,
    56, 206, 50, 84, 244, 166, 78, 97, 126, 248, 188, 137, 213, 89, 21, 0, 192, 138, 245, 183, 179,
    37, 181, 231, 219, 219, 82, 226, 74, 215, 65, 190, 171, 59, 202, 169, 77, 188, 88, 111, 112,
    242, 185, 103, 229, 88, 6, 171, 127, 39, 139, 47, 112, 207, 181, 155, 233, 175, 235, 84, 207,
    11, 201, 180, 99, 11, 46, 96, 80, 112, 189, 246, 24, 160, 255, 6, 110, 235, 10, 184, 245, 70,
    51, 200, 121, 239, 84, 13, 2, 166, 51, 100, 89, 35, 38, 129, 143, 133, 71, 46, 181, 44, 189,
    191, 54, 145, 158, 185, 113, 101, 23, 1, 10, 119, 204, 155, 110, 4, 71, 139, 239, 249, 210, 55,
    148, 240, 105, 151, 192, 244, 89, 21, 18, 224, 89, 34, 161, 17, 33, 8, 40, 79, 183, 201, 27,
    205, 108, 197, 245, 115, 190, 180, 96, 52, 249, 22, 152, 59, 156, 28, 204, 10, 166, 0, 76, 199,
    131, 226, 29, 240, 47, 227, 200, 69, 74, 249, 165, 251, 190, 242, 185, 39, 7, 70, 137, 217, 29,
    209, 62, 38, 158, 117, 61, 43, 221, 249, 146, 214, 27, 138, 196, 153, 21, 192, 158, 235, 27,
    86, 40, 128, 177, 238, 170, 187, 102, 171, 91, 255, 110, 94, 51, 230, 153, 54, 33, 141, 163,
    225, 91, 145, 186, 64, 153, 102, 155, 13, 176, 34, 92, 184, 218, 152, 206, 44, 141, 162, 209,
    218, 71, 237, 166, 253, 224, 185, 190, 243, 157, 218, 206, 113, 184, 164, 104, 229, 188, 255,
    76, 221, 41, 113, 14, 208, 82, 235, 142, 172, 129, 173, 181, 173, 18, 102, 58, 255, 200, 114,
    238, 81, 117, 234, 189, 29, 133, 219, 237, 205, 138, 147, 197, 162, 10, 124, 37, 160, 144, 37,
    27, 44, 138, 143, 118, 56, 164, 112, 78, 241, 152, 84, 245, 231, 180, 181, 169, 22, 23, 8, 94,
    127, 58, 252, 14, 199, 93, 148, 28, 164, 209, 254, 212, 163, 188, 130, 212, 12, 141, 229, 182,
    104, 155, 69, 250, 242, 167, 114, 127, 79, 25, 151, 250, 207, 174, 31, 53, 175, 235, 199, 140,
    73, 160, 87, 52, 45, 217, 114, 58, 246, 46, 139, 39, 201, 106, 158, 119, 4, 139, 35, 238, 110,
    194, 200, 33, 244, 50, 150, 27, 31, 116, 223, 72, 10, 106, 134,
];

bind_interrupts!(struct Irqs {
    OTG_FS => usb::InterruptHandler<peripherals::USB_OTG_FS>;
    RNG => rng::InterruptHandler<peripherals::RNG>;
});

// If you are trying this and your USB device doesn't connect, the most
// common issues are the RCC config and vbus_detection
//
// See https://embassy.dev/book/#_the_usb_examples_are_not_working_on_my_board_is_there_anything_else_i_need_to_configure
// for more information.
#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    info!("Hello World!");

    let mut config = Config::default();
    {
        use embassy_stm32::rcc::*;
        config.rcc.hsi48 = Some(Hsi48Config {
            sync_from_usb: true,
        }); // needed for USB
        config.rcc.sys = Sysclk::PLL1_R;
        config.rcc.hsi = true;
        config.rcc.pll = Some(Pll {
            source: PllSource::HSI,
            prediv: PllPreDiv::DIV1,
            mul: PllMul::MUL10,
            divp: None,
            divq: None,
            divr: Some(PllRDiv::DIV2), // sysclk 80Mhz (16 / 1 * 10 / 2)
        });
        config.rcc.mux.clk48sel = mux::Clk48sel::HSI48;
    }
    let p = embassy_stm32::init(config);

    // Create the driver, from the HAL.
    let mut ep_out_buffer = [0u8; 256];
    let mut config = embassy_stm32::usb::Config::default();

    // Do not enable vbus_detection. This is a safe default that works in all boards.
    // However, if your USB device is self-powered (can stay powered on if USB is unplugged), you need
    // to enable vbus_detection to comply with the USB spec. If you enable it, the board
    // has to support it or USB won't work at all. See docs on `vbus_detection` for details.
    config.vbus_detection = false;

    let driver = Driver::new_fs(
        p.USB_OTG_FS,
        Irqs,
        p.PA12,
        p.PA11,
        &mut ep_out_buffer,
        config,
    );

    // Create embassy-usb Config
    let mut config = embassy_usb::Config::new(0xc0de, 0xcafe);
    config.max_packet_size_0 = 64;
    config.manufacturer = Some("Embassy");
    config.product = Some("USB-serial example");
    config.serial_number = Some("12345678");

    // Create embassy-usb DeviceBuilder using the driver and config.
    // It needs some buffers for building the descriptors.
    let mut config_descriptor = [0; 256];
    let mut bos_descriptor = [0; 256];
    let mut control_buf = [0; 64];

    let mut state = State::new();

    let mut builder = Builder::new(
        driver,
        config,
        &mut config_descriptor,
        &mut bos_descriptor,
        &mut [], // no msos descriptors
        &mut control_buf,
    );

    let mut rng = Rng::new(p.RNG, Irqs);

    // Create classes on the builder.
    let mut class = CdcAcmClass::new(&mut builder, &mut state, 64);

    // Build the builder.
    let mut usb = builder.build();

    // Run the USB device.
    let usb_fut = usb.run();

    // Do stuff with the class!
    let echo_fut = async {
        loop {
            class.wait_connection().await;
            info!("Connected");
            let _ = echo(&mut class, &mut rng).await;
            info!("Disconnected");
        }
    };

    // Run everything concurrently.
    // If we had made everything `'static` above instead, we could do this using separate tasks instead.
    join(usb_fut, echo_fut).await;
}

struct Disconnected {}

impl From<EndpointError> for Disconnected {
    fn from(val: EndpointError) -> Self {
        match val {
            EndpointError::BufferOverflow => panic!("Buffer overflow"),
            EndpointError::Disabled => Disconnected {},
        }
    }
}

async fn echo<'d, T: UsbInstance + 'd, U: RngInstance + 'd>(
    class: &mut CdcAcmClass<'d, Driver<'d, T>>,
    rng: &mut Rng<'d, U>,
) -> Result<(), Disconnected> {
    let mut encapsulation_key_buffer = [0u8; MlKem768PublicKey::len()];
    let mut signature = MLDSA65Signature::zero();
    let mut index = 0;
    let mut buf = [0u8; 64];

    // Read an encapsulation key.
    info!("Reading ML-KEM 768 encapsulation key");
    while index < MlKem768PublicKey::len() {
        let n = class.read_packet(&mut buf).await?;
        info!(".. read {} bytes", n);
        encapsulation_key_buffer[index..index + n].copy_from_slice(&buf[..n]);
        index += n;
    }
    info!("Done reading ML-KEM 768 encapsulation key\n");

    index = 0;

    info!("Reading ML-DSA 65 signature");
    while index < MLDSA65Signature::len() {
        let n = class.read_packet(&mut buf).await?;
        info!(".. read {} bytes", n);
        signature.as_mut_slice()[index..index + n].copy_from_slice(&buf[..n]);
        index += n;
    }
    info!("Done reading ML-DSA 65 signature\n");

    info!("Verifying signature on encapsulation key");
    let mut send_encapsulation = false;
    let result = ml_dsa_65::verify(
        &MLDSA65VerificationKey::new(VK),
        &encapsulation_key_buffer,
        b"Libcrux-IoT Demo",
        &signature,
    );
    if result.is_ok() {
        info!(".. Signature verified!");
        send_encapsulation = true;
    } else {
        info!(".. Verification failed!");
    }

    let mut response_ciphertext = MlKem768Ciphertext::default();
    let mut result_shared_secret = [0u8; 32];
    // We send one full packet to indicate the response status:
    // - [0u8;64] -> Error (+ all zero encapsulation)
    // - [1u8;64] -> Success (+ real encapsulation)
    let mut status = [0u8; 64];
    if send_encapsulation {
        let encapsulation_key = MlKem768PublicKey::from(&encapsulation_key_buffer);
        let mut encapsulation_randomness = [0u8; libcrux_iot_ml_kem::ENCAPS_SEED_SIZE];
        unwrap!(rng.async_fill_bytes(&mut encapsulation_randomness).await);
        let (encapsulation, shared_secret) =
            libcrux_iot_ml_kem::mlkem768::encapsulate(&encapsulation_key, encapsulation_randomness);

        info!("Sending encapsulated shared secret");
        response_ciphertext
            .as_mut_slice()
            .copy_from_slice(encapsulation.as_slice());
        result_shared_secret.copy_from_slice(&shared_secret);
        status = [1u8; 64];
    }

    index = 0;
    let full_packets = MlKem768Ciphertext::len() / 64;
    let remainder = MlKem768Ciphertext::len() % 64;

    // Send response status
    class.write_packet(status.as_slice()).await?;
    // Send encapsulation
    for packet in 0..full_packets {
        let packet_offset = packet * 64;
        class
            .write_packet(&response_ciphertext.as_slice()[packet_offset..packet_offset + 64])
            .await?;
    }
    if remainder != 0 {
        let mut buf = [0u8; 64];
        buf[..remainder].copy_from_slice(
            &response_ciphertext.as_slice()[full_packets * 64..full_packets * 64 + remainder],
        );
        class
            .write_packet(&response_ciphertext.as_slice()[index..])
            .await?;
    } else {
        // Write a zero-length package in this case, to make the host process the last full-length package.
        class.write_packet(&[]).await?;
    }

    info!("Shared secret is {}", result_shared_secret);

    Ok(())
}
