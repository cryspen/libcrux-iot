#![no_main]
#![no_std]

use core::hint::black_box;
use core::panic::PanicInfo;

#[cfg(feature = "mldsa44")]
use libcrux_iot_ml_dsa::ml_dsa_44 as mldsa;
#[cfg(feature = "mldsa65")]
use libcrux_iot_ml_dsa::ml_dsa_65 as mldsa;
#[cfg(feature = "mldsa87")]
use libcrux_iot_ml_dsa::ml_dsa_87 as mldsa;

#[cfg(feature = "mldsa-sign")]
use libcrux_iot_ml_dsa::MLDSASigningKey;

#[cfg(feature = "mldsa-verify")]
use libcrux_iot_ml_dsa::{MLDSASignature, MLDSAVerificationKey};

#[cfg(feature = "mldsa-sign")]
mod sign {
    #[cfg(feature = "mldsa44")]
    pub const KEY: [u8; 2560] = [0; _];
    #[cfg(feature = "mldsa65")]
    pub const KEY: [u8; 4032] = [0; _];
    #[cfg(feature = "mldsa87")]
    pub const KEY: [u8; 4896] = [0; _];
}

#[cfg(feature = "mldsa-verify")]
mod verify {
    #[cfg(feature = "mldsa44")]
    pub const KEY: [u8; 1312] = [0; _];
    #[cfg(feature = "mldsa65")]
    pub const KEY: [u8; 1952] = [0; _];
    #[cfg(feature = "mldsa87")]
    pub const KEY: [u8; 2592] = [0; _];

    #[cfg(feature = "mldsa44")]
    pub const SIG: [u8; 2420] = [0; _];
    #[cfg(feature = "mldsa65")]
    pub const SIG: [u8; 3309] = [0; _];
    #[cfg(feature = "mldsa87")]
    pub const SIG: [u8; 4627] = [0; _];
}

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}

#[cortex_m_rt::entry]
fn main() -> ! {
    #[cfg(feature = "mldsa-keygen")]
    let _ = black_box(mldsa::generate_key_pair(black_box([0; _])));
    #[cfg(feature = "mldsa-sign")]
    let _ = black_box(mldsa::sign(
        black_box(&MLDSASigningKey::new(sign::KEY)),
        black_box(&[]),
        black_box(&[]),
        black_box([0; _]),
    ));

    #[cfg(feature = "mldsa-verify")]
    let _ = black_box(mldsa::verify(
        black_box(&MLDSAVerificationKey::new(verify::KEY)),
        black_box(&[]),
        black_box(&[]),
        black_box(&MLDSASignature::new(verify::SIG)),
    ));

    loop {}
}
