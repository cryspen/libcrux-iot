use libcrux_iot_ml_dsa::{
    ml_dsa_44::{self, MLDSA44KeyPair, MLDSA44Signature},
    KEY_GENERATION_RANDOMNESS_SIZE, SIGNING_RANDOMNESS_SIZE,
};

use pqcrypto_dilithium;

mod bench_utils;

fn main() {
    bench_group_libcrux!(
        "44 portable",
        ml_dsa_44::portable,
        MLDSA44KeyPair,
        MLDSA44Signature
    );
    bench_group_pqclean!("44", dilithium2);
}
