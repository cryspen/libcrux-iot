use libcrux_ml_dsa::ml_dsa_65;
use rand::{rngs::OsRng, RngCore};

fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

fn main() {
    let key_generation_seed = random_array();
    println!("const KEYGEN_SEED: [u8; 32] = {:?};", key_generation_seed);
    let signing_randomness = random_array();
    println!("const SIG_SEED: [u8; 32] = {:?};", signing_randomness);
    let message = random_array::<1023>();
    println!("const MESSAGE: [u8; 1023] = {:?};", message);

    let keypair = ml_dsa_65::generate_key_pair(key_generation_seed);
    println!(
        "const VK_BYTES: [u8; 1952] = {:?};",
        keypair.verification_key.as_ref()
    );
    println!(
        "const SK_BYTES: [u8; 1952] = {:?};",
        keypair.signing_key.as_ref()
    );
    let sig = ml_dsa_65::sign(&keypair.signing_key, &message, b"", signing_randomness).unwrap();
    println!("const SIG_BYTES: [u8; 3309] = {:?};", sig.as_ref());
}
