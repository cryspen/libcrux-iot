use libcrux_ml_kem::{mlkem512, ENCAPS_SEED_SIZE, KEY_GENERATION_SEED_SIZE};

fn main() {
    let randomness = [1u8; KEY_GENERATION_SEED_SIZE];
    let key_pair = mlkem512::generate_key_pair(randomness);

    let randomness = [2u8; ENCAPS_SEED_SIZE];

    let (ciphertext, shared_secret) = mlkem512::encapsulate(key_pair.public_key(), randomness);

    println!("Public Key:");
    println!("{:?}", *key_pair.public_key().as_slice());

    println!("\nPrivate Key:");
    println!("{:?}", *key_pair.private_key().as_slice());

    println!("\nCiphertext:");
    println!("{:?}", *ciphertext.as_slice());

    println!("\nShared Secret:");
    println!("{:?}", shared_secret);
    println!("\n Done");
}
