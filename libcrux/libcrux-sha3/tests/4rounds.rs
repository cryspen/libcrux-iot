#[test]
fn keccak_4rounds_print() {
    let mut s = libcrux_sha3::portable::incremental::shake128_init();
    libcrux_sha3::portable::incremental::keccakf1660_4rounds(&mut s);
    println!("{s:?}")
}
