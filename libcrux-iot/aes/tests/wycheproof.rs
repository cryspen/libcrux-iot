use libcrux_secrets::{ClassifyRef, ClassifyRefMut, DeclassifyRef};
use wycheproof::{aead::Test, TestResult};

fn run<Cipher: libcrux_iot_aes::Aead>(test: &Test, cipher: Cipher) {
    let mut ciphertext = vec![0u8; test.pt.len()];
    let mut plaintext = vec![0u8; test.pt.len()];
    let mut tag_bytes = [0u8; 16];

    let key = cipher.new_key(test.key.classify_ref()).unwrap();
    let nonce = cipher.new_nonce(test.nonce.classify_ref()).unwrap();
    let tag = cipher.new_tag_mut(tag_bytes.classify_ref_mut()).unwrap();

    key.encrypt(
        &mut ciphertext,
        tag,
        nonce,
        &test.aad,
        test.pt.classify_ref(),
    )
    .unwrap();

    let tag = cipher.new_tag(tag_bytes.classify_ref()).unwrap();
    key.decrypt(
        plaintext.classify_ref_mut(),
        nonce,
        &test.aad,
        &ciphertext,
        tag,
    )
    .unwrap();

    assert_eq!(plaintext.as_slice(), test.pt.as_slice());

    if test.result == TestResult::Valid {
        assert_eq!(test.ct.as_slice(), &ciphertext);
        assert_eq!(test.tag.as_slice(), tag.as_ref().declassify_ref());
    } else {
        let ct_ok = test.ct.as_slice() == ciphertext;
        let tag_ok = test.tag.as_slice() == tag.as_ref().declassify_ref();
        assert!(!ct_ok || !tag_ok);
    }
}

fn test_variant(cipher: impl libcrux_iot_aes::Aead) {
    let test_set = wycheproof::aead::TestSet::load(wycheproof::aead::TestName::AesGcm).unwrap();

    // Ensure we ran some tests.
    let mut tested = false;

    for test_group in test_set.test_groups {
        println!(
            "* Group key size:{} tag size:{} nonce size:{}",
            test_group.key_size, test_group.tag_size, test_group.nonce_size,
        );

        if test_group.nonce_size != 96 {
            println!("  Skipping unsupported nonce size");
            continue;
        }

        if test_group.key_size / 8 == cipher.key_len() {
            for test in test_group.tests {
                run(&test, cipher);
                tested = true;
            }
        }
    }

    assert!(tested, "No tests were run.")
}

#[test]
fn aes128_portable() {
    test_variant(libcrux_iot_aes::aes_gcm_128::portable::PortableAesGcm128);
}

#[test]
fn aes256_portable() {
    test_variant(libcrux_iot_aes::aes_gcm_256::portable::PortableAesGcm256);
}
