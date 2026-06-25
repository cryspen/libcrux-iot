use libcrux_iot_aes::{
    aes_gcm_128::{Key, Nonce, Tag},
    AesGcm128,
};
use libcrux_secrets::{Classify, ClassifyRef, ClassifyRefMut};

// tests that an error is returned if ptxt.len() != ctxt.len()
#[test]
fn non_matching_lengths() {
    use libcrux_iot_aes::AeadConsts as _;

    let k: Key = [0; AesGcm128::KEY_LEN].classify().into();
    let nonce: Nonce = [0; AesGcm128::NONCE_LEN].classify().into();
    let mut tag: Tag = [0; AesGcm128::TAG_LEN].classify().into();

    let pt = vec![0; 12];

    k.encrypt(&mut [0; 43], &mut tag, &nonce, b"", pt.classify_ref())
        .unwrap_err();
}

// tests that an error is returned if ptxt is too long
// NOTE: this test is not applicable for pointer widths less than 64.
#[test]
#[cfg(target_pointer_width = "64")]
fn ptxt_too_long() {
    use libcrux_iot_aes::AeadConsts as _;
    use libcrux_traits::aead::arrayref::{DecryptError, EncryptError};

    let k: Key = [0; AesGcm128::KEY_LEN].classify().into();
    let nonce: Nonce = [0; AesGcm128::NONCE_LEN].classify().into();
    let mut tag: Tag = [0; AesGcm128::TAG_LEN].classify().into();

    // unsafely create a slice that is too long
    let pt: &mut [u8] =
        unsafe { std::slice::from_raw_parts_mut(8 as *mut u8, u32::MAX as usize * 16) };

    // check that encryption returns error
    let e = k
        .encrypt(&mut [], &mut tag, &nonce, b"", pt.classify_ref())
        .unwrap_err();
    assert_eq!(e, EncryptError::PlaintextTooLong);

    // check that decryption returns error
    let e = k
        .decrypt(pt.classify_ref_mut(), &nonce, b"", &mut [], &tag)
        .unwrap_err();
    assert_eq!(e, DecryptError::PlaintextTooLong);
}
