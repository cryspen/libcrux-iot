use libcrux_traits::aead::{arrayref, consts, slice, typed_owned};

use crate::{
    NONCE_LEN, TAG_LEN, aes_gcm_128, aes_gcm_256,
    implementations::{AesGcm128, AesGcm256, PortableAesGcm128, PortableAesGcm256},
};

/// Macro to implement the libcrux_traits public API traits
///
/// For the blanket impl of `typed_refs::Aead` to take place,
/// the `$type` must implement `Copy` and `PartialEq`.
macro_rules! impl_traits_public_api {
    ($type:ty, $keylen:expr, $taglen:expr, $noncelen:expr) => {
        // prerequisite for typed_owned::Aead
        impl consts::AeadConsts for $type {
            const KEY_LEN: usize = $keylen;
            const TAG_LEN: usize = $taglen;
            const NONCE_LEN: usize = $noncelen;
        }
        // implement typed_owned::Aead
        typed_owned::impl_aead_typed_owned!($type, $keylen, $taglen, $noncelen);
    };
}

/// Macro to implement the different structs and multiplexing.
macro_rules! api {
    ($mod_name:ident, $variant:ident, $multiplexing:ty, $portable:ident) => {
        mod $mod_name {
            use super::*;
            use libcrux_secrets::{U8, DeclassifyRef, DeclassifyRefMut};

            use libcrux_traits::aead::arrayref::{DecryptError, EncryptError, KeyGenError};
            use $variant::KEY_LEN;

            pub type Key = [U8; KEY_LEN];
            pub type Tag = [U8; TAG_LEN];
            pub type Nonce = [U8; NONCE_LEN];

            mod _libcrux_traits_apis_multiplex {
                use super::*;

                // implement `libcrux_traits` slice trait
                slice::impl_aead_slice_trait!($multiplexing => KEY_LEN, TAG_LEN, NONCE_LEN);

                // implement `libcrux_traits` public API traits
                impl_traits_public_api!($multiplexing, KEY_LEN, TAG_LEN, NONCE_LEN);

                /// The plaintext length must be equal to the ciphertext length.
                impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $multiplexing {
                    fn keygen(key: &mut [U8; KEY_LEN], rand: &[U8; KEY_LEN]) -> Result<(), KeyGenError> {
                        *key = *rand;
                        Ok(())
                    }

                    fn encrypt(
                        ciphertext: &mut [u8],
                        tag: &mut Tag,
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        plaintext: &[U8],
                    ) -> Result<(), EncryptError> {
                        if plaintext.len() / crate::aes::AES_BLOCK_LEN >= (u32::MAX - 1) as usize {
                            return Err(EncryptError::PlaintextTooLong);
                        }

                        if plaintext.len() != ciphertext.len() {
                            return Err(EncryptError::WrongCiphertextLength);
                        }
                        $portable::encrypt(ciphertext, tag, key, nonce, aad, plaintext)
                    }

                    fn decrypt(
                        plaintext: &mut [U8],
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        ciphertext: &[u8],
                        tag: &Tag,
                    ) -> Result<(), DecryptError> {
                        if plaintext.len() / crate::aes::AES_BLOCK_LEN >= (u32::MAX - 1) as usize {
                            return Err(DecryptError::PlaintextTooLong);
                        }

                        if plaintext.len() != ciphertext.len() {
                            return Err(DecryptError::WrongPlaintextLength);
                        }

                        $portable::decrypt(plaintext, key, nonce, aad, ciphertext, tag)
                    }
                }
            }

            mod _libcrux_traits_apis_portable {
                use super::*;

                // implement `libcrux_traits` slice trait
                slice::impl_aead_slice_trait!($portable => KEY_LEN, TAG_LEN, NONCE_LEN);

                // implement `libcrux_traits` public API traits
                impl_traits_public_api!($portable, KEY_LEN, TAG_LEN, NONCE_LEN);

                /// The plaintext length must be equal to the ciphertext length.
                impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $portable {
                    fn keygen(key: &mut [U8; KEY_LEN], rand: &[U8; KEY_LEN]) -> Result<(), KeyGenError> {
                        *key = *rand;
                        Ok(())
                    }

                    fn encrypt(
                        ciphertext: &mut [u8],
                        tag: &mut Tag,
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        plaintext: &[U8],
                    ) -> Result<(), EncryptError> {
                        assert_eq!(plaintext.len(), ciphertext.len());
                        // declassify: for now, we only implement the libcrux-traits APIs in a secrets
                        // aware way, but don't use libcrux-secrets internally within this crate.
                        // Therefore, we need perform declassify operations at the boundaries between
                        // the libcrux-traits APIs and the internal ones.
                        ciphertext.copy_from_slice(plaintext.declassify_ref());
                        crate::portable::$variant::encrypt(key.declassify_ref(), nonce.declassify_ref(), aad.into_iter(), ciphertext, tag.declassify_ref_mut())
                    }

                    fn decrypt(
                        plaintext: &mut [U8],
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        ciphertext: &[u8],
                        tag: &Tag,
                    ) -> Result<(), DecryptError> {
                        assert_eq!(plaintext.len(), ciphertext.len());
                        // declassify: for now, we only implement the libcrux-traits APIs in a secrets
                        // aware way, but don't use libcrux-secrets internally within this crate.
                        // Therefore, we need perform declassify operations at the boundaries between
                        // the libcrux-traits APIs and the internal ones.
                        let plaintext = plaintext.declassify_ref_mut();
                        plaintext.copy_from_slice(ciphertext);
                        crate::portable::$variant::decrypt(key.declassify_ref(), nonce.declassify_ref(), aad.into_iter(), tag.declassify_ref(), plaintext)
                    }
                }
            }
        }
    };
}

api!(aes128, aes_gcm_128, AesGcm128, PortableAesGcm128);

api!(aes256, aes_gcm_256, AesGcm256, PortableAesGcm256);
