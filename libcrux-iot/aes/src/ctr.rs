//! AES ctr mode implementation.
//!
//! This implementation is generic over the [`AESState`], which has different,
//! platform dependent implementations.
//!
//! This get's instantiated in [`aes128_ctr`] and [`aes256_ctr`].

use crate::{aes::*, platform::AESState};

#[cfg(test)]
mod test128;

mod aes128_ctr;
mod aes256_ctr;

pub(crate) use aes128_ctr::*;
pub(crate) use aes256_ctr::*;

/// The ctr nonce length. This is different from the AES nonce length
/// [`crate::NONCE_LEN`].
const NONCE_LEN: usize = 16;

/// Generic AES CTR context.
pub(crate) struct AesCtrContext<T: AESState, const NUM_KEYS: usize> {
    pub(crate) extended_key: ExtendedKey<T, NUM_KEYS>,
    pub(crate) ctr_nonce: [u8; NONCE_LEN],
}

impl<T: AESState, const NUM_KEYS: usize> AesCtrContext<T, NUM_KEYS> {
    #[inline]
    fn aes_ctr_set_nonce(&mut self, nonce: &[u8]) {
        debug_assert!(nonce.len() == crate::NONCE_LEN);

        self.ctr_nonce[0..crate::NONCE_LEN].copy_from_slice(nonce);
    }

    #[inline]
    fn aes_ctr_key_block(&self, ctr: u32, out: &mut [u8]) {
        debug_assert!(out.len() == AES_BLOCK_LEN);

        let mut st_init = self.ctr_nonce;
        st_init[12..16].copy_from_slice(&ctr.to_be_bytes());
        let mut st = T::new();

        st.load_block(&st_init);

        block_cipher(&mut st, &self.extended_key);

        st.store_block(out);
    }

    #[inline]
    fn aes_ctr_xor_block(&self, ctr: u32, payload: &mut [u8]) {
        debug_assert!(payload.len() <= AES_BLOCK_LEN);

        let mut st_init = self.ctr_nonce;
        st_init[12..16].copy_from_slice(&ctr.to_be_bytes());
        let mut st = T::new();
        st.load_block(&st_init);

        block_cipher(&mut st, &self.extended_key);

        st.xor_block(payload);
    }

    #[inline]
    fn aes_ctr_xor_blocks(&self, ctr: u32, payload: &mut [u8]) {
        debug_assert!(payload.len().is_multiple_of(AES_BLOCK_LEN));
        // If payload.len() / AES_BLOCK_LEN == u32::MAX - 1 and we start with
        // ctr == 2 then we'll wrap to 0 below and we'll repeat the initial key
        // block
        debug_assert!(payload.len() / AES_BLOCK_LEN < (u32::MAX - 1) as usize);

        let blocks = payload.len() / AES_BLOCK_LEN;
        for i in 0..blocks {
            let offset = i * AES_BLOCK_LEN;
            self.aes_ctr_xor_block(
                ctr.wrapping_add(i as u32),
                &mut payload[offset..offset + AES_BLOCK_LEN],
            );
        }
    }

    #[inline]
    fn aes_ctr_update(&self, ctr: u32, payload: &mut [u8]) {
        debug_assert!(payload.len() / AES_BLOCK_LEN < u32::MAX as usize);

        let blocks = payload.len() / AES_BLOCK_LEN;
        self.aes_ctr_xor_blocks(ctr, &mut payload[0..blocks * AES_BLOCK_LEN]);

        let last = payload.len() - payload.len() % AES_BLOCK_LEN;
        if last < payload.len() {
            self.aes_ctr_xor_block(ctr.wrapping_add(blocks as u32), &mut payload[last..]);
        }
    }
}
