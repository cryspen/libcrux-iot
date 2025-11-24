use libcrux_secrets::{Classify as _, DeclassifyRef as _, U8};

macro_rules! impl_generic_struct {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        pub struct $name<const SIZE: usize> {
            pub(crate) value: [u8; SIZE],
        }

        impl<const SIZE: usize> Default for $name<SIZE> {
            fn default() -> Self {
                Self { value: [0u8; SIZE] }
            }
        }

        #[hax_lib::attributes]
        impl<const SIZE: usize> AsRef<[u8]> for $name<SIZE> {
            #[ensures(|result| fstar!(r#"$result = ${self_}.f_value"#))]
            fn as_ref(&self) -> &[u8] {
                &self.value
            }
        }

        #[hax_lib::attributes]
        impl<const SIZE: usize> From<[u8; SIZE]> for $name<SIZE> {
            #[ensures(|result| fstar!(r#"${result}.f_value = $value"#))]
            fn from(value: [u8; SIZE]) -> Self {
                Self { value }
            }
        }

        impl<const SIZE: usize> From<&[u8; SIZE]> for $name<SIZE> {
            fn from(value: &[u8; SIZE]) -> Self {
                Self {
                    value: value.clone(),
                }
            }
        }

        impl<const SIZE: usize> From<$name<SIZE>> for [u8; SIZE] {
            fn from(value: $name<SIZE>) -> Self {
                value.value
            }
        }

        impl<const SIZE: usize> TryFrom<&[u8]> for $name<SIZE> {
            type Error = core::array::TryFromSliceError;

            fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
                match value.try_into() {
                    Ok(value) => Ok(Self { value }),
                    Err(e) => Err(e),
                }
            }
        }

        #[hax_lib::attributes]
        impl<const SIZE: usize> $name<SIZE> {
            /// A reference to the raw byte slice.
            #[ensures(|result| fstar!(r#"$result == self.f_value"#))]
            pub fn as_slice(&self) -> &[u8; SIZE] {
                &self.value
            }

            // This is only used for some of the macro callers.
            // #[allow(dead_code)]
            // /// Split this value and return the raw byte slices.
            // pub(crate) fn split_at(&self, mid: usize) -> (&[u8], &[u8]) {
            //     self.value.split_at(mid)
            // }

            /// The number of bytes
            pub const fn len() -> usize {
                SIZE
            }
        }
    };
}

/// An ML-KEM Private key
pub struct MlKemPrivateKey<const SIZE: usize> {
    pub(crate) value: [U8; SIZE],
}
impl<const SIZE: usize> Default for MlKemPrivateKey<SIZE> {
    fn default() -> Self {
        Self {
            value: [0u8.classify(); SIZE],
        }
    }
}
#[hax_lib::attributes]
impl<const SIZE: usize> AsRef<[U8]> for MlKemPrivateKey<SIZE> {
    #[ensures(|result|fstar!(r#"$result = ${self_}.f_value"#))]
    fn as_ref(&self) -> &[U8] {
        &self.value
    }
}
#[hax_lib::attributes]
impl<const SIZE: usize> From<[U8; SIZE]> for MlKemPrivateKey<SIZE> {
    #[ensures(|result|fstar!(r#"${result}.f_value = $value"#))]
    fn from(value: [U8; SIZE]) -> Self {
        Self { value }
    }
}
impl<const SIZE: usize> From<&[U8; SIZE]> for MlKemPrivateKey<SIZE> {
    fn from(value: &[U8; SIZE]) -> Self {
        Self {
            value: value.clone(),
        }
    }
}
impl<const SIZE: usize> From<MlKemPrivateKey<SIZE>> for [U8; SIZE] {
    fn from(value: MlKemPrivateKey<SIZE>) -> Self {
        value.value
    }
}
impl<const SIZE: usize> TryFrom<&[U8]> for MlKemPrivateKey<SIZE> {
    type Error = core::array::TryFromSliceError;
    fn try_from(value: &[U8]) -> Result<Self, Self::Error> {
        match value.try_into() {
            Ok(value) => Ok(Self { value }),
            Err(e) => Err(e),
        }
    }
}
#[hax_lib::attributes]
impl<const SIZE: usize> MlKemPrivateKey<SIZE> {
    #[doc = r" A reference to the raw byte slice."]
    #[ensures(|result|fstar!(r#"$result == self.f_value"#))]
    pub fn as_slice(&self) -> &[U8; SIZE] {
        &self.value
    }
    #[doc = r" The number of bytes"]
    pub const fn len() -> usize {
        SIZE
    }
}

impl_generic_struct!(MlKemCiphertext, "An ML-KEM Ciphertext");
impl_generic_struct!(MlKemPublicKey, "An ML-KEM Public key");

/// An ML-KEM key pair
pub struct MlKemKeyPair<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize> {
    pub(crate) sk: MlKemPrivateKey<PRIVATE_KEY_SIZE>,
    pub(crate) pk: MlKemPublicKey<PUBLIC_KEY_SIZE>,
}

#[hax_lib::attributes]
impl<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize>
    MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>
{
    /// Creates a new [`MlKemKeyPair`].
    pub fn new(sk: [U8; PRIVATE_KEY_SIZE], pk: [u8; PUBLIC_KEY_SIZE]) -> Self {
        Self {
            sk: sk.into(),
            pk: pk.into(),
        }
    }

    /// Create a new [`MlKemKeyPair`] from the secret and public key.
    #[ensures(|result| fstar!(r#"${result}.f_sk == $sk /\ ${result}.f_pk == $pk"#))]
    pub fn from(
        sk: MlKemPrivateKey<PRIVATE_KEY_SIZE>,
        pk: MlKemPublicKey<PUBLIC_KEY_SIZE>,
    ) -> Self {
        Self { sk, pk }
    }

    /// Get a reference to the [`MlKemPublicKey<PUBLIC_KEY_SIZE>`].
    pub fn public_key(&self) -> &MlKemPublicKey<PUBLIC_KEY_SIZE> {
        &self.pk
    }

    /// Get a reference to the [`MlKemPrivateKey<PRIVATE_KEY_SIZE>`].
    pub fn private_key(&self) -> &MlKemPrivateKey<PRIVATE_KEY_SIZE> {
        &self.sk
    }

    /// Get a reference to the raw public key bytes.
    pub fn pk(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        self.pk.as_slice()
    }

    /// Get a reference to the raw private key bytes.
    pub fn sk(&self) -> &[U8; PRIVATE_KEY_SIZE] {
        self.sk.as_slice()
    }

    /// Separate this key into the public and private key.
    pub fn into_parts(
        self,
    ) -> (
        MlKemPrivateKey<PRIVATE_KEY_SIZE>,
        MlKemPublicKey<PUBLIC_KEY_SIZE>,
    ) {
        (self.sk, self.pk)
    }
}

/// Unpack an incoming private key into it's different parts.
///
/// We have this here in types to extract into a common core for C.
#[hax_lib::requires(fstar!(r#"Seq.length private_key >= 
                            v v_CPA_SECRET_KEY_SIZE + v v_PUBLIC_KEY_SIZE + 
                            v Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE"#))]
#[hax_lib::ensures(|result| fstar!(r#"
           let (ind_cpa_secret_key_s,rest) = split $private_key $CPA_SECRET_KEY_SIZE in
           let (ind_cpa_public_key_s,rest) = split rest $PUBLIC_KEY_SIZE in
           let (ind_cpa_public_key_hash_s,implicit_rejection_value_s) = split rest Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE in
           let (ind_cpa_secret_key,ind_cpa_public_key,ind_cpa_public_key_hash,implicit_rejection_value)
               = result in
           ind_cpa_secret_key_s == ind_cpa_secret_key /\
           ind_cpa_public_key_s == ind_cpa_public_key /\
           ind_cpa_public_key_hash_s == ind_cpa_public_key_hash /\
           implicit_rejection_value_s == implicit_rejection_value /\
           Seq.length ind_cpa_secret_key == v v_CPA_SECRET_KEY_SIZE /\
           Seq.length ind_cpa_public_key == v v_PUBLIC_KEY_SIZE /\
           Seq.length ind_cpa_public_key_hash == v Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE /\
           Seq.length implicit_rejection_value == 
           Seq.length private_key - 
             (v v_CPA_SECRET_KEY_SIZE + v v_PUBLIC_KEY_SIZE + v Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE)
           "#))]
pub(crate) fn unpack_private_key<const CPA_SECRET_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize>(
    private_key: &[U8], // len: SECRET_KEY_SIZE
) -> (&[U8], &[u8], &[u8], &[U8]) {
    let (ind_cpa_secret_key, secret_key) = private_key.split_at(CPA_SECRET_KEY_SIZE);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(PUBLIC_KEY_SIZE);
    let (ind_cpa_public_key_hash, implicit_rejection_value) =
        secret_key.split_at(crate::constants::H_DIGEST_SIZE);
    (
        ind_cpa_secret_key,
        // Declassification: This slice of the ML-KEM private key is the ML-KEM
        // public key (see FIPS203, Algorithm 16, line 3), and thus public
        // information.
        ind_cpa_public_key.declassify_ref(),
        // Declassification: This slice of the ML-KEM private key is the
        // hash of the ML-KEM public key (see FIPS203, Algorithm 16, line
        // 3), and thus public information
        ind_cpa_public_key_hash.declassify_ref(),
        implicit_rejection_value,
    )
}
