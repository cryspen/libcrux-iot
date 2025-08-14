use super::*;

macro_rules! parameter_set {
    ($parameter_module:ident, $feature:literal) => {
        #[cfg(feature = $feature)]
        pub mod $parameter_module {
            use super::*;
            use crate::ml_dsa_generic::$parameter_module::{
                SIGNATURE_SIZE, SIGNING_KEY_SIZE, VERIFICATION_KEY_SIZE,
            };

            pub(crate) fn generate_key_pair(
                randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
                signing_key: &mut [u8; SIGNING_KEY_SIZE],
                verification_key: &mut [u8; VERIFICATION_KEY_SIZE],
            ) {
                instantiations::portable::$parameter_module::generate_key_pair(
                    randomness,
                    signing_key,
                    verification_key,
                );
            }

            #[cfg(feature = "acvp")]
            pub(crate) fn sign_internal(
                signing_key: &[u8; SIGNING_KEY_SIZE],
                message: &[u8],
                randomness: [u8; SIGNING_RANDOMNESS_SIZE],
            ) -> Result<MLDSASignature<SIGNATURE_SIZE>, SigningError> {
                instantiations::portable::$parameter_module::sign_internal(
                    signing_key,
                    message,
                    randomness,
                )
            }

            pub(crate) fn sign(
                signing_key: &[u8; SIGNING_KEY_SIZE],
                message: &[u8],
                context: &[u8],
                randomness: [u8; SIGNING_RANDOMNESS_SIZE],
            ) -> Result<MLDSASignature<SIGNATURE_SIZE>, SigningError> {
                instantiations::portable::$parameter_module::sign(
                    signing_key,
                    message,
                    context,
                    randomness,
                )
            }

            pub(crate) fn sign_pre_hashed_shake128(
                signing_key: &[u8; SIGNING_KEY_SIZE],
                message: &[u8],
                context: &[u8],
                pre_hash_buffer: &mut [u8],
                randomness: [u8; SIGNING_RANDOMNESS_SIZE],
            ) -> Result<MLDSASignature<SIGNATURE_SIZE>, SigningError> {
                instantiations::portable::$parameter_module::sign_pre_hashed_shake128(
                    signing_key,
                    message,
                    context,
                    pre_hash_buffer,
                    randomness,
                )
            }

            #[cfg(feature = "acvp")]
            pub(crate) fn verify_internal(
                verification_key_serialized: &[u8; VERIFICATION_KEY_SIZE],
                message: &[u8],
                signature_serialized: &[u8; SIGNATURE_SIZE],
            ) -> Result<(), VerificationError> {
                instantiations::portable::$parameter_module::verify_internal(
                    verification_key_serialized,
                    message,
                    signature_serialized,
                )
            }

            pub(crate) fn verify(
                verification_key_serialized: &[u8; VERIFICATION_KEY_SIZE],
                message: &[u8],
                context: &[u8],
                signature_serialized: &[u8; SIGNATURE_SIZE],
            ) -> Result<(), VerificationError> {
                instantiations::portable::$parameter_module::verify(
                    verification_key_serialized,
                    message,
                    context,
                    signature_serialized,
                )
            }

            pub(crate) fn verify_pre_hashed_shake128(
                verification_key_serialized: &[u8; VERIFICATION_KEY_SIZE],
                message: &[u8],
                context: &[u8],
                pre_hash_buffer: &mut [u8],
                signature_serialized: &[u8; SIGNATURE_SIZE],
            ) -> Result<(), VerificationError> {
                instantiations::portable::$parameter_module::verify_pre_hashed_shake128(
                    verification_key_serialized,
                    message,
                    context,
                    pre_hash_buffer,
                    signature_serialized,
                )
            }
        }
    };
}

parameter_set!(ml_dsa_44, "mldsa44");
parameter_set!(ml_dsa_65, "mldsa65");
parameter_set!(ml_dsa_87, "mldsa87");
