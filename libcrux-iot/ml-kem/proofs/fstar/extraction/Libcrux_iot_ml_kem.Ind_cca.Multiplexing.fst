module Libcrux_iot_ml_kem.Ind_cca.Multiplexing
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let validate_public_key (v_K v_PUBLIC_KEY_SIZE: usize) (public_key: t_Array u8 v_PUBLIC_KEY_SIZE) =
  Libcrux_iot_ml_kem.Ind_cca.Instantiations.Portable.validate_public_key v_K
    v_PUBLIC_KEY_SIZE
    public_key

let validate_private_key
      (v_K v_SECRET_KEY_SIZE v_CIPHERTEXT_SIZE: usize)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  Libcrux_iot_ml_kem.Ind_cca.Instantiations.Portable.validate_private_key v_K
    v_SECRET_KEY_SIZE
    v_CIPHERTEXT_SIZE
    private_key
    ciphertext

let generate_keypair
      (v_K v_K_SQUARED v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1:
          usize)
      (randomness: t_Array u8 (mk_usize 64))
     =
  Libcrux_iot_ml_kem.Ind_cca.Instantiations.Portable.generate_keypair v_K
    v_K_SQUARED
    v_CPA_PRIVATE_KEY_SIZE
    v_PRIVATE_KEY_SIZE
    v_PUBLIC_KEY_SIZE
    v_ETA1
    v_ETA1_RANDOMNESS_SIZE
    v_PRF_OUTPUT_SIZE1
    randomness

let encapsulate
      (v_K v_K_SQUARED v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2:
          usize)
      (public_key: Libcrux_iot_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (mk_usize 32))
     =
  Libcrux_iot_ml_kem.Ind_cca.Instantiations.Portable.encapsulate v_K v_K_SQUARED v_CIPHERTEXT_SIZE
    v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
    v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
    v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2 public_key randomness

let decapsulate
      (v_K v_K_SQUARED v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  Libcrux_iot_ml_kem.Ind_cca.Instantiations.Portable.decapsulate v_K v_K_SQUARED v_SECRET_KEY_SIZE
    v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
    v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
    v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE private_key ciphertext
