module Libcrux_iot_ml_kem.Ind_cca.Multiplexing
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

val validate_public_key (v_K v_PUBLIC_KEY_SIZE: usize) (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
    : Prims.Pure bool
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        v_PUBLIC_KEY_SIZE =.
        ((v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize) +! mk_usize 32
          <:
          usize))
      (fun _ -> Prims.l_True)

val validate_private_key
      (v_K v_SECRET_KEY_SIZE v_CIPHERTEXT_SIZE: usize)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure bool
      (requires
        (match v_K <: usize with
          | Rust_primitives.Integers.MkInt 2 ->
            v_SECRET_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem512.v_SECRET_KEY_SIZE
          | Rust_primitives.Integers.MkInt 3 ->
            v_SECRET_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem768.v_SECRET_KEY_SIZE
          | Rust_primitives.Integers.MkInt 4 ->
            v_SECRET_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem1024.v_SECRET_KEY_SIZE
          | _ -> false))
      (fun _ -> Prims.l_True)

val generate_keypair
      (v_K v_K_SQUARED v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1:
          usize)
      (randomness: t_Array u8 (mk_usize 64))
    : Prims.Pure (Libcrux_iot_ml_kem.Types.t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      (requires
        (v_K =. mk_usize 2 && v_PRIVATE_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem512.v_SECRET_KEY_SIZE ||
        v_K =. mk_usize 3 && v_PRIVATE_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem768.v_SECRET_KEY_SIZE ||
        v_K =. mk_usize 4 && v_PRIVATE_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem1024.v_SECRET_KEY_SIZE) &&
        v_K_SQUARED =. (v_K *! v_K <: usize) &&
        (v_ETA1 =. mk_usize 3 || v_ETA1 =. mk_usize 2) &&
        v_ETA1_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA1 <: usize) &&
        v_CPA_PRIVATE_KEY_SIZE =.
        (v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize) &&
        v_PRF_OUTPUT_SIZE1 =. (v_K *! v_ETA1_RANDOMNESS_SIZE <: usize) &&
        v_PUBLIC_KEY_SIZE =.
        ((v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize) +! mk_usize 32
          <:
          usize))
      (fun _ -> Prims.l_True)

val encapsulate
      (v_K v_K_SQUARED v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2:
          usize)
      (public_key: Libcrux_iot_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure
      (Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (mk_usize 32))
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        v_K_SQUARED =. (v_K *! v_K <: usize) &&
        (v_ETA1 =. mk_usize 3 || v_ETA1 =. mk_usize 2) &&
        v_ETA1_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA1 <: usize) &&
        v_PRF_OUTPUT_SIZE1 =. (v_K *! v_ETA1_RANDOMNESS_SIZE <: usize) &&
        v_ETA2 =. mk_usize 2 &&
        v_ETA2_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA2 <: usize) &&
        v_PRF_OUTPUT_SIZE2 =. (v_K *! v_ETA2_RANDOMNESS_SIZE <: usize) &&
        (v_VECTOR_U_COMPRESSION_FACTOR =. mk_usize 10 &&
        v_C1_BLOCK_SIZE =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 20 <: usize) ||
        v_VECTOR_U_COMPRESSION_FACTOR =. mk_usize 11 &&
        v_C1_BLOCK_SIZE =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 22 <: usize)) &&
        (v_VECTOR_V_COMPRESSION_FACTOR =. mk_usize 4 && v_C2_SIZE =. mk_usize 128 ||
        v_VECTOR_V_COMPRESSION_FACTOR =. mk_usize 5 && v_C2_SIZE =. mk_usize 160) &&
        v_C1_SIZE =. (v_K *! v_C1_BLOCK_SIZE <: usize) &&
        v_CIPHERTEXT_SIZE =. (v_C1_SIZE +! v_C2_SIZE <: usize) &&
        v_T_AS_NTT_ENCODED_SIZE =.
        (Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT *! v_K <: usize) &&
        v_PUBLIC_KEY_SIZE =. (v_T_AS_NTT_ENCODED_SIZE +! mk_usize 32 <: usize))
      (fun _ -> Prims.l_True)

val decapsulate
      (v_K v_K_SQUARED v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (mk_usize 32))
      (requires
        (v_K =. mk_usize 2 && v_SECRET_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem512.v_SECRET_KEY_SIZE &&
        v_CPA_SECRET_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem512.v_CPA_PKE_SECRET_KEY_SIZE &&
        v_PUBLIC_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem512.v_CPA_PKE_PUBLIC_KEY_SIZE ||
        v_K =. mk_usize 3 && v_SECRET_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem768.v_SECRET_KEY_SIZE &&
        v_CPA_SECRET_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem768.v_CPA_PKE_SECRET_KEY_SIZE &&
        v_PUBLIC_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem768.v_CPA_PKE_PUBLIC_KEY_SIZE ||
        v_K =. mk_usize 4 && v_SECRET_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem1024.v_SECRET_KEY_SIZE &&
        v_CPA_SECRET_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem1024.v_CPA_PKE_SECRET_KEY_SIZE &&
        v_PUBLIC_KEY_SIZE =. Libcrux_iot_ml_kem.Mlkem1024.v_CPA_PKE_PUBLIC_KEY_SIZE) &&
        v_K_SQUARED =. (v_K *! v_K <: usize) &&
        (v_ETA1 =. mk_usize 3 || v_ETA1 =. mk_usize 2) &&
        v_ETA1_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA1 <: usize) &&
        v_PRF_OUTPUT_SIZE1 =. (v_K *! v_ETA1_RANDOMNESS_SIZE <: usize) &&
        v_ETA2 =. mk_usize 2 &&
        v_ETA2_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA2 <: usize) &&
        v_PRF_OUTPUT_SIZE2 =. (v_K *! v_ETA2_RANDOMNESS_SIZE <: usize) &&
        (v_VECTOR_U_COMPRESSION_FACTOR =. mk_usize 10 &&
        v_C1_BLOCK_SIZE =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 20 <: usize) ||
        v_VECTOR_U_COMPRESSION_FACTOR =. mk_usize 11 &&
        v_C1_BLOCK_SIZE =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 22 <: usize)) &&
        (v_VECTOR_V_COMPRESSION_FACTOR =. mk_usize 4 && v_C2_SIZE =. mk_usize 128 ||
        v_VECTOR_V_COMPRESSION_FACTOR =. mk_usize 5 && v_C2_SIZE =. mk_usize 160) &&
        v_C1_SIZE =. (v_K *! v_C1_BLOCK_SIZE <: usize) &&
        v_CIPHERTEXT_SIZE =. (v_C1_SIZE +! v_C2_SIZE <: usize) &&
        v_T_AS_NTT_ENCODED_SIZE =.
        (Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT *! v_K <: usize) &&
        v_CIPHERTEXT_SIZE =.
        (((v_K *! mk_usize 32 <: usize) *! v_VECTOR_U_COMPRESSION_FACTOR <: usize) +!
          (mk_usize 32 *! v_VECTOR_V_COMPRESSION_FACTOR <: usize)
          <:
          usize) &&
        v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =.
        (Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE +! v_CIPHERTEXT_SIZE <: usize))
      (fun _ -> Prims.l_True)
