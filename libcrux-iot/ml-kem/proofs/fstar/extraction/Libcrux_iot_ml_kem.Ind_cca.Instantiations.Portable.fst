module Libcrux_iot_ml_kem.Ind_cca.Instantiations.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Hash_functions in
  let open Libcrux_iot_ml_kem.Hash_functions.Portable in
  let open Libcrux_iot_ml_kem.Variant in
  let open Libcrux_iot_ml_kem.Vector.Portable in
  let open Libcrux_iot_ml_kem.Vector.Traits in
  ()

let generate_keypair
      (v_K v_K_SQUARED v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1:
          usize)
      (randomness: t_Array u8 (mk_usize 64))
     =
  Libcrux_iot_ml_kem.Ind_cca.generate_keypair v_K v_K_SQUARED v_CPA_PRIVATE_KEY_SIZE
    v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1
    #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #Libcrux_iot_ml_kem.Hash_functions.Portable.t_PortableHash #Libcrux_iot_ml_kem.Variant.t_MlKem
    randomness

let validate_public_key (v_K v_PUBLIC_KEY_SIZE: usize) (public_key: t_Array u8 v_PUBLIC_KEY_SIZE) =
  Libcrux_iot_ml_kem.Ind_cca.validate_public_key v_K
    v_PUBLIC_KEY_SIZE
    #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    public_key

let validate_private_key
      (v_K v_SECRET_KEY_SIZE v_CIPHERTEXT_SIZE: usize)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  Libcrux_iot_ml_kem.Ind_cca.validate_private_key v_K
    v_SECRET_KEY_SIZE
    v_CIPHERTEXT_SIZE
    #Libcrux_iot_ml_kem.Hash_functions.Portable.t_PortableHash
    private_key
    ciphertext

let validate_private_key_only
      (v_K v_SECRET_KEY_SIZE: usize)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
     =
  Libcrux_iot_ml_kem.Ind_cca.validate_private_key_only v_K
    v_SECRET_KEY_SIZE
    #Libcrux_iot_ml_kem.Hash_functions.Portable.t_PortableHash
    private_key

let encapsulate
      (v_K v_K_SQUARED v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2:
          usize)
      (public_key: Libcrux_iot_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (mk_usize 32))
     =
  Libcrux_iot_ml_kem.Ind_cca.encapsulate v_K v_K_SQUARED v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE
    v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR
    v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
    v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2
    #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #Libcrux_iot_ml_kem.Hash_functions.Portable.t_PortableHash #Libcrux_iot_ml_kem.Variant.t_MlKem
    public_key randomness

let decapsulate
      (v_K v_K_SQUARED v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  Libcrux_iot_ml_kem.Ind_cca.decapsulate v_K v_K_SQUARED v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE
    v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE
    v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
    v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
    #Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #Libcrux_iot_ml_kem.Hash_functions.Portable.t_PortableHash #Libcrux_iot_ml_kem.Variant.t_MlKem
    private_key ciphertext
