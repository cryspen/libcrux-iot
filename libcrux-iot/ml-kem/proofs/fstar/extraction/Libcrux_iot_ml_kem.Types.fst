module Libcrux_iot_ml_kem.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int.Classify_public in
  let open Libcrux_secrets.Traits in
  ()

/// An ML-KEM Private key
type t_MlKemPrivateKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (v_SIZE: usize)
    : Core_models.Convert.t_From (t_MlKemPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post
    =
    (fun (value: t_Array u8 v_SIZE) (result: t_MlKemPrivateKey v_SIZE) -> result.f_value =. value);
    f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_MlKemPrivateKey v_SIZE
  }

///An ML-KEM Ciphertext
type t_MlKemCiphertext (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12 (v_SIZE: usize)
    : Core_models.Convert.t_From (t_MlKemCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post
    =
    (fun (value: t_Array u8 v_SIZE) (result: t_MlKemCiphertext v_SIZE) -> result.f_value =. value);
    f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_MlKemCiphertext v_SIZE
  }

///An ML-KEM Public key
type t_MlKemPublicKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19 (v_SIZE: usize)
    : Core_models.Convert.t_From (t_MlKemPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post
    =
    (fun (value: t_Array u8 v_SIZE) (result: t_MlKemPublicKey v_SIZE) -> result.f_value =. value);
    f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_MlKemPublicKey v_SIZE
  }

/// A reference to the raw byte slice.
let impl_20__as_slice (v_SIZE: usize) (self: t_MlKemPublicKey v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 v_SIZE = result in
          result =. self.f_value) = self.f_value

/// An ML-KEM key pair
type t_MlKemKeyPair (v_PRIVATE_KEY_SIZE: usize) (v_PUBLIC_KEY_SIZE: usize) = {
  f_sk:t_MlKemPrivateKey v_PRIVATE_KEY_SIZE;
  f_pk:t_MlKemPublicKey v_PUBLIC_KEY_SIZE
}

/// Create a new [`MlKemKeyPair`] from the secret and public key.
let impl_21__from
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE = result in
          result.f_sk == sk /\ result.f_pk == pk) =
  { f_sk = sk; f_pk = pk } <: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE

/// Unpack an incoming private key into it\'s different parts.
/// We have this here in types to extract into a common core for C.
let unpack_private_key (v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE: usize) (private_key: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8 & t_Slice u8 & t_Slice u8)
      (requires
        v_CPA_SECRET_KEY_SIZE <=. Libcrux_iot_ml_kem.Mlkem1024.v_CPA_PKE_SECRET_KEY_SIZE &&
        v_PUBLIC_KEY_SIZE <=. Libcrux_iot_ml_kem.Mlkem1024.v_CPA_PKE_PUBLIC_KEY_SIZE &&
        (Core_models.Slice.impl__len #u8 private_key <: usize) >=.
        ((v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE <: usize) +!
          Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE
          <:
          usize))
      (ensures
        fun result ->
          let result:(t_Slice u8 & t_Slice u8 & t_Slice u8 & t_Slice u8) = result in
          (Core_models.Slice.impl__len #u8 result._1 <: usize) =. v_CPA_SECRET_KEY_SIZE &&
          (Core_models.Slice.impl__len #u8 result._2 <: usize) =. v_PUBLIC_KEY_SIZE &&
          (Core_models.Slice.impl__len #u8 result._3 <: usize) =.
          Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE &&
          (Core_models.Slice.impl__len #u8 result._4 <: usize) =.
          ((Core_models.Slice.impl__len #u8 private_key <: usize) -!
            ((v_CPA_SECRET_KEY_SIZE +! v_PUBLIC_KEY_SIZE <: usize) +!
              Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE
              <:
              usize)
            <:
            usize)) =
  let (ind_cpa_secret_key: t_Slice u8), (secret_key: t_Slice u8) =
    Core_models.Slice.impl__split_at #u8 private_key v_CPA_SECRET_KEY_SIZE
  in
  let (ind_cpa_public_key: t_Slice u8), (secret_key: t_Slice u8) =
    Core_models.Slice.impl__split_at #u8 secret_key v_PUBLIC_KEY_SIZE
  in
  let (ind_cpa_public_key_hash: t_Slice u8), (implicit_rejection_value: t_Slice u8) =
    Core_models.Slice.impl__split_at #u8 secret_key Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE
  in
  ind_cpa_secret_key,
  Libcrux_secrets.Traits.f_declassify_ref #(t_Slice u8)
    #FStar.Tactics.Typeclasses.solve
    ind_cpa_public_key,
  Libcrux_secrets.Traits.f_declassify_ref #(t_Slice u8)
    #FStar.Tactics.Typeclasses.solve
    ind_cpa_public_key_hash,
  implicit_rejection_value
  <:
  (t_Slice u8 & t_Slice u8 & t_Slice u8 & t_Slice u8)
