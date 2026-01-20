module Libcrux_iot_ml_kem.Variant
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Hash_functions in
  ()

/// This trait collects differences in specification between ML-KEM
/// (FIPS 203) and the Round 3 CRYSTALS-Kyber submission in the
/// NIST PQ competition.
/// cf. FIPS 203, Appendix C
class t_Variant (v_Self: Type0) = {
  f_kdf_pre:
      v_K: usize ->
      v_CIPHERTEXT_SIZE: usize ->
      #v_Hasher: Type0 ->
      {| i0: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |} ->
      shared_secret: t_Slice u8 ->
      ciphertext: t_Array u8 v_CIPHERTEXT_SIZE ->
      out: t_Slice u8
    -> pred:
      Type0
        { (Core_models.Slice.impl__len #u8 shared_secret <: usize) =. mk_usize 32 &&
          (Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 32 ==>
          pred };
  f_kdf_post:
      v_K: usize ->
      v_CIPHERTEXT_SIZE: usize ->
      #v_Hasher: Type0 ->
      {| i0: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |} ->
      shared_secret: t_Slice u8 ->
      ciphertext: t_Array u8 v_CIPHERTEXT_SIZE ->
      out: t_Slice u8 ->
      out_future: t_Slice u8
    -> pred:
      Type0
        { pred ==>
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize) };
  f_kdf:
      v_K: usize ->
      v_CIPHERTEXT_SIZE: usize ->
      #v_Hasher: Type0 ->
      {| i0: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |} ->
      x0: t_Slice u8 ->
      x1: t_Array u8 v_CIPHERTEXT_SIZE ->
      x2: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_kdf_pre v_K v_CIPHERTEXT_SIZE #v_Hasher #i0 x0 x1 x2)
        (fun result -> f_kdf_post v_K v_CIPHERTEXT_SIZE #v_Hasher #i0 x0 x1 x2 result);
  f_entropy_preprocess_pre:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i0: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |} ->
      randomness: t_Slice u8 ->
      out: t_Slice u8
    -> pred:
      Type0
        { (Core_models.Slice.impl__len #u8 randomness <: usize) =. mk_usize 32 &&
          (Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 32 ==>
          pred };
  f_entropy_preprocess_post:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i0: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |} ->
      randomness: t_Slice u8 ->
      out: t_Slice u8 ->
      out_future: t_Slice u8
    -> pred:
      Type0
        { pred ==>
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize) };
  f_entropy_preprocess:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i0: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |} ->
      x0: t_Slice u8 ->
      x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_entropy_preprocess_pre v_K #v_Hasher #i0 x0 x1)
        (fun result -> f_entropy_preprocess_post v_K #v_Hasher #i0 x0 x1 result);
  f_cpa_keygen_seed_pre:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i0: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |} ->
      seed: t_Slice u8 ->
      out: t_Slice u8
    -> pred:
      Type0
        { (Core_models.Slice.impl__len #u8 seed <: usize) =. mk_usize 32 &&
          (Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 64 ==>
          pred };
  f_cpa_keygen_seed_post:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i0: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |} ->
      seed: t_Slice u8 ->
      out: t_Slice u8 ->
      out_future: t_Slice u8
    -> pred:
      Type0
        { pred ==>
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize) };
  f_cpa_keygen_seed:
      v_K: usize ->
      #v_Hasher: Type0 ->
      {| i0: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |} ->
      x0: t_Slice u8 ->
      x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_cpa_keygen_seed_pre v_K #v_Hasher #i0 x0 x1)
        (fun result -> f_cpa_keygen_seed_post v_K #v_Hasher #i0 x0 x1 result)
}
