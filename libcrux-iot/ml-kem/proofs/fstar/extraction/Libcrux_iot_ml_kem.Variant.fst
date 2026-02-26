module Libcrux_iot_ml_kem.Variant
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Hash_functions in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Variant t_MlKem =
  {
    f_kdf_pre
    =
    (fun
        (v_K: usize)
        (v_CIPHERTEXT_SIZE: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
        (shared_secret: t_Slice u8)
        (_: t_Array u8 v_CIPHERTEXT_SIZE)
        (out: t_Slice u8)
        ->
        (Core_models.Slice.impl__len #u8 shared_secret <: usize) =. mk_usize 32 &&
        (Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 32);
    f_kdf_post
    =
    (fun
        (v_K: usize)
        (v_CIPHERTEXT_SIZE: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
        (shared_secret: t_Slice u8)
        (_: t_Array u8 v_CIPHERTEXT_SIZE)
        (out: t_Slice u8)
        (out_future: t_Slice u8)
        ->
        (Core_models.Slice.impl__len #u8 out_future <: usize) =.
        (Core_models.Slice.impl__len #u8 out <: usize));
    f_kdf
    =
    (fun
        (v_K: usize)
        (v_CIPHERTEXT_SIZE: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
        (shared_secret: t_Slice u8)
        (_: t_Array u8 v_CIPHERTEXT_SIZE)
        (out: t_Slice u8)
        ->
        let out:t_Slice u8 = Core_models.Slice.impl__copy_from_slice #u8 out shared_secret in
        out);
    f_entropy_preprocess_pre
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
        (randomness: t_Slice u8)
        (out: t_Slice u8)
        ->
        (Core_models.Slice.impl__len #u8 randomness <: usize) =. mk_usize 32 &&
        (Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 32);
    f_entropy_preprocess_post
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
        (randomness: t_Slice u8)
        (out: t_Slice u8)
        (out_future: t_Slice u8)
        ->
        (Core_models.Slice.impl__len #u8 out_future <: usize) =.
        (Core_models.Slice.impl__len #u8 out <: usize));
    f_entropy_preprocess
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
        (randomness: t_Slice u8)
        (out: t_Slice u8)
        ->
        let out:t_Slice u8 = Core_models.Slice.impl__copy_from_slice #u8 out randomness in
        out);
    f_cpa_keygen_seed_pre
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
        (key_generation_seed: t_Slice u8)
        (out: t_Slice u8)
        ->
        (Core_models.Slice.impl__len #u8 key_generation_seed <: usize) =. mk_usize 32 &&
        (Core_models.Slice.impl__len #u8 out <: usize) =. mk_usize 64);
    f_cpa_keygen_seed_post
    =
    (fun
        (v_K: usize)
        (#v_Hasher: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
        (key_generation_seed: t_Slice u8)
        (out: t_Slice u8)
        (out_future: t_Slice u8)
        ->
        (Core_models.Slice.impl__len #u8 out_future <: usize) =.
        (Core_models.Slice.impl__len #u8 out <: usize));
    f_cpa_keygen_seed
    =
    fun
      (v_K: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
        i0:
        Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (key_generation_seed: t_Slice u8)
      (out: t_Slice u8)
      ->
      let seed:t_Array u8 (mk_usize 33) =
        Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
              #FStar.Tactics.Typeclasses.solve
              (mk_u8 0)
            <:
            u8)
          (mk_usize 33)
      in
      let seed:t_Array u8 (mk_usize 33) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range seed
          ({
              Core_models.Ops.Range.f_start = mk_usize 0;
              Core_models.Ops.Range.f_end
              =
              Libcrux_iot_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (seed.[ {
                    Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end
                    =
                    Libcrux_iot_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              key_generation_seed
            <:
            t_Slice u8)
      in
      let seed:t_Array u8 (mk_usize 33) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed
          Libcrux_iot_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
          (Libcrux_secrets.Traits.f_classify #u8
              #FStar.Tactics.Typeclasses.solve
              (cast (v_K <: usize) <: u8)
            <:
            u8)
      in
      let _:Prims.unit =
        eq_intro seed (Seq.append key_generation_seed (Seq.create 1 (cast v_K <: u8)))
      in
      let out:t_Slice u8 =
        Libcrux_iot_ml_kem.Hash_functions.f_G #v_Hasher
          #FStar.Tactics.Typeclasses.solve
          (seed <: t_Slice u8)
          out
      in
      out
  }
