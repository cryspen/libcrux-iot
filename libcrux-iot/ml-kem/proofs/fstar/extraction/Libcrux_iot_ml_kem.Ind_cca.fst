module Libcrux_iot_ml_kem.Ind_cca
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Hash_functions in
  let open Libcrux_iot_ml_kem.Types in
  let open Libcrux_iot_ml_kem.Variant in
  let open Libcrux_iot_ml_kem.Vector.Traits in
  let open Libcrux_secrets.Int.Classify_public in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

let serialize_kem_secret_key_mut
      (v_K v_SERIALIZED_KEY_LEN: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (private_key public_key implicit_rejection_value: t_Slice u8)
      (serialized: t_Array u8 v_SERIALIZED_KEY_LEN)
     =
  let pointer:usize = mk_usize 0 in
  let serialized:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core_models.Ops.Range.f_start = pointer;
          Core_models.Ops.Range.f_end
          =
          pointer +! (Core_models.Slice.impl__len #u8 private_key <: usize) <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (serialized.[ {
                Core_models.Ops.Range.f_start = pointer;
                Core_models.Ops.Range.f_end
                =
                pointer +! (Core_models.Slice.impl__len #u8 private_key <: usize) <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          private_key
        <:
        t_Slice u8)
  in
  let pointer:usize = pointer +! (Core_models.Slice.impl__len #u8 private_key <: usize) in
  let serialized:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core_models.Ops.Range.f_start = pointer;
          Core_models.Ops.Range.f_end
          =
          pointer +! (Core_models.Slice.impl__len #u8 public_key <: usize) <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (serialized.[ {
                Core_models.Ops.Range.f_start = pointer;
                Core_models.Ops.Range.f_end
                =
                pointer +! (Core_models.Slice.impl__len #u8 public_key <: usize) <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (Libcrux_secrets.Traits.f_classify_ref #(t_Slice u8)
              #FStar.Tactics.Typeclasses.solve
              public_key
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let pointer:usize = pointer +! (Core_models.Slice.impl__len #u8 public_key <: usize) in
  let serialized:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core_models.Ops.Range.f_start = pointer;
          Core_models.Ops.Range.f_end
          =
          pointer +! Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Libcrux_iot_ml_kem.Hash_functions.f_H #v_Hasher
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_classify_ref #(t_Slice u8)
              #FStar.Tactics.Typeclasses.solve
              public_key
            <:
            t_Slice u8)
          (serialized.[ {
                Core_models.Ops.Range.f_start = pointer;
                Core_models.Ops.Range.f_end
                =
                pointer +! Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let pointer:usize = pointer +! Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE in
  let serialized:t_Array u8 v_SERIALIZED_KEY_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core_models.Ops.Range.f_start = pointer;
          Core_models.Ops.Range.f_end
          =
          pointer +! (Core_models.Slice.impl__len #u8 implicit_rejection_value <: usize) <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (serialized.[ {
                Core_models.Ops.Range.f_start = pointer;
                Core_models.Ops.Range.f_end
                =
                pointer +! (Core_models.Slice.impl__len #u8 implicit_rejection_value <: usize)
                <:
                usize
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          implicit_rejection_value
        <:
        t_Slice u8)
  in
  serialized

let validate_public_key
      (v_K v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key: t_Array u8 v_PUBLIC_KEY_SIZE)
     =
  let
  (deserialized_pk: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K):t_Array
    (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core_models.Array.from_fn #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun e_i ->
          let e_i:usize = e_i in
          Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let deserialized_pk:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Libcrux_iot_ml_kem.Serialize.deserialize_ring_elements_reduced v_K
      #v_Vector
      (public_key.[ {
            Core_models.Ops.Range.f_end
            =
            Libcrux_iot_ml_kem.Constants.ranked_bytes_per_ring_element v_K <: usize
          }
          <:
          Core_models.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
      deserialized_pk
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.repeat (mk_u8 0) v_PUBLIC_KEY_SIZE
  in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.f_ZERO #v_Vector #FStar.Tactics.Typeclasses.solve ()
  in
  let (tmp0: t_Array u8 v_PUBLIC_KEY_SIZE), (tmp1: v_Vector) =
    Libcrux_iot_ml_kem.Ind_cpa.serialize_public_key_mut v_K
      v_PUBLIC_KEY_SIZE
      #v_Vector
      deserialized_pk
      (public_key.[ {
            Core_models.Ops.Range.f_start
            =
            Libcrux_iot_ml_kem.Constants.ranked_bytes_per_ring_element v_K <: usize
          }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
      public_key_serialized
      scratch
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  public_key =. public_key_serialized

let validate_private_key_only
      (v_K v_SECRET_KEY_SIZE: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
     =
  let t:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 32)
  in
  let t:t_Array u8 (mk_usize 32) =
    Libcrux_iot_ml_kem.Hash_functions.f_H #v_Hasher
      #FStar.Tactics.Typeclasses.solve
      (private_key.Libcrux_iot_ml_kem.Types.f_value.[ {
            Core_models.Ops.Range.f_start = mk_usize 384 *! v_K <: usize;
            Core_models.Ops.Range.f_end = (mk_usize 768 *! v_K <: usize) +! mk_usize 32 <: usize
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
      t
  in
  let expected:t_Slice u8 =
    Libcrux_secrets.Traits.f_declassify_ref #(t_Slice u8)
      #FStar.Tactics.Typeclasses.solve
      (private_key.Libcrux_iot_ml_kem.Types.f_value.[ {
            Core_models.Ops.Range.f_start = (mk_usize 768 *! v_K <: usize) +! mk_usize 32 <: usize;
            Core_models.Ops.Range.f_end = (mk_usize 768 *! v_K <: usize) +! mk_usize 64 <: usize
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  (Libcrux_secrets.Traits.f_declassify_ref #(t_Slice u8)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Array.impl_23__as_slice #u8 (mk_usize 32) t <: t_Slice u8)
    <:
    t_Slice u8) =.
  expected

let validate_private_key
      (v_K v_SECRET_KEY_SIZE v_CIPHERTEXT_SIZE: usize)
      (#v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (e_ciphertext: Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     = validate_private_key_only v_K v_SECRET_KEY_SIZE #v_Hasher private_key

let generate_keypair
      (v_K v_K_SQUARED v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_iot_ml_kem.Variant.t_Variant v_Scheme)
      (randomness: t_Array u8 (mk_usize 64))
     =
  let ind_cpa_keypair_randomness:t_Slice u8 =
    randomness.[ {
        Core_models.Ops.Range.f_start = mk_usize 0;
        Core_models.Ops.Range.f_end
        =
        Libcrux_iot_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core_models.Ops.Range.t_Range usize ]
  in
  let implicit_rejection_value:t_Slice u8 =
    randomness.[ {
        Core_models.Ops.Range.f_start
        =
        Libcrux_iot_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core_models.Ops.Range.t_RangeFrom usize ]
  in
  let public_key:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.repeat (mk_u8 0) v_PUBLIC_KEY_SIZE
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      v_PRIVATE_KEY_SIZE
  in
  let ind_cpa_private_key:t_Array u8 v_CPA_PRIVATE_KEY_SIZE =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      v_CPA_PRIVATE_KEY_SIZE
  in
  let scratch:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
  in
  let accumulator:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (mk_i32 0)
        <:
        i32)
      (mk_usize 256)
  in
  let s_cache:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.repeat (Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
        <:
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
  in
  let
  (tmp0: t_Array u8 v_CPA_PRIVATE_KEY_SIZE),
  (tmp1: t_Array u8 v_PUBLIC_KEY_SIZE),
  (tmp2: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp3: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp4: t_Array i32 (mk_usize 256)) =
    Libcrux_iot_ml_kem.Ind_cpa.generate_keypair v_K v_K_SQUARED v_CPA_PRIVATE_KEY_SIZE
      v_PUBLIC_KEY_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 #v_Vector #v_Hasher
      #v_Scheme ind_cpa_keypair_randomness ind_cpa_private_key public_key scratch s_cache
      accumulator
  in
  let ind_cpa_private_key:t_Array u8 v_CPA_PRIVATE_KEY_SIZE = tmp0 in
  let public_key:t_Array u8 v_PUBLIC_KEY_SIZE = tmp1 in
  let scratch:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp2 in
  let s_cache:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = tmp3 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp4 in
  let _:Prims.unit = () in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_kem_secret_key_mut v_K
      v_PRIVATE_KEY_SIZE
      #v_Hasher
      (ind_cpa_private_key <: t_Slice u8)
      (public_key <: t_Slice u8)
      implicit_rejection_value
      secret_key_serialized
  in
  let (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_PRIVATE_KEY_SIZE):Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey
  v_PRIVATE_KEY_SIZE =
    Core_models.Convert.f_from #(Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      #(t_Array u8 v_PRIVATE_KEY_SIZE)
      #FStar.Tactics.Typeclasses.solve
      secret_key_serialized
  in
  Libcrux_iot_ml_kem.Types.impl_21__from v_PRIVATE_KEY_SIZE
    v_PUBLIC_KEY_SIZE
    private_key
    (Core_models.Convert.f_from #(Libcrux_iot_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
        #(t_Array u8 v_PUBLIC_KEY_SIZE)
        #FStar.Tactics.Typeclasses.solve
        public_key
      <:
      Libcrux_iot_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)

let encapsulate
      (v_K v_K_SQUARED v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_iot_ml_kem.Variant.t_Variant v_Scheme)
      (public_key: Libcrux_iot_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (randomness: t_Array u8 (mk_usize 32))
     =
  let processed_randomness:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 32)
  in
  let processed_randomness:t_Array u8 (mk_usize 32) =
    Libcrux_iot_ml_kem.Variant.f_entropy_preprocess #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      #v_Hasher
      (randomness <: t_Slice u8)
      processed_randomness
  in
  let (to_hash: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
    Libcrux_iot_ml_kem.Utils.into_padded_array (mk_usize 64) (processed_randomness <: t_Slice u8)
  in
  let to_hash:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core_models.Ops.Range.f_start = Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      (Libcrux_iot_ml_kem.Hash_functions.f_H #v_Hasher
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Array.impl_23__as_slice #u8
              v_PUBLIC_KEY_SIZE
              (Libcrux_secrets.Traits.f_classify #(t_Array u8 v_PUBLIC_KEY_SIZE)
                  #FStar.Tactics.Typeclasses.solve
                  public_key.Libcrux_iot_ml_kem.Types.f_value
                <:
                t_Array u8 v_PUBLIC_KEY_SIZE)
            <:
            t_Slice u8)
          (to_hash.[ {
                Core_models.Ops.Range.f_start = Libcrux_iot_ml_kem.Constants.v_H_DIGEST_SIZE
              }
              <:
              Core_models.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 64)
  in
  let hashed:t_Array u8 (mk_usize 64) =
    Libcrux_iot_ml_kem.Hash_functions.f_G #v_Hasher
      #FStar.Tactics.Typeclasses.solve
      (to_hash <: t_Slice u8)
      hashed
  in
  let (shared_secret: t_Slice u8), (pseudorandomness: t_Slice u8) =
    Core_models.Slice.impl__split_at #u8
      (hashed <: t_Slice u8)
      Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.repeat (mk_u8 0) v_CIPHERTEXT_SIZE
  in
  let (r_as_ntt: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K):t_Array
    (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core_models.Array.from_fn #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun e_i ->
          let e_i:usize = e_i in
          Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let error_2_:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
  in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.f_ZERO #v_Vector #FStar.Tactics.Typeclasses.solve ()
  in
  let accumulator:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (mk_i32 0)
        <:
        i32)
      (mk_usize 256)
  in
  let cache:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.repeat (Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
        <:
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
  in
  let matrix_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
  in
  let
  (tmp0: t_Array u8 v_CIPHERTEXT_SIZE),
  (tmp1: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp2: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp3: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp4: v_Vector),
  (tmp5: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp6: t_Array i32 (mk_usize 256)) =
    Libcrux_iot_ml_kem.Ind_cpa.encrypt v_K v_K_SQUARED v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE
      v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR
      v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1
      v_PRF_OUTPUT_SIZE2 #v_Vector #v_Hasher
      (Libcrux_iot_ml_kem.Types.impl_20__as_slice v_PUBLIC_KEY_SIZE public_key <: t_Slice u8)
      processed_randomness pseudorandomness ciphertext matrix_entry r_as_ntt error_2_ scratch cache
      accumulator
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE = tmp0 in
  let matrix_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let r_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    tmp2
  in
  let error_2_:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp3 in
  let scratch:v_Vector = tmp4 in
  let cache:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = tmp5 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp6 in
  let _:Prims.unit = () in
  let ciphertext:Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE =
    Core_models.Convert.f_from #(Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
      #(t_Array u8 v_CIPHERTEXT_SIZE)
      #FStar.Tactics.Typeclasses.solve
      ciphertext
  in
  let shared_secret_array:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 32)
  in
  let shared_secret_array:t_Array u8 (mk_usize 32) =
    Libcrux_iot_ml_kem.Variant.f_kdf #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      v_CIPHERTEXT_SIZE
      #v_Hasher
      shared_secret
      ciphertext.Libcrux_iot_ml_kem.Types.f_value
      shared_secret_array
  in
  ciphertext, shared_secret_array
  <:
  (Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (mk_usize 32))

let decapsulate
      (v_K v_K_SQUARED v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_iot_ml_kem.Variant.t_Variant v_Scheme)
      (private_key: Libcrux_iot_ml_kem.Types.t_MlKemPrivateKey v_SECRET_KEY_SIZE)
      (ciphertext: Libcrux_iot_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  let
  (ind_cpa_secret_key: t_Slice u8),
  (ind_cpa_public_key: t_Slice u8),
  (ind_cpa_public_key_hash: t_Slice u8),
  (implicit_rejection_value: t_Slice u8) =
    Libcrux_iot_ml_kem.Types.unpack_private_key v_CPA_SECRET_KEY_SIZE
      v_PUBLIC_KEY_SIZE
      (private_key.Libcrux_iot_ml_kem.Types.f_value <: t_Slice u8)
  in
  let decrypted:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 32)
  in
  let scratch:v_Vector =
    Libcrux_iot_ml_kem.Vector.Traits.f_ZERO #v_Vector #FStar.Tactics.Typeclasses.solve ()
  in
  let accumulator:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (mk_i32 0)
        <:
        i32)
      (mk_usize 256)
  in
  let (tmp0: t_Array u8 (mk_usize 32)), (tmp1: v_Vector), (tmp2: t_Array i32 (mk_usize 256)) =
    Libcrux_iot_ml_kem.Ind_cpa.decrypt v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_V_COMPRESSION_FACTOR #v_Vector ind_cpa_secret_key
      ciphertext.Libcrux_iot_ml_kem.Types.f_value decrypted scratch accumulator
  in
  let decrypted:t_Array u8 (mk_usize 32) = tmp0 in
  let scratch:v_Vector = tmp1 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp2 in
  let _:Prims.unit = () in
  let (to_hash: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
    Libcrux_iot_ml_kem.Utils.into_padded_array (mk_usize 64) (decrypted <: t_Slice u8)
  in
  let to_hash:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core_models.Ops.Range.f_start = Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (to_hash.[ {
                Core_models.Ops.Range.f_start = Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE
              }
              <:
              Core_models.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Libcrux_secrets.Traits.f_classify_ref #(t_Slice u8)
              #FStar.Tactics.Typeclasses.solve
              ind_cpa_public_key_hash
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 64)
  in
  let hashed:t_Array u8 (mk_usize 64) =
    Libcrux_iot_ml_kem.Hash_functions.f_G #v_Hasher
      #FStar.Tactics.Typeclasses.solve
      (to_hash <: t_Slice u8)
      hashed
  in
  let (shared_secret: t_Slice u8), (pseudorandomness: t_Slice u8) =
    Core_models.Slice.impl__split_at #u8
      (hashed <: t_Slice u8)
      Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE
  in
  let (to_hash: t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE):t_Array u8
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Libcrux_iot_ml_kem.Utils.into_padded_array v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
      implicit_rejection_value
  in
  let to_hash:t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core_models.Ops.Range.f_start = Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (to_hash.[ {
                Core_models.Ops.Range.f_start = Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE
              }
              <:
              Core_models.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Core_models.Array.impl_23__as_slice #u8
              v_CIPHERTEXT_SIZE
              (Libcrux_secrets.Traits.f_classify #(t_Array u8 v_CIPHERTEXT_SIZE)
                  #FStar.Tactics.Typeclasses.solve
                  ciphertext.Libcrux_iot_ml_kem.Types.f_value
                <:
                t_Array u8 v_CIPHERTEXT_SIZE)
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let implicit_rejection_shared_secret:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 32)
  in
  let implicit_rejection_shared_secret:t_Array u8 (mk_usize 32) =
    Libcrux_iot_ml_kem.Hash_functions.f_PRF #v_Hasher
      #FStar.Tactics.Typeclasses.solve
      (mk_usize 32)
      (to_hash <: t_Slice u8)
      implicit_rejection_shared_secret
  in
  let expected_ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.repeat (mk_u8 0) v_CIPHERTEXT_SIZE
  in
  let (r_as_ntt: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K):t_Array
    (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core_models.Array.from_fn #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun e_i ->
          let e_i:usize = e_i in
          Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let error_2_:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
  in
  let cache:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.repeat (Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
        <:
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
  in
  let matrix_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
  in
  let
  (tmp0: t_Array u8 v_CIPHERTEXT_SIZE),
  (tmp1: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp2: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp3: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp4: v_Vector),
  (tmp5: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp6: t_Array i32 (mk_usize 256)) =
    Libcrux_iot_ml_kem.Ind_cpa.encrypt v_K v_K_SQUARED v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE
      v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR
      v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1
      v_PRF_OUTPUT_SIZE2 #v_Vector #v_Hasher ind_cpa_public_key decrypted pseudorandomness
      expected_ciphertext matrix_entry r_as_ntt error_2_ scratch cache accumulator
  in
  let expected_ciphertext:t_Array u8 v_CIPHERTEXT_SIZE = tmp0 in
  let matrix_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let r_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    tmp2
  in
  let error_2_:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp3 in
  let scratch:v_Vector = tmp4 in
  let cache:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = tmp5 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp6 in
  let _:Prims.unit = () in
  let implicit_rejection_shared_secret_kdf:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 32)
  in
  let implicit_rejection_shared_secret_kdf:t_Array u8 (mk_usize 32) =
    Libcrux_iot_ml_kem.Variant.f_kdf #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      v_CIPHERTEXT_SIZE
      #v_Hasher
      (implicit_rejection_shared_secret <: t_Slice u8)
      ciphertext.Libcrux_iot_ml_kem.Types.f_value
      implicit_rejection_shared_secret_kdf
  in
  let shared_secret_kdf:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 32)
  in
  let shared_secret_kdf:t_Array u8 (mk_usize 32) =
    Libcrux_iot_ml_kem.Variant.f_kdf #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      v_CIPHERTEXT_SIZE
      #v_Hasher
      shared_secret
      ciphertext.Libcrux_iot_ml_kem.Types.f_value
      shared_secret_kdf
  in
  let shared_secret:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 32)
  in
  let shared_secret:t_Array u8 (mk_usize 32) =
    Libcrux_iot_ml_kem.Constant_time_ops.compare_ciphertexts_select_shared_secret_in_constant_time (Core_models.Array.impl_23__as_slice
          #u8
          v_CIPHERTEXT_SIZE
          (Libcrux_secrets.Traits.f_classify #(t_Array u8 v_CIPHERTEXT_SIZE)
              #FStar.Tactics.Typeclasses.solve
              ciphertext.Libcrux_iot_ml_kem.Types.f_value
            <:
            t_Array u8 v_CIPHERTEXT_SIZE)
        <:
        t_Slice u8)
      (Core_models.Array.impl_23__as_slice #u8
          v_CIPHERTEXT_SIZE
          (Libcrux_secrets.Traits.f_classify #(t_Array u8 v_CIPHERTEXT_SIZE)
              #FStar.Tactics.Typeclasses.solve
              expected_ciphertext
            <:
            t_Array u8 v_CIPHERTEXT_SIZE)
        <:
        t_Slice u8)
      (shared_secret_kdf <: t_Slice u8)
      (implicit_rejection_shared_secret_kdf <: t_Slice u8)
      shared_secret
  in
  shared_secret
