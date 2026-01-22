module Libcrux_iot_ml_kem.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Hash_functions in
  let open Libcrux_iot_ml_kem.Ind_cpa.Unpacked in
  let open Libcrux_iot_ml_kem.Variant in
  let open Libcrux_iot_ml_kem.Vector.Traits in
  let open Libcrux_secrets.Int.Classify_public in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

/// Call [`serialize_uncompressed_ring_element`] for each ring element.
val serialize_vector
      (v_K: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (key: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (out: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires
        v_K <=. mk_usize 4 && v_K >. mk_usize 0 &&
        (Core_models.Slice.impl__len #u8 out <: usize) =.
        (v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize))
      (ensures
        fun temp_0_ ->
          let (out_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize))

/// Concatenate `t` and `ρ` into the public key.
val serialize_public_key_mut
      (v_K v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (tt_as_ntt: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (seed_for_a serialized: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        (Core_models.Slice.impl__len #u8 seed_for_a <: usize) =. mk_usize 32 &&
        (Core_models.Slice.impl__len #u8 serialized <: usize) =.
        ((v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize) +! mk_usize 32
          <:
          usize))
      (ensures
        fun temp_0_ ->
          let (serialized_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 serialized_future <: usize) =.
          (Core_models.Slice.impl__len #u8 serialized <: usize))

/// Sample a vector of ring elements from a centered binomial distribution.
val sample_ring_element_cbd
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2 v_PRF_OUTPUT_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i1: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |}
      (prf_input: t_Array u8 (mk_usize 33))
      (domain_separator: u8)
      (error_1_: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (sample_buffer: t_Array i16 (mk_usize 256))
    : Prims.Pure
      (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
        t_Array i16 (mk_usize 256) &
        u8)
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) && v_ETA2 =. mk_usize 2 &&
        v_ETA2_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA2 <: usize) &&
        v_PRF_OUTPUT_SIZE =. (v_K *! v_ETA2_RANDOMNESS_SIZE <: usize) &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            error_1_
          <:
          usize) =.
        v_K &&
        (cast (domain_separator <: u8) <: usize) <. (mk_usize 2 *! v_K <: usize))
      (ensures
        fun temp_0_ ->
          let
          (error_1_future: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (sample_buffer_future: t_Array i16 (mk_usize 256)),
          (result: u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              error_1_future
            <:
            usize) =.
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              error_1_
            <:
            usize) &&
          result =. (domain_separator +! (cast (v_K <: usize) <: u8) <: u8))

/// Sample a vector of ring elements from a centered binomial distribution and
/// convert them into their NTT representations.
val sample_vector_cbd_then_ntt
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i1: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |}
      (re_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (prf_input: t_Array u8 (mk_usize 33))
      (domain_separator: u8)
      (scratch: v_Vector)
    : Prims.Pure
      (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) & v_Vector & u8)
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        (v_ETA =. mk_usize 3 || v_ETA =. mk_usize 2) &&
        v_ETA_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA <: usize) &&
        v_PRF_OUTPUT_SIZE =. (v_K *! v_ETA_RANDOMNESS_SIZE <: usize) &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            re_as_ntt
          <:
          usize) =.
        v_K &&
        (cast (domain_separator <: u8) <: usize) <. (mk_usize 2 *! v_K <: usize))
      (ensures
        fun temp_0_ ->
          let
          (re_as_ntt_future:
            t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (scratch_future: v_Vector),
          (result: u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              re_as_ntt_future
            <:
            usize) =.
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              re_as_ntt
            <:
            usize) &&
          result =. (domain_separator +! (cast (v_K <: usize) <: u8) <: u8))

/// This function implements most of <strong>Algorithm 12</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation algorithm.
/// We say \"most of\" since Algorithm 12 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `key_generation_seed` parameter.
/// Algorithm 12 is reproduced below:
/// ```plaintext
/// Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
/// d ←$ B
/// (ρ,σ) ← G(d)
/// N ← 0
/// for (i ← 0; i < k; i++)
///     for(j ← 0; j < k; j++)
///         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
///     end for
/// end for
/// for(i ← 0; i < k; i++)
///     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
///     N ← N + 1
/// end for
/// for(i ← 0; i < k; i++)
///     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
///     N ← N + 1
/// end for
/// ŝ ← NTT(s)
/// ê ← NTT(e)
/// t\u{302} ← Â◦ŝ + ê
/// ekₚₖₑ ← ByteEncode₁₂(t\u{302}) ‖ ρ
/// dkₚₖₑ ← ByteEncode₁₂(ŝ)
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val generate_keypair_unpacked
      (v_K v_K_SQUARED v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1: usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i1: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |}
      {| i2: Libcrux_iot_ml_kem.Variant.t_Variant v_Scheme |}
      (key_generation_seed: t_Slice u8)
      (private_key: Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (public_key:
          Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector)
      (scratch: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (s_cache: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure
      (Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector &
        Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector &
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
        t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
        t_Array i32 (mk_usize 256))
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        v_K_SQUARED =. (v_K *! v_K <: usize) &&
        (v_ETA1 =. mk_usize 3 || v_ETA1 =. mk_usize 2) &&
        v_ETA1_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA1 <: usize) &&
        v_PRF_OUTPUT_SIZE1 =. (v_K *! v_ETA1_RANDOMNESS_SIZE <: usize) &&
        (Core_models.Slice.impl__len #u8 key_generation_seed <: usize) =.
        Libcrux_iot_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE)
      (fun _ -> Prims.l_True)

/// Serialize the secret key from the unpacked key pair generation.
val serialize_unpacked_secret_key
      (v_K v_K_SQUARED v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key:
          Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector)
      (private_key: Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (serialized_private_key serialized_public_key: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & t_Slice u8 & v_Vector)
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        v_PRIVATE_KEY_SIZE =.
        (v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize) &&
        v_PUBLIC_KEY_SIZE =.
        ((v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize) +! mk_usize 32
          <:
          usize) &&
        (Core_models.Slice.impl__len #u8 serialized_private_key <: usize) =. v_PRIVATE_KEY_SIZE &&
        (Core_models.Slice.impl__len #u8 serialized_public_key <: usize) =. v_PUBLIC_KEY_SIZE)
      (ensures
        fun temp_0_ ->
          let
          (serialized_private_key_future: t_Slice u8),
          (serialized_public_key_future: t_Slice u8),
          (scratch_future: v_Vector) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 serialized_private_key_future <: usize) =.
          v_PRIVATE_KEY_SIZE &&
          (Core_models.Slice.impl__len #u8 serialized_public_key_future <: usize) =.
          v_PUBLIC_KEY_SIZE)

val generate_keypair
      (v_K v_K_SQUARED v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i1: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |}
      {| i2: Libcrux_iot_ml_kem.Variant.t_Variant v_Scheme |}
      (key_generation_seed serialized_ind_cpa_private_key serialized_public_key: t_Slice u8)
      (scratch: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (s_cache: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure
      (t_Slice u8 & t_Slice u8 & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
        t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
        t_Array i32 (mk_usize 256))
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        v_K_SQUARED =. (v_K *! v_K <: usize) &&
        (v_ETA1 =. mk_usize 3 || v_ETA1 =. mk_usize 2) &&
        v_ETA1_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA1 <: usize) &&
        v_PRF_OUTPUT_SIZE1 =. (v_K *! v_ETA1_RANDOMNESS_SIZE <: usize) &&
        v_PRIVATE_KEY_SIZE =.
        (v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize) &&
        v_PUBLIC_KEY_SIZE =.
        ((v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize) +! mk_usize 32
          <:
          usize) &&
        (Core_models.Slice.impl__len #u8 key_generation_seed <: usize) =.
        Libcrux_iot_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE &&
        (Core_models.Slice.impl__len #u8 serialized_ind_cpa_private_key <: usize) =.
        v_PRIVATE_KEY_SIZE &&
        (Core_models.Slice.impl__len #u8 serialized_public_key <: usize) =. v_PUBLIC_KEY_SIZE)
      (ensures
        fun temp_0_ ->
          let
          (serialized_ind_cpa_private_key_future: t_Slice u8),
          (serialized_public_key_future: t_Slice u8),
          (scratch_future: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
          (s_cache_future:
            t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
          (accumulator_future: t_Array i32 (mk_usize 256)) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 serialized_ind_cpa_private_key_future <: usize) =.
          v_PRIVATE_KEY_SIZE &&
          (Core_models.Slice.impl__len #u8 serialized_public_key_future <: usize) =.
          v_PUBLIC_KEY_SIZE)

/// Call [`compress_then_serialize_ring_element_u`] on each ring element.
val compress_then_serialize_u
      (v_K v_C1_LEN v_U_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (input: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (out: t_Slice u8)
      (scratch: v_Vector)
    : Prims.Pure (t_Slice u8 & v_Vector)
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        (v_U_COMPRESSION_FACTOR =. mk_usize 10 &&
        v_BLOCK_LEN =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 20 <: usize) ||
        v_U_COMPRESSION_FACTOR =. mk_usize 11 &&
        v_BLOCK_LEN =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 22 <: usize)) &&
        v_C1_LEN =. (v_K *! v_BLOCK_LEN <: usize) &&
        (Core_models.Slice.impl__len #u8 out <: usize) =. v_C1_LEN)
      (ensures
        fun temp_0_ ->
          let (out_future: t_Slice u8), (scratch_future: v_Vector) = temp_0_ in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize))

val encrypt_c1
      (v_K v_K_SQUARED v_C1_LEN v_U_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i1: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |}
      (randomness: t_Slice u8)
      (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (seed_for_a ciphertext: t_Slice u8)
      (r_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (error_2_: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure
      (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & t_Slice u8 &
        t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
        v_Vector &
        t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
        t_Array i32 (mk_usize 256))
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        (v_ETA1 =. mk_usize 3 || v_ETA1 =. mk_usize 2) &&
        v_ETA1_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA1 <: usize) &&
        v_PRF_OUTPUT_SIZE1 =. (v_K *! v_ETA1_RANDOMNESS_SIZE <: usize) &&
        v_ETA2 =. mk_usize 2 &&
        v_ETA2_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA2 <: usize) &&
        v_PRF_OUTPUT_SIZE2 =. (v_K *! v_ETA2_RANDOMNESS_SIZE <: usize) &&
        (v_U_COMPRESSION_FACTOR =. mk_usize 10 &&
        v_BLOCK_LEN =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 20 <: usize) ||
        v_U_COMPRESSION_FACTOR =. mk_usize 11 &&
        v_BLOCK_LEN =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 22 <: usize)) &&
        v_C1_LEN =. (v_K *! v_BLOCK_LEN <: usize) &&
        (Core_models.Slice.impl__len #u8 randomness <: usize) =. mk_usize 32 &&
        (Core_models.Slice.impl__len #u8 seed_for_a <: usize) =. mk_usize 32 &&
        (Core_models.Slice.impl__len #u8 ciphertext <: usize) =. v_C1_LEN &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            r_as_ntt
          <:
          usize) =.
        v_K &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            cache
          <:
          usize) =.
        v_K)
      (ensures
        fun temp_0_ ->
          let
          (matrix_entry_future: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
          (ciphertext_future: t_Slice u8),
          (r_as_ntt_future:
            t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (error_2_future: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
          (scratch_future: v_Vector),
          (cache_future: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (accumulator_future: t_Array i32 (mk_usize 256)) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 ciphertext_future <: usize) =. v_C1_LEN &&
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              r_as_ntt_future
            <:
            usize) =.
          v_K &&
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              cache_future
            <:
            usize) =.
          v_K)

val encrypt_c2
      (v_K v_V_COMPRESSION_FACTOR v_C2_LEN: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: t_Slice u8)
      (tt_as_ntt_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (r_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (error_2_: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (message: t_Array u8 (mk_usize 32))
      (ciphertext: t_Slice u8)
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure
      (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & t_Slice u8 & v_Vector &
        t_Array i32 (mk_usize 256))
      (requires
        v_K >. mk_usize 0 && v_K <=. mk_usize 4 &&
        (v_V_COMPRESSION_FACTOR =. mk_usize 4 && v_C2_LEN =. mk_usize 128 ||
        v_V_COMPRESSION_FACTOR =. mk_usize 5 && v_C2_LEN =. mk_usize 160) &&
        (Core_models.Slice.impl__len #u8 public_key <: usize) =.
        (Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT *! v_K <: usize) &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            cache
          <:
          usize) =.
        v_K &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            r_as_ntt
          <:
          usize) =.
        v_K &&
        (Core_models.Slice.impl__len #u8 ciphertext <: usize) =. v_C2_LEN)
      (ensures
        fun temp_0_ ->
          let
          (tt_as_ntt_entry_future: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
          (ciphertext_future: t_Slice u8),
          (scratch_future: v_Vector),
          (accumulator_future: t_Array i32 (mk_usize 256)) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 ciphertext_future <: usize) =. v_C2_LEN)

/// This function implements <strong>Algorithm 13</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.
/// Algorithm 13 is reproduced below:
/// ```plaintext
/// Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Input: message m ∈ 𝔹^{32}.
/// Input: encryption randomness r ∈ 𝔹^{32}.
/// Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
/// N ← 0
/// t\u{302} ← ByteDecode₁₂(ekₚₖₑ[0:384k])
/// ρ ← ekₚₖₑ[384k: 384k + 32]
/// for (i ← 0; i < k; i++)
///     for(j ← 0; j < k; j++)
///         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
///     end for
/// end for
/// for(i ← 0; i < k; i++)
///     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
///     N ← N + 1
/// end for
/// for(i ← 0; i < k; i++)
///     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
///     N ← N + 1
/// end for
/// e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
/// r\u{302} ← NTT(r)
/// u ← NTT-¹(Âᵀ ◦ r\u{302}) + e₁
/// μ ← Decompress₁(ByteDecode₁(m)))
/// v ← NTT-¹(t\u{302}ᵀ ◦ rˆ) + e₂ + μ
/// c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
/// c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
/// return c ← (c₁ ‖ c₂)
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val encrypt
      (v_K v_K_SQUARED v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i1: Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher |}
      (public_key: t_Slice u8)
      (message: t_Array u8 (mk_usize 32))
      (randomness ciphertext: t_Slice u8)
      (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (r_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (error_2_: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure
      (t_Slice u8 & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
        t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
        v_Vector &
        t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
        t_Array i32 (mk_usize 256))
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        v_K_SQUARED =. (v_K *! v_K <: usize) &&
        (v_ETA1 =. mk_usize 3 || v_ETA1 =. mk_usize 2) &&
        v_ETA1_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA1 <: usize) &&
        v_PRF_OUTPUT_SIZE1 =. (v_K *! v_ETA1_RANDOMNESS_SIZE <: usize) &&
        v_ETA2 =. mk_usize 2 &&
        v_ETA2_RANDOMNESS_SIZE =. (mk_usize 64 *! v_ETA2 <: usize) &&
        v_PRF_OUTPUT_SIZE2 =. (v_K *! v_ETA2_RANDOMNESS_SIZE <: usize) &&
        (v_U_COMPRESSION_FACTOR =. mk_usize 10 &&
        v_BLOCK_LEN =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 20 <: usize) ||
        v_U_COMPRESSION_FACTOR =. mk_usize 11 &&
        v_BLOCK_LEN =.
        (Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT *! mk_usize 22 <: usize)) &&
        (v_V_COMPRESSION_FACTOR =. mk_usize 4 && v_C2_LEN =. mk_usize 128 ||
        v_V_COMPRESSION_FACTOR =. mk_usize 5 && v_C2_LEN =. mk_usize 160) &&
        v_C1_LEN =. (v_K *! v_BLOCK_LEN <: usize) &&
        v_CIPHERTEXT_SIZE =. (v_C1_LEN +! v_C2_LEN <: usize) &&
        v_T_AS_NTT_ENCODED_SIZE =.
        (Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT *! v_K <: usize) &&
        (Core_models.Slice.impl__len #u8 public_key <: usize) =.
        (v_T_AS_NTT_ENCODED_SIZE +! mk_usize 32 <: usize) &&
        (Core_models.Slice.impl__len #u8 randomness <: usize) =.
        Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE &&
        (Core_models.Slice.impl__len #u8 ciphertext <: usize) =. v_CIPHERTEXT_SIZE &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            r_as_ntt
          <:
          usize) =.
        v_K &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            cache
          <:
          usize) =.
        v_K)
      (ensures
        fun temp_0_ ->
          let
          (ciphertext_future: t_Slice u8),
          (matrix_entry_future: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
          (r_as_ntt_future:
            t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (error_2_future: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
          (scratch_future: v_Vector),
          (cache_future: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (accumulator_future: t_Array i32 (mk_usize 256)) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 ciphertext <: usize) =. v_CIPHERTEXT_SIZE &&
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              r_as_ntt
            <:
            usize) =.
          v_K &&
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              cache
            <:
            usize) =.
          v_K)

/// Call [`deserialize_then_decompress_ring_element_u`] on each ring element
/// in the `ciphertext`.
val deserialize_then_decompress_u
      (v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (ciphertext: t_Slice u8)
      (u_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (scratch: v_Vector)
    : Prims.Pure
      (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) & v_Vector)
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        (v_U_COMPRESSION_FACTOR =. mk_usize 10 || v_U_COMPRESSION_FACTOR =. mk_usize 11) &&
        (Core_models.Slice.impl__len #u8 ciphertext <: usize) =.
        ((v_K *! mk_usize 32 <: usize) *! v_U_COMPRESSION_FACTOR <: usize) &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            u_as_ntt
          <:
          usize) =.
        v_K)
      (ensures
        fun temp_0_ ->
          let
          (u_as_ntt_future:
            t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (scratch_future: v_Vector) =
            temp_0_
          in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              u_as_ntt_future
            <:
            usize) =.
          v_K)

/// Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
val deserialize_vector
      (v_K: usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: t_Slice u8)
      (secret_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
    : Prims.Pure (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (requires
        v_K >. mk_usize 0 && v_K <=. mk_usize 4 &&
        (Core_models.Slice.impl__len #u8 secret_key <: usize) =.
        (v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize) &&
        (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
              v_Vector)
            secret_as_ntt
          <:
          usize) =.
        v_K)
      (ensures
        fun secret_as_ntt_future ->
          let secret_as_ntt_future:t_Slice
          (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            secret_as_ntt_future
          in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              secret_as_ntt_future
            <:
            usize) =.
          v_K)

/// This function implements <strong>Algorithm 14</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.
/// Algorithm 14 is reproduced below:
/// ```plaintext
/// Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
/// Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
/// Output: message m ∈ 𝔹^{32}.
/// c₁ ← c[0 : 32dᵤk]
/// c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
/// u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
/// v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
/// ŝ ← ByteDecode₁₂(dkₚₖₑ)
/// w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
/// m ← ByteEncode₁(Compress₁(w))
/// return m
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val decrypt_unpacked
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
      (decrypted: t_Slice u8)
      (scratch: v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure (t_Slice u8 & v_Vector & t_Array i32 (mk_usize 256))
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        (v_U_COMPRESSION_FACTOR =. mk_usize 10 &&
        v_VECTOR_U_ENCODED_SIZE =.
        ((v_K *! Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT <: usize) *! mk_usize 20
          <:
          usize) ||
        v_U_COMPRESSION_FACTOR =. mk_usize 11 &&
        v_VECTOR_U_ENCODED_SIZE =.
        ((v_K *! Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT <: usize) *! mk_usize 22
          <:
          usize)) &&
        (v_V_COMPRESSION_FACTOR =. mk_usize 4 || v_V_COMPRESSION_FACTOR =. mk_usize 5) &&
        v_CIPHERTEXT_SIZE =.
        (((v_K *! mk_usize 32 <: usize) *! v_U_COMPRESSION_FACTOR <: usize) +!
          (mk_usize 32 *! v_V_COMPRESSION_FACTOR <: usize)
          <:
          usize) &&
        (Core_models.Slice.impl__len #u8 decrypted <: usize) =.
        Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (ensures
        fun temp_0_ ->
          let
          (decrypted_future: t_Slice u8),
          (scratch_future: v_Vector),
          (accumulator_future: t_Array i32 (mk_usize 256)) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 decrypted_future <: usize) =.
          (Core_models.Slice.impl__len #u8 decrypted <: usize))

val decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
      (decrypted: t_Slice u8)
      (scratch: v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure (t_Slice u8 & v_Vector & t_Array i32 (mk_usize 256))
      (requires
        (v_K =. mk_usize 2 || v_K =. mk_usize 3 || v_K =. mk_usize 4) &&
        (v_U_COMPRESSION_FACTOR =. mk_usize 10 &&
        v_VECTOR_U_ENCODED_SIZE =.
        ((v_K *! Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT <: usize) *! mk_usize 20
          <:
          usize) ||
        v_U_COMPRESSION_FACTOR =. mk_usize 11 &&
        v_VECTOR_U_ENCODED_SIZE =.
        ((v_K *! Libcrux_iot_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT <: usize) *! mk_usize 22
          <:
          usize)) &&
        (v_V_COMPRESSION_FACTOR =. mk_usize 4 || v_V_COMPRESSION_FACTOR =. mk_usize 5) &&
        v_CIPHERTEXT_SIZE =.
        (((v_K *! mk_usize 32 <: usize) *! v_U_COMPRESSION_FACTOR <: usize) +!
          (mk_usize 32 *! v_V_COMPRESSION_FACTOR <: usize)
          <:
          usize) &&
        (Core_models.Slice.impl__len #u8 secret_key <: usize) =.
        (Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT *! v_K <: usize) &&
        (Core_models.Slice.impl__len #u8 decrypted <: usize) =.
        Libcrux_iot_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (ensures
        fun temp_0_ ->
          let
          (decrypted_future: t_Slice u8),
          (scratch_future: v_Vector),
          (accumulator_future: t_Array i32 (mk_usize 256)) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 decrypted_future <: usize) =.
          (Core_models.Slice.impl__len #u8 decrypted <: usize))
