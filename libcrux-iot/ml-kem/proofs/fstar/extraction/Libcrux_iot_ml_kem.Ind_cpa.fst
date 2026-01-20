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

let serialize_vector
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (key: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (out: t_Slice u8)
      (scratch: v_Vector)
     =
  let (out: t_Slice u8), (scratch: v_Vector) =
    Rust_primitives.Hax.Folds.fold_enumerated_slice key
      (fun temp_0_ i ->
          let (out: t_Slice u8), (scratch: v_Vector) = temp_0_ in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 out <: usize) =.
          (v_K *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize)
          <:
          bool)
      (out, scratch <: (t_Slice u8 & v_Vector))
      (fun temp_0_ temp_1_ ->
          let (out: t_Slice u8), (scratch: v_Vector) = temp_0_ in
          let (i: usize), (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_1_
          in
          let (tmp0: v_Vector), (tmp1: t_Slice u8) =
            Libcrux_iot_ml_kem.Serialize.serialize_uncompressed_ring_element #v_Vector
              re
              scratch
              (out.[ {
                    Core_models.Ops.Range.f_start
                    =
                    i *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                    Core_models.Ops.Range.f_end
                    =
                    (i +! mk_usize 1 <: usize) *!
                    Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
                    <:
                    usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
          in
          let scratch:v_Vector = tmp0 in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core_models.Ops.Range.f_start
                  =
                  i *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                  Core_models.Ops.Range.f_end
                  =
                  (i +! mk_usize 1 <: usize) *!
                  Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
                  <:
                  usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              tmp1
          in
          let _:Prims.unit = () in
          out, scratch <: (t_Slice u8 & v_Vector))
  in
  out, scratch <: (t_Slice u8 & v_Vector)

let serialize_public_key_mut
      (v_K v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (tt_as_ntt: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (seed_for_a serialized: t_Slice u8)
      (scratch: v_Vector)
     =
  let (tmp0: t_Slice u8), (tmp1: v_Vector) =
    serialize_vector v_K
      #v_Vector
      tt_as_ntt
      (serialized.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end
            =
            Libcrux_iot_ml_kem.Constants.ranked_bytes_per_ring_element v_K <: usize
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
      scratch
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core_models.Ops.Range.f_start = mk_usize 0;
          Core_models.Ops.Range.f_end
          =
          Libcrux_iot_ml_kem.Constants.ranked_bytes_per_ring_element v_K <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize)
      tmp0
  in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from serialized
      ({
          Core_models.Ops.Range.f_start
          =
          Libcrux_iot_ml_kem.Constants.ranked_bytes_per_ring_element v_K <: usize
        }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (serialized.[ {
                Core_models.Ops.Range.f_start
                =
                Libcrux_iot_ml_kem.Constants.ranked_bytes_per_ring_element v_K <: usize
              }
              <:
              Core_models.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          seed_for_a
        <:
        t_Slice u8)
  in
  serialized, scratch <: (t_Slice u8 & v_Vector)

let sample_ring_element_cbd
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2 v_PRF_OUTPUT_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (prf_input: t_Array u8 (mk_usize 33))
      (domain_separator: u8)
      (error_1_: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (sample_buffer: t_Array i16 (mk_usize 256))
     =
  let prf_inputs:t_Array (t_Array u8 (mk_usize 33)) v_K =
    Rust_primitives.Hax.repeat (Core_models.Clone.f_clone #(t_Array u8 (mk_usize 33))
          #FStar.Tactics.Typeclasses.solve
          prf_input
        <:
        t_Array u8 (mk_usize 33))
      v_K
  in
  let e_domain_separator_init:u8 = domain_separator in
  let (tmp0: t_Array (t_Array u8 (mk_usize 33)) v_K), (out: u8) =
    Libcrux_iot_ml_kem.Utils.prf_input_inc v_K prf_inputs domain_separator
  in
  let prf_inputs:t_Array (t_Array u8 (mk_usize 33)) v_K = tmp0 in
  let domain_separator:u8 = out in
  let prf_outputs:t_Array u8 v_PRF_OUTPUT_SIZE =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      v_PRF_OUTPUT_SIZE
  in
  let prf_outputs:t_Array u8 v_PRF_OUTPUT_SIZE =
    Libcrux_iot_ml_kem.Hash_functions.f_PRFxN #v_Hasher
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Array.impl_23__as_slice #(t_Array u8 (mk_usize 33)) v_K prf_inputs
        <:
        t_Slice (t_Array u8 (mk_usize 33)))
      prf_outputs
      v_ETA2_RANDOMNESS_SIZE
  in
  let
  (error_1_: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
  (sample_buffer: t_Array i16 (mk_usize 256)) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ i ->
          let
          (error_1_: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (sample_buffer: t_Array i16 (mk_usize 256)) =
            temp_0_
          in
          let i:usize = i in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              error_1_
            <:
            usize) =.
          v_K
          <:
          bool)
      (error_1_, sample_buffer
        <:
        (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
          t_Array i16 (mk_usize 256)))
      (fun temp_0_ i ->
          let
          (error_1_: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (sample_buffer: t_Array i16 (mk_usize 256)) =
            temp_0_
          in
          let i:usize = i in
          let randomness:t_Slice u8 =
            prf_outputs.[ {
                Core_models.Ops.Range.f_start = i *! v_ETA2_RANDOMNESS_SIZE <: usize;
                Core_models.Ops.Range.f_end
                =
                (i +! mk_usize 1 <: usize) *! v_ETA2_RANDOMNESS_SIZE <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
          in
          let sample_buffer:t_Array i16 (mk_usize 256) =
            Libcrux_iot_ml_kem.Sampling.sample_from_binomial_distribution v_ETA2
              #v_Vector
              randomness
              sample_buffer
          in
          let error_1_:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize error_1_
              i
              (Libcrux_iot_ml_kem.Polynomial.impl_2__from_i16_array #v_Vector
                  (sample_buffer <: t_Slice i16)
                  (error_1_.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          error_1_, sample_buffer
          <:
          (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
            t_Array i16 (mk_usize 256)))
  in
  let hax_temp_output:u8 = domain_separator in
  error_1_, sample_buffer, hax_temp_output
  <:
  (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
    t_Array i16 (mk_usize 256) &
    u8)

let sample_vector_cbd_then_ntt
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (re_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (prf_input: t_Array u8 (mk_usize 33))
      (domain_separator: u8)
      (scratch: v_Vector)
     =
  let prf_inputs:t_Array (t_Array u8 (mk_usize 33)) v_K =
    Rust_primitives.Hax.repeat (Core_models.Clone.f_clone #(t_Array u8 (mk_usize 33))
          #FStar.Tactics.Typeclasses.solve
          prf_input
        <:
        t_Array u8 (mk_usize 33))
      v_K
  in
  let e_domain_separator_init:u8 = domain_separator in
  let (tmp0: t_Array (t_Array u8 (mk_usize 33)) v_K), (out: u8) =
    Libcrux_iot_ml_kem.Utils.prf_input_inc v_K prf_inputs domain_separator
  in
  let prf_inputs:t_Array (t_Array u8 (mk_usize 33)) v_K = tmp0 in
  let domain_separator:u8 = out in
  let prf_outputs:t_Array u8 v_PRF_OUTPUT_SIZE =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      v_PRF_OUTPUT_SIZE
  in
  let prf_outputs:t_Array u8 v_PRF_OUTPUT_SIZE =
    Libcrux_iot_ml_kem.Hash_functions.f_PRFxN #v_Hasher
      #FStar.Tactics.Typeclasses.solve
      (prf_inputs <: t_Slice (t_Array u8 (mk_usize 33)))
      prf_outputs
      v_ETA_RANDOMNESS_SIZE
  in
  let
  (re_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
  (scratch: v_Vector) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ e_i ->
          let
          (re_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (scratch: v_Vector) =
            temp_0_
          in
          let e_i:usize = e_i in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              re_as_ntt
            <:
            usize) =.
          v_K
          <:
          bool)
      (re_as_ntt, scratch
        <:
        (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) & v_Vector))
      (fun temp_0_ i ->
          let
          (re_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (scratch: v_Vector) =
            temp_0_
          in
          let i:usize = i in
          let randomness:t_Slice u8 =
            prf_outputs.[ {
                Core_models.Ops.Range.f_start = i *! v_ETA_RANDOMNESS_SIZE <: usize;
                Core_models.Ops.Range.f_end
                =
                (i +! mk_usize 1 <: usize) *! v_ETA_RANDOMNESS_SIZE <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
          in
          let sample_buffer:t_Array i16 (mk_usize 256) =
            Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i16
                  #FStar.Tactics.Typeclasses.solve
                  (mk_i16 0)
                <:
                i16)
              (mk_usize 256)
          in
          let sample_buffer:t_Array i16 (mk_usize 256) =
            Libcrux_iot_ml_kem.Sampling.sample_from_binomial_distribution v_ETA
              #v_Vector
              randomness
              sample_buffer
          in
          let re_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re_as_ntt
              i
              (Libcrux_iot_ml_kem.Polynomial.impl_2__from_i16_array #v_Vector
                  (sample_buffer <: t_Slice i16)
                  (re_as_ntt.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
                  )
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let
          (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector), (tmp1: v_Vector) =
            Libcrux_iot_ml_kem.Ntt.ntt_binomially_sampled_ring_element #v_Vector
              (re_as_ntt.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              scratch
          in
          let re_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re_as_ntt i tmp0
          in
          let scratch:v_Vector = tmp1 in
          let _:Prims.unit = () in
          re_as_ntt, scratch
          <:
          (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) & v_Vector))
  in
  let hax_temp_output:u8 = domain_separator in
  re_as_ntt, scratch, hax_temp_output
  <:
  (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) & v_Vector & u8)

let generate_keypair_unpacked
      (v_K v_K_SQUARED v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1: usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_iot_ml_kem.Variant.t_Variant v_Scheme)
      (key_generation_seed: t_Slice u8)
      (private_key: Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (public_key:
          Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector)
      (scratch: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (s_cache: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let hashed:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      (mk_usize 64)
  in
  let hashed:t_Array u8 (mk_usize 64) =
    Libcrux_iot_ml_kem.Variant.f_cpa_keygen_seed #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      #v_Hasher
      key_generation_seed
      hashed
  in
  let (seed_for_A: t_Slice u8), (seed_for_secret_and_error: t_Slice u8) =
    Core_models.Slice.impl__split_at #u8 (hashed <: t_Slice u8) (mk_usize 32)
  in
  let public_key:Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K
    v_K_SQUARED
    v_Vector =
    {
      public_key with
      Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_A
      =
      Libcrux_iot_ml_kem.Matrix.sample_matrix_A v_K
        #v_Vector
        #v_Hasher
        public_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_A
        (Libcrux_secrets.Traits.f_declassify #(t_Array u8 (mk_usize 34))
            #FStar.Tactics.Typeclasses.solve
            (Libcrux_iot_ml_kem.Utils.into_padded_array (mk_usize 34) seed_for_A
              <:
              t_Array u8 (mk_usize 34))
          <:
          t_Array u8 (mk_usize 34))
        true
    }
    <:
    Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector
  in
  let (prf_input: t_Array u8 (mk_usize 33)):t_Array u8 (mk_usize 33) =
    Libcrux_iot_ml_kem.Utils.into_padded_array (mk_usize 33) seed_for_secret_and_error
  in
  let
  (tmp0: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp1: v_Vector),
  (out: u8) =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 #v_Vector
      #v_Hasher private_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt prf_input (mk_u8 0)
      (scratch.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ mk_usize 0 ] <: v_Vector)
  in
  let private_key:Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector =
    { private_key with Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt = tmp0 }
    <:
    Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector
  in
  let scratch:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    {
      scratch with
      Libcrux_iot_ml_kem.Polynomial.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize scratch
          .Libcrux_iot_ml_kem.Polynomial.f_coefficients
        (mk_usize 0)
        tmp1
    }
    <:
    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
  in
  let domain_separator:u8 = out in
  let error_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core_models.Array.from_fn #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun temp_0_ ->
          let _:usize = temp_0_ in
          Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let
  (tmp0: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp1: v_Vector),
  (out: u8) =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 #v_Vector
      #v_Hasher error_as_ntt prf_input domain_separator
      (scratch.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ mk_usize 0 ] <: v_Vector)
  in
  let error_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    tmp0
  in
  let scratch:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    {
      scratch with
      Libcrux_iot_ml_kem.Polynomial.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize scratch
          .Libcrux_iot_ml_kem.Polynomial.f_coefficients
        (mk_usize 0)
        tmp1
    }
    <:
    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
  in
  let _:u8 = out in
  let
  (tmp0: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp1: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp2: t_Array i32 (mk_usize 256)) =
    Libcrux_iot_ml_kem.Matrix.compute_As_plus_e v_K
      #v_Vector
      public_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_tt_as_ntt
      (public_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_A
        <:
        t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      private_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
      error_as_ntt
      s_cache
      accumulator
  in
  let public_key:Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K
    v_K_SQUARED
    v_Vector =
    { public_key with Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_tt_as_ntt = tmp0 }
    <:
    Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector
  in
  let s_cache:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = tmp1 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp2 in
  let _:Prims.unit = () in
  let public_key:Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K
    v_K_SQUARED
    v_Vector =
    {
      public_key with
      Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_seed_for_A
      =
      Core_models.Slice.impl__copy_from_slice #u8
        public_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_seed_for_A
        (Libcrux_secrets.Traits.f_declassify_ref #(t_Slice u8)
            #FStar.Tactics.Typeclasses.solve
            seed_for_A
          <:
          t_Slice u8)
    }
    <:
    Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector
  in
  private_key, public_key, scratch, s_cache, accumulator
  <:
  (Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector &
    Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector &
    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    t_Array i32 (mk_usize 256))

let serialize_unpacked_secret_key
      (v_K v_K_SQUARED v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key:
          Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector)
      (private_key: Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (serialized_private_key serialized_public_key: t_Slice u8)
      (scratch: v_Vector)
     =
  let (tmp0: t_Slice u8), (tmp1: v_Vector) =
    serialize_public_key_mut v_K
      v_PUBLIC_KEY_SIZE
      #v_Vector
      public_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_tt_as_ntt
      (public_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_seed_for_A <: t_Slice u8)
      serialized_public_key
      scratch
  in
  let serialized_public_key:t_Slice u8 = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  let (tmp0: t_Slice u8), (tmp1: v_Vector) =
    serialize_vector v_K
      #v_Vector
      private_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
      serialized_private_key
      scratch
  in
  let serialized_private_key:t_Slice u8 = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  serialized_private_key, serialized_public_key, scratch <: (t_Slice u8 & t_Slice u8 & v_Vector)

let generate_keypair
      (v_K v_K_SQUARED v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Libcrux_iot_ml_kem.Variant.t_Variant v_Scheme)
      (key_generation_seed serialized_ind_cpa_private_key serialized_public_key: t_Slice u8)
      (scratch: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (s_cache: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let private_key:Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector =
    Core_models.Default.f_default #(Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked
          v_K v_Vector)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let public_key:Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K
    v_K_SQUARED
    v_Vector =
    Core_models.Default.f_default #(Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked
          v_K v_K_SQUARED v_Vector)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let
  (tmp0: Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector),
  (tmp1: Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_K_SQUARED v_Vector),
  (tmp2: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp3: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp4: t_Array i32 (mk_usize 256)) =
    generate_keypair_unpacked v_K v_K_SQUARED v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1
      #v_Vector #v_Hasher #v_Scheme key_generation_seed private_key public_key scratch s_cache
      accumulator
  in
  let private_key:Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector =
    tmp0
  in
  let public_key:Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K
    v_K_SQUARED
    v_Vector =
    tmp1
  in
  let scratch:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp2 in
  let s_cache:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = tmp3 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp4 in
  let _:Prims.unit = () in
  let (tmp0: t_Slice u8), (tmp1: t_Slice u8), (tmp2: v_Vector) =
    serialize_unpacked_secret_key v_K v_K_SQUARED v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE #v_Vector
      public_key private_key serialized_ind_cpa_private_key serialized_public_key
      (scratch.Libcrux_iot_ml_kem.Polynomial.f_coefficients.[ mk_usize 0 ] <: v_Vector)
  in
  let serialized_ind_cpa_private_key:t_Slice u8 = tmp0 in
  let serialized_public_key:t_Slice u8 = tmp1 in
  let scratch:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    {
      scratch with
      Libcrux_iot_ml_kem.Polynomial.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize scratch
          .Libcrux_iot_ml_kem.Polynomial.f_coefficients
        (mk_usize 0)
        tmp2
    }
    <:
    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
  in
  let _:Prims.unit = () in
  serialized_ind_cpa_private_key, serialized_public_key, scratch, s_cache, accumulator
  <:
  (t_Slice u8 & t_Slice u8 & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    t_Array i32 (mk_usize 256))

let compress_then_serialize_u
      (v_K v_C1_LEN v_U_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (input: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (out: t_Slice u8)
      (scratch: v_Vector)
     =
  let (out: t_Slice u8), (scratch: v_Vector) =
    Rust_primitives.Hax.Folds.fold_enumerated_slice input
      (fun temp_0_ temp_1_ ->
          let (out: t_Slice u8), (scratch: v_Vector) = temp_0_ in
          let _:usize = temp_1_ in
          (Core_models.Slice.impl__len #u8 out <: usize) =. v_C1_LEN <: bool)
      (out, scratch <: (t_Slice u8 & v_Vector))
      (fun temp_0_ temp_1_ ->
          let (out: t_Slice u8), (scratch: v_Vector) = temp_0_ in
          let (i: usize), (re: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_1_
          in
          let (tmp0: t_Slice u8), (tmp1: v_Vector) =
            Libcrux_iot_ml_kem.Serialize.compress_then_serialize_ring_element_u v_U_COMPRESSION_FACTOR
              v_BLOCK_LEN
              #v_Vector
              re
              (out.[ {
                    Core_models.Ops.Range.f_start = i *! (v_C1_LEN /! v_K <: usize) <: usize;
                    Core_models.Ops.Range.f_end
                    =
                    (i +! mk_usize 1 <: usize) *! (v_C1_LEN /! v_K <: usize) <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              scratch
          in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core_models.Ops.Range.f_start = i *! (v_C1_LEN /! v_K <: usize) <: usize;
                  Core_models.Ops.Range.f_end
                  =
                  (i +! mk_usize 1 <: usize) *! (v_C1_LEN /! v_K <: usize) <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              tmp0
          in
          let scratch:v_Vector = tmp1 in
          let _:Prims.unit = () in
          out, scratch <: (t_Slice u8 & v_Vector))
  in
  out, scratch <: (t_Slice u8 & v_Vector)

let encrypt_c1
      (v_K v_K_SQUARED v_C1_LEN v_U_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (randomness: t_Slice u8)
      (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (seed_for_a ciphertext: t_Slice u8)
      (r_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (error_2_: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let (prf_input: t_Array u8 (mk_usize 33)):t_Array u8 (mk_usize 33) =
    Libcrux_iot_ml_kem.Utils.into_padded_array (mk_usize 33) randomness
  in
  let
  (tmp0: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
  (tmp1: v_Vector),
  (out: u8) =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 #v_Vector
      #v_Hasher r_as_ntt prf_input (mk_u8 0) scratch
  in
  let r_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) = tmp0 in
  let scratch:v_Vector = tmp1 in
  let domain_separator:u8 = out in
  let (error_1_: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K):t_Array
    (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core_models.Array.from_fn #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun e_i ->
          let e_i:usize = e_i in
          Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let sampling_buffer:t_Array i16 (mk_usize 256) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (mk_i16 0)
        <:
        i16)
      (mk_usize 256)
  in
  let
  (tmp0: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp1: t_Array i16 (mk_usize 256)),
  (out: u8) =
    sample_ring_element_cbd v_K v_ETA2_RANDOMNESS_SIZE v_ETA2 v_PRF_OUTPUT_SIZE2 #v_Vector #v_Hasher
      prf_input domain_separator error_1_ sampling_buffer
  in
  let error_1_:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    tmp0
  in
  let sampling_buffer:t_Array i16 (mk_usize 256) = tmp1 in
  let domain_separator:u8 = out in
  let prf_input:t_Array u8 (mk_usize 33) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_input
      (mk_usize 32)
      (Libcrux_secrets.Traits.f_classify #u8 #FStar.Tactics.Typeclasses.solve domain_separator <: u8
      )
  in
  let prf_output:t_Array u8 v_ETA2_RANDOMNESS_SIZE =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (mk_u8 0)
        <:
        u8)
      v_ETA2_RANDOMNESS_SIZE
  in
  let prf_output:t_Array u8 v_ETA2_RANDOMNESS_SIZE =
    Libcrux_iot_ml_kem.Hash_functions.f_PRF #v_Hasher
      #FStar.Tactics.Typeclasses.solve
      v_ETA2_RANDOMNESS_SIZE
      (prf_input <: t_Slice u8)
      prf_output
  in
  let sampling_buffer:t_Array i16 (mk_usize 256) =
    Libcrux_iot_ml_kem.Sampling.sample_from_binomial_distribution v_ETA2
      #v_Vector
      (prf_output <: t_Slice u8)
      sampling_buffer
  in
  let error_2_:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__from_i16_array #v_Vector
      (sampling_buffer <: t_Slice i16)
      error_2_
  in
  let u:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core_models.Array.from_fn #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun e_i ->
          let e_i:usize = e_i in
          Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let
  (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp1: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp2: v_Vector),
  (tmp3: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
  (tmp4: t_Array i32 (mk_usize 256)) =
    Libcrux_iot_ml_kem.Matrix.compute_vector_u v_K #v_Vector #v_Hasher matrix_entry seed_for_a
      r_as_ntt
      (error_1_ <: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)) u
      scratch cache accumulator
  in
  let matrix_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp0 in
  let u:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = tmp1 in
  let scratch:v_Vector = tmp2 in
  let cache:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) = tmp3 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp4 in
  let _:Prims.unit = () in
  let (tmp0: t_Slice u8), (tmp1: v_Vector) =
    compress_then_serialize_u v_K
      v_C1_LEN
      v_U_COMPRESSION_FACTOR
      v_BLOCK_LEN
      #v_Vector
      u
      ciphertext
      scratch
  in
  let ciphertext:t_Slice u8 = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  matrix_entry, ciphertext, r_as_ntt, error_2_, scratch, cache, accumulator
  <:
  (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & t_Slice u8 &
    t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector &
    t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
    t_Array i32 (mk_usize 256))

let encrypt_c2
      (v_K v_V_COMPRESSION_FACTOR v_C2_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key: t_Slice u8)
      (tt_as_ntt_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (r_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (error_2_: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (message: t_Array u8 (mk_usize 32))
      (ciphertext: t_Slice u8)
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let message_as_ring_element:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
  in
  let message_as_ring_element:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Serialize.deserialize_then_decompress_message #v_Vector
      message
      message_as_ring_element
  in
  let v:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
  in
  let
  (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp1: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp2: v_Vector),
  (tmp3: t_Array i32 (mk_usize 256)) =
    Libcrux_iot_ml_kem.Matrix.compute_ring_element_v v_K #v_Vector public_key tt_as_ntt_entry
      r_as_ntt error_2_ message_as_ring_element v scratch cache accumulator
  in
  let tt_as_ntt_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp0 in
  let v:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp1 in
  let scratch:v_Vector = tmp2 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp3 in
  let _:Prims.unit = () in
  let (tmp0: t_Slice u8), (tmp1: v_Vector) =
    Libcrux_iot_ml_kem.Serialize.compress_then_serialize_ring_element_v v_K
      v_V_COMPRESSION_FACTOR
      v_C2_LEN
      #v_Vector
      v
      ciphertext
      scratch
  in
  let ciphertext:t_Slice u8 = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  tt_as_ntt_entry, ciphertext, scratch, accumulator
  <:
  (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & t_Slice u8 & v_Vector &
    t_Array i32 (mk_usize 256))

let encrypt
      (v_K v_K_SQUARED v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (public_key: t_Slice u8)
      (message: t_Array u8 (mk_usize 32))
      (randomness ciphertext: t_Slice u8)
      (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (r_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (error_2_: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let
  (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp1: t_Slice u8),
  (tmp2: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
  (tmp3: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp4: v_Vector),
  (tmp5: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
  (tmp6: t_Array i32 (mk_usize 256)) =
    encrypt_c1 v_K v_K_SQUARED v_C1_LEN v_U_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_PRF_OUTPUT_SIZE1 v_PRF_OUTPUT_SIZE2
      #v_Vector #v_Hasher randomness matrix_entry
      (public_key.[ { Core_models.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
      (ciphertext.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = v_C1_LEN
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8) r_as_ntt error_2_ scratch cache accumulator
  in
  let matrix_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp0 in
  let ciphertext:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range ciphertext
      ({ Core_models.Ops.Range.f_start = mk_usize 0; Core_models.Ops.Range.f_end = v_C1_LEN }
        <:
        Core_models.Ops.Range.t_Range usize)
      tmp1
  in
  let r_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) = tmp2 in
  let error_2_:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp3 in
  let scratch:v_Vector = tmp4 in
  let cache:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) = tmp5 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp6 in
  let _:Prims.unit = () in
  let
  (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp1: t_Slice u8),
  (tmp2: v_Vector),
  (tmp3: t_Array i32 (mk_usize 256)) =
    encrypt_c2 v_K v_V_COMPRESSION_FACTOR v_C2_LEN #v_Vector
      (public_key.[ { Core_models.Ops.Range.f_end = v_T_AS_NTT_ENCODED_SIZE }
          <:
          Core_models.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8) matrix_entry r_as_ntt error_2_ message
      (ciphertext.[ { Core_models.Ops.Range.f_start = v_C1_LEN }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8) scratch cache accumulator
  in
  let matrix_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp0 in
  let ciphertext:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from ciphertext
      ({ Core_models.Ops.Range.f_start = v_C1_LEN } <: Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let scratch:v_Vector = tmp2 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp3 in
  let _:Prims.unit = () in
  ciphertext, matrix_entry, r_as_ntt, error_2_, scratch, cache, accumulator
  <:
  (t_Slice u8 & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector &
    t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
    t_Array i32 (mk_usize 256))

let deserialize_then_decompress_u
      (v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (ciphertext: t_Slice u8)
      (u_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (scratch: v_Vector)
     =
  let
  (scratch: v_Vector),
  (u_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)) =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice ((Libcrux_iot_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
          v_U_COMPRESSION_FACTOR
          <:
          usize) /!
        mk_usize 8
        <:
        usize)
      ciphertext
      (fun temp_0_ e_i ->
          let
          (scratch: v_Vector),
          (u_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)) =
            temp_0_
          in
          let e_i:usize = e_i in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              u_as_ntt
            <:
            usize) =.
          v_K
          <:
          bool)
      (scratch, u_as_ntt
        <:
        (v_Vector & t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)))
      (fun temp_0_ temp_1_ ->
          let
          (scratch: v_Vector),
          (u_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)) =
            temp_0_
          in
          let (i: usize), (u_bytes: t_Slice u8) = temp_1_ in
          let u_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize u_as_ntt
              i
              (Libcrux_iot_ml_kem.Serialize.deserialize_then_decompress_ring_element_u v_U_COMPRESSION_FACTOR
                  #v_Vector
                  u_bytes
                  (u_as_ntt.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let
          (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector), (tmp1: v_Vector) =
            Libcrux_iot_ml_kem.Ntt.ntt_vector_u v_U_COMPRESSION_FACTOR
              #v_Vector
              (u_as_ntt.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              scratch
          in
          let u_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize u_as_ntt i tmp0
          in
          let scratch:v_Vector = tmp1 in
          let _:Prims.unit = () in
          scratch, u_as_ntt
          <:
          (v_Vector & t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)))
  in
  u_as_ntt, scratch
  <:
  (t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) & v_Vector)

let deserialize_vector
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (secret_key: t_Slice u8)
      (secret_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
     =
  let secret_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun secret_as_ntt i ->
          let secret_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          =
            secret_as_ntt
          in
          let i:usize = i in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              secret_as_ntt
            <:
            usize) =.
          v_K
          <:
          bool)
      secret_as_ntt
      (fun secret_as_ntt i ->
          let secret_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          =
            secret_as_ntt
          in
          let i:usize = i in
          let secret_as_ntt:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize secret_as_ntt
              i
              (Libcrux_iot_ml_kem.Serialize.deserialize_to_uncompressed_ring_element #v_Vector
                  (secret_key.[ {
                        Core_models.Ops.Range.f_start
                        =
                        i *! Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (i +! mk_usize 1 <: usize) *!
                        Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
                        <:
                        usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (secret_as_ntt.[ i ]
                    <:
                    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          secret_as_ntt)
  in
  secret_as_ntt

let decrypt_unpacked
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (secret_key: Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
      (decrypted: t_Slice u8)
      (scratch: v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let u_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core_models.Array.from_fn #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun temp_0_ ->
          let _:usize = temp_0_ in
          Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let
  (tmp0: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K),
  (tmp1: v_Vector) =
    deserialize_then_decompress_u v_K
      v_CIPHERTEXT_SIZE
      v_U_COMPRESSION_FACTOR
      #v_Vector
      (ciphertext.[ { Core_models.Ops.Range.f_end = v_VECTOR_U_ENCODED_SIZE }
          <:
          Core_models.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
      u_as_ntt
      scratch
  in
  let u_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    tmp0
  in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  let v:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
  in
  let v:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Serialize.deserialize_then_decompress_ring_element_v v_K
      v_V_COMPRESSION_FACTOR
      #v_Vector
      (ciphertext.[ { Core_models.Ops.Range.f_start = v_VECTOR_U_ENCODED_SIZE }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
      v
  in
  let message:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
  in
  let
  (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (tmp1: v_Vector),
  (tmp2: t_Array i32 (mk_usize 256)) =
    Libcrux_iot_ml_kem.Matrix.compute_message v_K
      #v_Vector
      v
      secret_key.Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
      u_as_ntt
      message
      scratch
      accumulator
  in
  let message:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp0 in
  let scratch:v_Vector = tmp1 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp2 in
  let _:Prims.unit = () in
  let (tmp0: t_Slice u8), (tmp1: v_Vector) =
    Libcrux_iot_ml_kem.Serialize.compress_then_serialize_message #v_Vector message decrypted scratch
  in
  let decrypted:t_Slice u8 = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  decrypted, scratch, accumulator <: (t_Slice u8 & v_Vector & t_Array i32 (mk_usize 256))

let decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
      (decrypted: t_Slice u8)
      (scratch: v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let secret_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core_models.Array.from_fn #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun temp_0_ ->
          let _:usize = temp_0_ in
          Libcrux_iot_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let secret_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    deserialize_vector v_K #v_Vector secret_key secret_as_ntt
  in
  let secret_key_unpacked:Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K
    v_Vector =
    { Libcrux_iot_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt = secret_as_ntt }
    <:
    Libcrux_iot_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector
  in
  let (tmp0: t_Slice u8), (tmp1: v_Vector), (tmp2: t_Array i32 (mk_usize 256)) =
    decrypt_unpacked v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR
      v_V_COMPRESSION_FACTOR #v_Vector secret_key_unpacked ciphertext decrypted scratch accumulator
  in
  let decrypted:t_Slice u8 = tmp0 in
  let scratch:v_Vector = tmp1 in
  let accumulator:t_Array i32 (mk_usize 256) = tmp2 in
  let _:Prims.unit = () in
  decrypted, scratch, accumulator <: (t_Slice u8 & v_Vector & t_Array i32 (mk_usize 256))
