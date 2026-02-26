module Libcrux_iot_ml_kem.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Hash_functions in
  let open Libcrux_iot_ml_kem.Vector.Traits in
  let open Libcrux_secrets.Int.Classify_public in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

let entry
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (matrix: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (i j: usize)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                  v_Vector)
                matrix
              <:
              usize) =.
            (v_K *! v_K <: usize)
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit = Hax_lib.v_assert (i <. v_K <: bool) in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit = Hax_lib.v_assert (j <. v_K <: bool) in
      ()
  in
  matrix.[ (i *! v_K <: usize) +! j <: usize ]

let sample_matrix_entry
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (out: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (seed: t_Slice u8)
      (i j: usize)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 seed <: usize) =. mk_usize 32 <: bool)
      in
      ()
  in
  let seed_ij:t_Array u8 (mk_usize 34) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 34) in
  let seed_ij:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range seed_ij
      ({ Core_models.Ops.Range.f_start = mk_usize 0; Core_models.Ops.Range.f_end = mk_usize 32 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (seed_ij.[ {
                Core_models.Ops.Range.f_start = mk_usize 0;
                Core_models.Ops.Range.f_end = mk_usize 32
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          seed
        <:
        t_Slice u8)
  in
  let seed_ij:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed_ij
      (mk_usize 32)
      (cast (i <: usize) <: u8)
  in
  let seed_ij:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed_ij
      (mk_usize 33)
      (cast (j <: usize) <: u8)
  in
  let sampled_coefficients:t_Array usize (mk_usize 1) =
    Rust_primitives.Hax.repeat (mk_usize 0) (mk_usize 1)
  in
  let out_raw:t_Array (t_Array i16 (mk_usize 272)) (mk_usize 1) =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (mk_i16 0) (mk_usize 272)
        <:
        t_Array i16 (mk_usize 272))
      (mk_usize 1)
  in
  let (tmp0: t_Array usize (mk_usize 1)), (tmp1: t_Array (t_Array i16 (mk_usize 272)) (mk_usize 1))
  =
    Libcrux_iot_ml_kem.Sampling.sample_from_xof (mk_usize 1)
      #v_Vector
      #v_Hasher
      ((let list = [seed_ij] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
        <:
        t_Slice (t_Array u8 (mk_usize 34)))
      sampled_coefficients
      out_raw
  in
  let sampled_coefficients:t_Array usize (mk_usize 1) = tmp0 in
  let out_raw:t_Array (t_Array i16 (mk_usize 272)) (mk_usize 1) = tmp1 in
  let _:Prims.unit = () in
  let out:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__from_i16_array #v_Vector
      (Core_models.Array.impl_23__as_slice #i16
          (mk_usize 272)
          (Libcrux_secrets.Traits.f_classify #(t_Array i16 (mk_usize 272))
              #FStar.Tactics.Typeclasses.solve
              (out_raw.[ mk_usize 0 ] <: t_Array i16 (mk_usize 272))
            <:
            t_Array i16 (mk_usize 272))
        <:
        t_Slice i16)
      out
  in
  out

let sample_matrix_A
      (v_K: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (v_A_transpose: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (seed: t_Array u8 (mk_usize 34))
      (transpose: bool)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                  v_Vector)
                v_A_transpose
              <:
              usize) =.
            (v_K *! v_K <: usize)
            <:
            bool)
      in
      ()
  in
  let v_A_transpose:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun v_A_transpose temp_1_ ->
          let v_A_transpose:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          =
            v_A_transpose
          in
          let _:usize = temp_1_ in
          (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                v_Vector)
              v_A_transpose
            <:
            usize) =.
          (v_K *! v_K <: usize)
          <:
          bool)
      v_A_transpose
      (fun v_A_transpose i ->
          let v_A_transpose:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          =
            v_A_transpose
          in
          let i:usize = i in
          let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K = Rust_primitives.Hax.repeat seed v_K in
          let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              v_K
              (fun seeds temp_1_ ->
                  let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K = seeds in
                  let _:usize = temp_1_ in
                  (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                        v_Vector)
                      v_A_transpose
                    <:
                    usize) =.
                  (v_K *! v_K <: usize)
                  <:
                  bool)
              seeds
              (fun seeds j ->
                  let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K = seeds in
                  let j:usize = j in
                  let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seeds
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (seeds.[ j ]
                            <:
                            t_Array u8 (mk_usize 34))
                          (mk_usize 32)
                          (cast (i <: usize) <: u8)
                        <:
                        t_Array u8 (mk_usize 34))
                  in
                  let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seeds
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (seeds.[ j ]
                            <:
                            t_Array u8 (mk_usize 34))
                          (mk_usize 33)
                          (cast (j <: usize) <: u8)
                        <:
                        t_Array u8 (mk_usize 34))
                  in
                  seeds)
          in
          let sampled_coefficients:t_Array usize v_K =
            Rust_primitives.Hax.repeat (mk_usize 0) v_K
          in
          let out:t_Array (t_Array i16 (mk_usize 272)) v_K =
            Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (mk_i16 0) (mk_usize 272)
                <:
                t_Array i16 (mk_usize 272))
              v_K
          in
          let (tmp0: t_Array usize v_K), (tmp1: t_Array (t_Array i16 (mk_usize 272)) v_K) =
            Libcrux_iot_ml_kem.Sampling.sample_from_xof v_K
              #v_Vector
              #v_Hasher
              (seeds <: t_Slice (t_Array u8 (mk_usize 34)))
              sampled_coefficients
              out
          in
          let sampled_coefficients:t_Array usize v_K = tmp0 in
          let out:t_Array (t_Array i16 (mk_usize 272)) v_K = tmp1 in
          let _:Prims.unit = () in
          Rust_primitives.Hax.Folds.fold_enumerated_slice out
            (fun v_A_transpose temp_1_ ->
                let v_A_transpose:t_Slice
                (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                  v_A_transpose
                in
                let _:usize = temp_1_ in
                (Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                      v_Vector)
                    v_A_transpose
                  <:
                  usize) =.
                (v_K *! v_K <: usize)
                <:
                bool)
            v_A_transpose
            (fun v_A_transpose temp_1_ ->
                let v_A_transpose:t_Slice
                (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                  v_A_transpose
                in
                let (j: usize), (sample: t_Array i16 (mk_usize 272)) = temp_1_ in
                if transpose
                then
                  let v_A_transpose:t_Slice
                  (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A_transpose
                      ((j *! v_K <: usize) +! i <: usize)
                      (Libcrux_iot_ml_kem.Polynomial.impl_2__from_i16_array #v_Vector
                          (Libcrux_secrets.Traits.f_classify_ref #(t_Slice i16)
                              #FStar.Tactics.Typeclasses.solve
                              (sample.[ { Core_models.Ops.Range.f_end = mk_usize 256 }
                                  <:
                                  Core_models.Ops.Range.t_RangeTo usize ]
                                <:
                                t_Slice i16)
                            <:
                            t_Slice i16)
                          (v_A_transpose.[ (j *! v_K <: usize) +! i <: usize ]
                            <:
                            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                        <:
                        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  in
                  v_A_transpose
                else
                  let v_A_transpose:t_Slice
                  (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A_transpose
                      ((i *! v_K <: usize) +! j <: usize)
                      (Libcrux_iot_ml_kem.Polynomial.impl_2__from_i16_array #v_Vector
                          (Libcrux_secrets.Traits.f_classify_ref #(t_Slice i16)
                              #FStar.Tactics.Typeclasses.solve
                              (sample.[ { Core_models.Ops.Range.f_end = mk_usize 256 }
                                  <:
                                  Core_models.Ops.Range.t_RangeTo usize ]
                                <:
                                t_Slice i16)
                            <:
                            t_Slice i16)
                          (v_A_transpose.[ (i *! v_K <: usize) +! j <: usize ]
                            <:
                            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                        <:
                        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  in
                  v_A_transpose))
  in
  v_A_transpose

let compute_message
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (v: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (secret_as_ntt u_as_ntt:
          t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (result: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let accumulator:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (mk_i32 0)
        <:
        i32)
      (mk_usize 256)
  in
  let accumulator:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun accumulator temp_1_ ->
          let accumulator:t_Array i32 (mk_usize 256) = accumulator in
          let _:usize = temp_1_ in
          true)
      accumulator
      (fun accumulator i ->
          let accumulator:t_Array i32 (mk_usize 256) = accumulator in
          let i:usize = i in
          Libcrux_iot_ml_kem.Polynomial.impl_2__accumulating_ntt_multiply #v_Vector
            (secret_as_ntt.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
            (u_as_ntt.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
            accumulator
          <:
          t_Array i32 (mk_usize 256))
  in
  let result:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__reducing_from_i32_array #v_Vector
      (accumulator <: t_Slice i32)
      result
  in
  let (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector), (tmp1: v_Vector) =
    Libcrux_iot_ml_kem.Invert_ntt.invert_ntt_montgomery v_K #v_Vector result scratch
  in
  let result:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  let result:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__subtract_reduce #v_Vector v result
  in
  result, scratch, accumulator
  <:
  (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector & v_Vector &
    t_Array i32 (mk_usize 256))

let compute_ring_element_v
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key: t_Slice u8)
      (tt_as_ntt_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (r_as_ntt: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (error_2_ message result: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let accumulator:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (mk_i32 0)
        <:
        i32)
      (mk_usize 256)
  in
  let
  (accumulator: t_Array i32 (mk_usize 256)),
  (tt_as_ntt_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice Libcrux_iot_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
      public_key
      (fun temp_0_ temp_1_ ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (tt_as_ntt_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (accumulator, tt_as_ntt_entry
        <:
        (t_Array i32 (mk_usize 256) & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
        ))
      (fun temp_0_ temp_1_ ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (tt_as_ntt_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          let (i: usize), (ring_element: t_Slice u8) = temp_1_ in
          let tt_as_ntt_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Libcrux_iot_ml_kem.Serialize.deserialize_to_reduced_ring_element #v_Vector
              (Libcrux_secrets.Traits.f_classify_ref #(t_Slice u8)
                  #FStar.Tactics.Typeclasses.solve
                  ring_element
                <:
                t_Slice u8)
              tt_as_ntt_entry
          in
          let accumulator:t_Array i32 (mk_usize 256) =
            Libcrux_iot_ml_kem.Polynomial.impl_2__accumulating_ntt_multiply_use_cache #v_Vector
              tt_as_ntt_entry
              (r_as_ntt.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              accumulator
              (cache.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          accumulator, tt_as_ntt_entry
          <:
          (t_Array i32 (mk_usize 256) &
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
  in
  let result:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_iot_ml_kem.Polynomial.impl_2__reducing_from_i32_array #v_Vector
      (accumulator <: t_Slice i32)
      result
  in
  let (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector), (tmp1: v_Vector) =
    Libcrux_iot_ml_kem.Invert_ntt.invert_ntt_montgomery v_K #v_Vector result scratch
  in
  let result:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  let (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector), (tmp1: v_Vector) =
    Libcrux_iot_ml_kem.Polynomial.impl_2__add_message_error_reduce #v_Vector
      error_2_
      message
      result
      scratch
  in
  let result:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = tmp0 in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  tt_as_ntt_entry, result, scratch, accumulator
  <:
  (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    v_Vector &
    t_Array i32 (mk_usize 256))

let compute_vector_u
      (v_K: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (seed: t_Slice u8)
      (r_as_ntt error_1_ result:
          t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (scratch: v_Vector)
      (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                  v_Vector)
                r_as_ntt
              <:
              usize) =.
            v_K
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                  v_Vector)
                error_1_
              <:
              usize) =.
            v_K
            <:
            bool)
      in
      ()
  in
  let accumulator:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (mk_i32 0)
        <:
        i32)
      (mk_usize 256)
  in
  let
  (accumulator: t_Array i32 (mk_usize 256)),
  (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
  (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ temp_1_ ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          let _:usize = temp_1_ in
          ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                  v_Vector)
                result
              <:
              usize) =.
            v_K
            <:
            bool) &&
          ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                  v_Vector)
                cache
              <:
              usize) =.
            v_K
            <:
            bool))
      (accumulator, cache, matrix_entry
        <:
        (t_Array i32 (mk_usize 256) &
          t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
          Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (fun temp_0_ j ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (cache: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          let j:usize = j in
          let matrix_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            sample_matrix_entry #v_Vector #v_Hasher matrix_entry seed (mk_usize 0) j
          in
          let
          (tmp0: t_Array i32 (mk_usize 256)),
          (tmp1: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Libcrux_iot_ml_kem.Polynomial.impl_2__accumulating_ntt_multiply_fill_cache #v_Vector
              matrix_entry
              (r_as_ntt.[ j ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              accumulator
              (cache.[ j ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let accumulator:t_Array i32 (mk_usize 256) = tmp0 in
          let cache:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize cache j tmp1
          in
          let _:Prims.unit = () in
          accumulator, cache, matrix_entry
          <:
          (t_Array i32 (mk_usize 256) &
            t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
  in
  let result:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (mk_usize 0)
      (Libcrux_iot_ml_kem.Polynomial.impl_2__reducing_from_i32_array #v_Vector
          (accumulator <: t_Slice i32)
          (result.[ mk_usize 0 ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
        <:
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector), (tmp1: v_Vector) =
    Libcrux_iot_ml_kem.Invert_ntt.invert_ntt_montgomery v_K
      #v_Vector
      (result.[ mk_usize 0 ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      scratch
  in
  let result:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (mk_usize 0) tmp0
  in
  let scratch:v_Vector = tmp1 in
  let _:Prims.unit = () in
  let result:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (mk_usize 0)
      (Libcrux_iot_ml_kem.Polynomial.impl_2__add_error_reduce #v_Vector
          (result.[ mk_usize 0 ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          (error_1_.[ mk_usize 0 ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          )
        <:
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let
  (accumulator: t_Array i32 (mk_usize 256)),
  (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
  (result: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
  (scratch: v_Vector) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
      v_K
      (fun temp_0_ temp_1_ ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
          (result: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (scratch: v_Vector) =
            temp_0_
          in
          let _:usize = temp_1_ in
          ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                  v_Vector)
                result
              <:
              usize) =.
            v_K
            <:
            bool) &&
          ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                  v_Vector)
                cache
              <:
              usize) =.
            v_K
            <:
            bool))
      (accumulator, matrix_entry, result, scratch
        <:
        (t_Array i32 (mk_usize 256) & Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
          t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
          v_Vector))
      (fun temp_0_ i ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector),
          (result: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)),
          (scratch: v_Vector) =
            temp_0_
          in
          let i:usize = i in
          let accumulator:t_Array i32 (mk_usize 256) =
            Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i32
                  #FStar.Tactics.Typeclasses.solve
                  (mk_i32 0)
                <:
                i32)
              (mk_usize 256)
          in
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              v_K
              (fun temp_0_ temp_1_ ->
                  let
                  (accumulator: t_Array i32 (mk_usize 256)),
                  (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                    temp_0_
                  in
                  let _:usize = temp_1_ in
                  ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                          v_Vector)
                        result
                      <:
                      usize) =.
                    v_K
                    <:
                    bool) &&
                  ((Core_models.Slice.impl__len #(Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement
                          v_Vector)
                        cache
                      <:
                      usize) =.
                    v_K
                    <:
                    bool))
              (accumulator, matrix_entry
                <:
                (t_Array i32 (mk_usize 256) &
                  Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
              (fun temp_0_ j ->
                  let
                  (accumulator: t_Array i32 (mk_usize 256)),
                  (matrix_entry: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                    temp_0_
                  in
                  let j:usize = j in
                  let matrix_entry:Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
                    sample_matrix_entry #v_Vector #v_Hasher matrix_entry seed i j
                  in
                  let accumulator:t_Array i32 (mk_usize 256) =
                    Libcrux_iot_ml_kem.Polynomial.impl_2__accumulating_ntt_multiply_use_cache #v_Vector
                      matrix_entry
                      (r_as_ntt.[ j ]
                        <:
                        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                      accumulator
                      (cache.[ j ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
                      )
                  in
                  accumulator, matrix_entry
                  <:
                  (t_Array i32 (mk_usize 256) &
                    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
          in
          let result:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_iot_ml_kem.Polynomial.impl_2__reducing_from_i32_array #v_Vector
                  (accumulator <: t_Slice i32)
                  (result.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let
          (tmp0: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector), (tmp1: v_Vector) =
            Libcrux_iot_ml_kem.Invert_ntt.invert_ntt_montgomery v_K
              #v_Vector
              (result.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              scratch
          in
          let result:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result i tmp0
          in
          let scratch:v_Vector = tmp1 in
          let _:Prims.unit = () in
          let result:t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_iot_ml_kem.Polynomial.impl_2__add_error_reduce #v_Vector
                  (result.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  (error_1_.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          accumulator, matrix_entry, result, scratch
          <:
          (t_Array i32 (mk_usize 256) &
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
            t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
            v_Vector))
  in
  matrix_entry, result, scratch, cache, accumulator
  <:
  (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector &
    t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
    v_Vector &
    t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) &
    t_Array i32 (mk_usize 256))

let compute_As_plus_e
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (tt_as_ntt: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (matrix_A: t_Slice (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
      (s_as_ntt error_as_ntt s_cache:
          t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let
  (accumulator: t_Array i32 (mk_usize 256)),
  (s_cache: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ temp_1_ ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (s_cache: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (accumulator, s_cache
        <:
        (t_Array i32 (mk_usize 256) &
          t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
      (fun temp_0_ j ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (s_cache: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) =
            temp_0_
          in
          let j:usize = j in
          let
          (tmp0: t_Array i32 (mk_usize 256)),
          (tmp1: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            Libcrux_iot_ml_kem.Polynomial.impl_2__accumulating_ntt_multiply_fill_cache #v_Vector
              (entry v_K #v_Vector matrix_A (mk_usize 0) j
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              (s_as_ntt.[ j ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              accumulator
              (s_cache.[ j ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let accumulator:t_Array i32 (mk_usize 256) = tmp0 in
          let s_cache:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s_cache j tmp1
          in
          accumulator, s_cache
          <:
          (t_Array i32 (mk_usize 256) &
            t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
  in
  let tt_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
      (mk_usize 0)
      (Libcrux_iot_ml_kem.Polynomial.impl_2__reducing_from_i32_array #v_Vector
          (accumulator <: t_Slice i32)
          (tt_as_ntt.[ mk_usize 0 ]
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
        <:
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let tt_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
      (mk_usize 0)
      (Libcrux_iot_ml_kem.Polynomial.impl_2__add_standard_error_reduce #v_Vector
          (tt_as_ntt.[ mk_usize 0 ]
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          (error_as_ntt.[ mk_usize 0 ]
            <:
            Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
        <:
        Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let
  (accumulator: t_Array i32 (mk_usize 256)),
  (tt_as_ntt: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
      v_K
      (fun temp_0_ temp_1_ ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (tt_as_ntt: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
          =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (accumulator, tt_as_ntt
        <:
        (t_Array i32 (mk_usize 256) &
          t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
      (fun temp_0_ i ->
          let
          (accumulator: t_Array i32 (mk_usize 256)),
          (tt_as_ntt: t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
          =
            temp_0_
          in
          let i:usize = i in
          let accumulator:t_Array i32 (mk_usize 256) =
            Rust_primitives.Hax.repeat (Libcrux_secrets.Traits.f_classify #i32
                  #FStar.Tactics.Typeclasses.solve
                  (mk_i32 0)
                <:
                i32)
              (mk_usize 256)
          in
          let accumulator:t_Array i32 (mk_usize 256) =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              v_K
              (fun accumulator temp_1_ ->
                  let accumulator:t_Array i32 (mk_usize 256) = accumulator in
                  let _:usize = temp_1_ in
                  true)
              accumulator
              (fun accumulator j ->
                  let accumulator:t_Array i32 (mk_usize 256) = accumulator in
                  let j:usize = j in
                  Libcrux_iot_ml_kem.Polynomial.impl_2__accumulating_ntt_multiply_use_cache #v_Vector
                    (entry v_K #v_Vector matrix_A i j
                      <:
                      Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    (s_as_ntt.[ j ]
                      <:
                      Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    accumulator
                    (s_cache.[ j ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
                    )
                  <:
                  t_Array i32 (mk_usize 256))
          in
          let tt_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
          =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
              i
              (Libcrux_iot_ml_kem.Polynomial.impl_2__reducing_from_i32_array #v_Vector
                  (accumulator <: t_Slice i32)
                  (tt_as_ntt.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
                  )
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let tt_as_ntt:t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
          =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
              i
              (Libcrux_iot_ml_kem.Polynomial.impl_2__add_standard_error_reduce #v_Vector
                  (tt_as_ntt.[ i ] <: Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
                  )
                  (error_as_ntt.[ i ]
                    <:
                    Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          accumulator, tt_as_ntt
          <:
          (t_Array i32 (mk_usize 256) &
            t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
  in
  tt_as_ntt, s_cache, accumulator
  <:
  (t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    t_Array (Libcrux_iot_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    t_Array i32 (mk_usize 256))
