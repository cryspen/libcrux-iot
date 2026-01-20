module Libcrux_iot_ml_kem.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Hash_functions in
  let open Libcrux_iot_ml_kem.Vector.Traits in
  let open Libcrux_secrets.Int in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

let sample_from_uniform_distribution_next
      (#v_Vector: Type0)
      (v_K v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (randomness: t_Slice (t_Array u8 v_N))
      (sampled_coefficients: t_Slice usize)
      (out: t_Slice (t_Array i16 (mk_usize 272)))
     =
  let (out: t_Slice (t_Array i16 (mk_usize 272))), (sampled_coefficients: t_Slice usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ temp_1_ ->
          let (out: t_Slice (t_Array i16 (mk_usize 272))), (sampled_coefficients: t_Slice usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          ((Core_models.Slice.impl__len #usize sampled_coefficients <: usize) =. v_K <: bool) &&
          ((Core_models.Slice.impl__len #(t_Array i16 (mk_usize 272)) out <: usize) =. v_K <: bool))
      (out, sampled_coefficients <: (t_Slice (t_Array i16 (mk_usize 272)) & t_Slice usize))
      (fun temp_0_ i ->
          let (out: t_Slice (t_Array i16 (mk_usize 272))), (sampled_coefficients: t_Slice usize) =
            temp_0_
          in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            (v_N /! mk_usize 24 <: usize)
            (fun temp_0_ temp_1_ ->
                let
                (out: t_Slice (t_Array i16 (mk_usize 272))), (sampled_coefficients: t_Slice usize) =
                  temp_0_
                in
                let _:usize = temp_1_ in
                ((Core_models.Slice.impl__len #usize sampled_coefficients <: usize) =. v_K <: bool) &&
                ((Core_models.Slice.impl__len #(t_Array i16 (mk_usize 272)) out <: usize) =. v_K
                  <:
                  bool))
            (out, sampled_coefficients <: (t_Slice (t_Array i16 (mk_usize 272)) & t_Slice usize))
            (fun temp_0_ r ->
                let
                (out: t_Slice (t_Array i16 (mk_usize 272))), (sampled_coefficients: t_Slice usize) =
                  temp_0_
                in
                let r:usize = r in
                if
                  (sampled_coefficients.[ i ] <: usize) <.
                  Libcrux_iot_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  <:
                  bool
                then
                  let (tmp0: t_Slice i16), (out1: usize) =
                    Libcrux_iot_ml_kem.Vector.Traits.f_rej_sample #v_Vector
                      #FStar.Tactics.Typeclasses.solve
                      ((randomness.[ i ] <: t_Array u8 v_N).[ {
                            Core_models.Ops.Range.f_start = r *! mk_usize 24 <: usize;
                            Core_models.Ops.Range.f_end
                            =
                            (r *! mk_usize 24 <: usize) +! mk_usize 24 <: usize
                          }
                          <:
                          Core_models.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                      ((out.[ i ] <: t_Array i16 (mk_usize 272)).[ {
                            Core_models.Ops.Range.f_start = sampled_coefficients.[ i ] <: usize;
                            Core_models.Ops.Range.f_end
                            =
                            (sampled_coefficients.[ i ] <: usize) +! mk_usize 16 <: usize
                          }
                          <:
                          Core_models.Ops.Range.t_Range usize ]
                        <:
                        t_Slice i16)
                  in
                  let out:t_Slice (t_Array i16 (mk_usize 272)) =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                      i
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ i ]
                            <:
                            t_Array i16 (mk_usize 272))
                          ({
                              Core_models.Ops.Range.f_start = sampled_coefficients.[ i ] <: usize;
                              Core_models.Ops.Range.f_end
                              =
                              (sampled_coefficients.[ i ] <: usize) +! mk_usize 16 <: usize
                            }
                            <:
                            Core_models.Ops.Range.t_Range usize)
                          tmp0
                        <:
                        t_Array i16 (mk_usize 272))
                  in
                  let sampled:usize = out1 in
                  let sampled_coefficients:t_Slice usize =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_coefficients
                      i
                      (Core_models.Num.impl_usize__wrapping_add (sampled_coefficients.[ i ] <: usize
                          )
                          sampled
                        <:
                        usize)
                  in
                  out, sampled_coefficients
                  <:
                  (t_Slice (t_Array i16 (mk_usize 272)) & t_Slice usize)
                else
                  out, sampled_coefficients
                  <:
                  (t_Slice (t_Array i16 (mk_usize 272)) & t_Slice usize))
          <:
          (t_Slice (t_Array i16 (mk_usize 272)) & t_Slice usize))
  in
  let done:bool = true in
  let (done: bool), (sampled_coefficients: t_Slice usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ temp_1_ ->
          let (done: bool), (sampled_coefficients: t_Slice usize) = temp_0_ in
          let _:usize = temp_1_ in
          (Core_models.Slice.impl__len #usize sampled_coefficients <: usize) =. v_K <: bool)
      (done, sampled_coefficients <: (bool & t_Slice usize))
      (fun temp_0_ i ->
          let (done: bool), (sampled_coefficients: t_Slice usize) = temp_0_ in
          let i:usize = i in
          if
            (sampled_coefficients.[ i ] <: usize) >=.
            Libcrux_iot_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            <:
            bool
          then
            let sampled_coefficients:t_Slice usize =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_coefficients
                i
                Libcrux_iot_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            in
            done, sampled_coefficients <: (bool & t_Slice usize)
          else false, sampled_coefficients <: (bool & t_Slice usize))
  in
  let hax_temp_output:bool = done in
  sampled_coefficients, out, hax_temp_output
  <:
  (t_Slice usize & t_Slice (t_Array i16 (mk_usize 272)) & bool)

#push-options "--admit_smt_queries true"

let sample_from_xof
      (v_K: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_iot_ml_kem.Hash_functions.t_Hash v_Hasher)
      (seeds: t_Slice (t_Array u8 (mk_usize 34)))
      (sampled_coefficients: t_Slice usize)
      (out: t_Slice (t_Array i16 (mk_usize 272)))
     =
  let xof_state:v_Hasher =
    Libcrux_iot_ml_kem.Hash_functions.f_shake128_init_absorb_final #v_Hasher
      #FStar.Tactics.Typeclasses.solve
      seeds
  in
  let randomness:t_Array (t_Array u8 (mk_usize 504)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 504)
        <:
        t_Array u8 (mk_usize 504))
      v_K
  in
  let randomness_blocksize:t_Array (t_Array u8 (mk_usize 168)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 168)
        <:
        t_Array u8 (mk_usize 168))
      v_K
  in
  let (tmp0: v_Hasher), (tmp1: t_Array (t_Array u8 (mk_usize 504)) v_K) =
    Libcrux_iot_ml_kem.Hash_functions.f_shake128_squeeze_first_three_blocks #v_Hasher
      #FStar.Tactics.Typeclasses.solve
      xof_state
      randomness
  in
  let xof_state:v_Hasher = tmp0 in
  let randomness:t_Array (t_Array u8 (mk_usize 504)) v_K = tmp1 in
  let _:Prims.unit = () in
  let (tmp0: t_Slice usize), (tmp1: t_Slice (t_Array i16 (mk_usize 272))), (out1: bool) =
    sample_from_uniform_distribution_next #v_Vector
      v_K
      (mk_usize 504)
      (randomness <: t_Slice (t_Array u8 (mk_usize 504)))
      sampled_coefficients
      out
  in
  let sampled_coefficients:t_Slice usize = tmp0 in
  let out:t_Slice (t_Array i16 (mk_usize 272)) = tmp1 in
  let done:bool = out1 in
  let
  (done: bool),
  (out: t_Slice (t_Array i16 (mk_usize 272))),
  (randomness_blocksize: t_Array (t_Array u8 (mk_usize 168)) v_K),
  (sampled_coefficients: t_Slice usize),
  (xof_state: v_Hasher) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let
          (done: bool),
          (out: t_Slice (t_Array i16 (mk_usize 272))),
          (randomness_blocksize: t_Array (t_Array u8 (mk_usize 168)) v_K),
          (sampled_coefficients: t_Slice usize),
          (xof_state: v_Hasher) =
            temp_0_
          in
          true)
      (fun temp_0_ ->
          let
          (done: bool),
          (out: t_Slice (t_Array i16 (mk_usize 272))),
          (randomness_blocksize: t_Array (t_Array u8 (mk_usize 168)) v_K),
          (sampled_coefficients: t_Slice usize),
          (xof_state: v_Hasher) =
            temp_0_
          in
          ~.done <: bool)
      (fun temp_0_ ->
          let
          (done: bool),
          (out: t_Slice (t_Array i16 (mk_usize 272))),
          (randomness_blocksize: t_Array (t_Array u8 (mk_usize 168)) v_K),
          (sampled_coefficients: t_Slice usize),
          (xof_state: v_Hasher) =
            temp_0_
          in
          Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
      (done, out, randomness_blocksize, sampled_coefficients, xof_state
        <:
        (bool & t_Slice (t_Array i16 (mk_usize 272)) & t_Array (t_Array u8 (mk_usize 168)) v_K &
          t_Slice usize &
          v_Hasher))
      (fun temp_0_ ->
          let
          (done: bool),
          (out: t_Slice (t_Array i16 (mk_usize 272))),
          (randomness_blocksize: t_Array (t_Array u8 (mk_usize 168)) v_K),
          (sampled_coefficients: t_Slice usize),
          (xof_state: v_Hasher) =
            temp_0_
          in
          let (tmp0: v_Hasher), (tmp1: t_Array (t_Array u8 (mk_usize 168)) v_K) =
            Libcrux_iot_ml_kem.Hash_functions.f_shake128_squeeze_next_block #v_Hasher
              #FStar.Tactics.Typeclasses.solve
              xof_state
              randomness_blocksize
          in
          let xof_state:v_Hasher = tmp0 in
          let randomness_blocksize:t_Array (t_Array u8 (mk_usize 168)) v_K = tmp1 in
          let _:Prims.unit = () in
          let (tmp0: t_Slice usize), (tmp1: t_Slice (t_Array i16 (mk_usize 272))), (out1: bool) =
            sample_from_uniform_distribution_next #v_Vector
              v_K
              (mk_usize 168)
              (randomness_blocksize <: t_Slice (t_Array u8 (mk_usize 168)))
              sampled_coefficients
              out
          in
          let sampled_coefficients:t_Slice usize = tmp0 in
          let out:t_Slice (t_Array i16 (mk_usize 272)) = tmp1 in
          let done:bool = out1 in
          done, out, randomness_blocksize, sampled_coefficients, xof_state
          <:
          (bool & t_Slice (t_Array i16 (mk_usize 272)) & t_Array (t_Array u8 (mk_usize 168)) v_K &
            t_Slice usize &
            v_Hasher))
  in
  sampled_coefficients, out <: (t_Slice usize & t_Slice (t_Array i16 (mk_usize 272)))

#pop-options

let sample_from_binomial_distribution_2_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (randomness: t_Slice u8)
      (sampled_i16s: t_Array i16 (mk_usize 256))
     =
  let sampled_i16s:t_Array i16 (mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 4)
      randomness
      (fun sampled_i16s temp_1_ ->
          let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
          let _:usize = temp_1_ in
          true)
      sampled_i16s
      (fun sampled_i16s temp_1_ ->
          let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
          let (chunk_number: usize), (byte_chunk: t_Slice u8) = temp_1_ in
          let (random_bits_as_u32: u32):u32 =
            (((Libcrux_secrets.Int.f_as_u32 #u8
                    #FStar.Tactics.Typeclasses.solve
                    (byte_chunk.[ mk_usize 0 ] <: u8)
                  <:
                  u32) |.
                ((Libcrux_secrets.Int.f_as_u32 #u8
                      #FStar.Tactics.Typeclasses.solve
                      (byte_chunk.[ mk_usize 1 ] <: u8)
                    <:
                    u32) <<!
                  mk_i32 8
                  <:
                  u32)
                <:
                u32) |.
              ((Libcrux_secrets.Int.f_as_u32 #u8
                    #FStar.Tactics.Typeclasses.solve
                    (byte_chunk.[ mk_usize 2 ] <: u8)
                  <:
                  u32) <<!
                mk_i32 16
                <:
                u32)
              <:
              u32) |.
            ((Libcrux_secrets.Int.f_as_u32 #u8
                  #FStar.Tactics.Typeclasses.solve
                  (byte_chunk.[ mk_usize 3 ] <: u8)
                <:
                u32) <<!
              mk_i32 24
              <:
              u32)
          in
          let even_bits:u32 =
            random_bits_as_u32 &.
            (Libcrux_secrets.Traits.f_classify #u32
                #FStar.Tactics.Typeclasses.solve
                (mk_u32 1431655765)
              <:
              u32)
          in
          let odd_bits:u32 =
            (random_bits_as_u32 >>! mk_i32 1 <: u32) &.
            (Libcrux_secrets.Traits.f_classify #u32
                #FStar.Tactics.Typeclasses.solve
                (mk_u32 1431655765)
              <:
              u32)
          in
          let coin_toss_outcomes:u32 = Core_models.Num.impl_u32__wrapping_add even_bits odd_bits in
          Rust_primitives.Hax.Folds.fold_range_step_by (mk_u32 0)
            (mk_u32 32)
            (mk_usize 4)
            (fun sampled_i16s temp_1_ ->
                let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
                let _:u32 = temp_1_ in
                true)
            sampled_i16s
            (fun sampled_i16s outcome_set ->
                let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
                let outcome_set:u32 = outcome_set in
                let outcome_1_:i16 =
                  Libcrux_secrets.Int.f_as_i16 #u32
                    #FStar.Tactics.Typeclasses.solve
                    ((coin_toss_outcomes >>! outcome_set <: u32) &.
                      (Libcrux_secrets.Traits.f_classify #u32
                          #FStar.Tactics.Typeclasses.solve
                          (mk_u32 3)
                        <:
                        u32)
                      <:
                      u32)
                in
                let outcome_2_:i16 =
                  Libcrux_secrets.Int.f_as_i16 #u32
                    #FStar.Tactics.Typeclasses.solve
                    ((coin_toss_outcomes >>!
                        (Core_models.Num.impl_u32__wrapping_add outcome_set (mk_u32 2) <: u32)
                        <:
                        u32) &.
                      (Libcrux_secrets.Traits.f_classify #u32
                          #FStar.Tactics.Typeclasses.solve
                          (mk_u32 3)
                        <:
                        u32)
                      <:
                      u32)
                in
                let offset:usize = cast (outcome_set >>! mk_i32 2 <: u32) <: usize in
                let sampled_i16s:t_Array i16 (mk_usize 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_i16s
                    ((mk_usize 8 *! chunk_number <: usize) +! offset <: usize)
                    (Core_models.Num.impl_i16__wrapping_sub outcome_1_ outcome_2_ <: i16)
                in
                sampled_i16s))
  in
  sampled_i16s

let sample_from_binomial_distribution_3_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (randomness: t_Slice u8)
      (sampled_i16s: t_Array i16 (mk_usize 256))
     =
  let sampled_i16s:t_Array i16 (mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 3)
      randomness
      (fun sampled_i16s temp_1_ ->
          let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
          let _:usize = temp_1_ in
          true)
      sampled_i16s
      (fun sampled_i16s temp_1_ ->
          let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
          let (chunk_number: usize), (byte_chunk: t_Slice u8) = temp_1_ in
          let (random_bits_as_u24: u32):u32 =
            ((Libcrux_secrets.Int.f_as_u32 #u8
                  #FStar.Tactics.Typeclasses.solve
                  (byte_chunk.[ mk_usize 0 ] <: u8)
                <:
                u32) |.
              ((Libcrux_secrets.Int.f_as_u32 #u8
                    #FStar.Tactics.Typeclasses.solve
                    (byte_chunk.[ mk_usize 1 ] <: u8)
                  <:
                  u32) <<!
                mk_i32 8
                <:
                u32)
              <:
              u32) |.
            ((Libcrux_secrets.Int.f_as_u32 #u8
                  #FStar.Tactics.Typeclasses.solve
                  (byte_chunk.[ mk_usize 2 ] <: u8)
                <:
                u32) <<!
              mk_i32 16
              <:
              u32)
          in
          let first_bits:u32 =
            random_bits_as_u24 &.
            (Libcrux_secrets.Traits.f_classify #u32
                #FStar.Tactics.Typeclasses.solve
                (mk_u32 2396745)
              <:
              u32)
          in
          let second_bits:u32 =
            (random_bits_as_u24 >>! mk_i32 1 <: u32) &.
            (Libcrux_secrets.Traits.f_classify #u32
                #FStar.Tactics.Typeclasses.solve
                (mk_u32 2396745)
              <:
              u32)
          in
          let third_bits:u32 =
            (random_bits_as_u24 >>! mk_i32 2 <: u32) &.
            (Libcrux_secrets.Traits.f_classify #u32
                #FStar.Tactics.Typeclasses.solve
                (mk_u32 2396745)
              <:
              u32)
          in
          let coin_toss_outcomes:u32 =
            Core_models.Num.impl_u32__wrapping_add first_bits
              (Core_models.Num.impl_u32__wrapping_add second_bits third_bits <: u32)
          in
          Rust_primitives.Hax.Folds.fold_range_step_by (mk_u8 0)
            (mk_u8 24)
            (mk_usize 6)
            (fun sampled_i16s temp_1_ ->
                let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
                let _:u8 = temp_1_ in
                true)
            sampled_i16s
            (fun sampled_i16s outcome_set ->
                let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
                let outcome_set:u8 = outcome_set in
                let outcome_1_:i16 =
                  Libcrux_secrets.Int.f_as_i16 #u32
                    #FStar.Tactics.Typeclasses.solve
                    ((coin_toss_outcomes >>! outcome_set <: u32) &.
                      (Libcrux_secrets.Traits.f_classify #u32
                          #FStar.Tactics.Typeclasses.solve
                          (mk_u32 7)
                        <:
                        u32)
                      <:
                      u32)
                in
                let outcome_2_:i16 =
                  Libcrux_secrets.Int.f_as_i16 #u32
                    #FStar.Tactics.Typeclasses.solve
                    ((coin_toss_outcomes >>!
                        (Core_models.Num.impl_u8__wrapping_add outcome_set (mk_u8 3) <: u8)
                        <:
                        u32) &.
                      (Libcrux_secrets.Traits.f_classify #u32
                          #FStar.Tactics.Typeclasses.solve
                          (mk_u32 7)
                        <:
                        u32)
                      <:
                      u32)
                in
                let offset:usize = cast (outcome_set /! mk_u8 6 <: u8) <: usize in
                let sampled_i16s:t_Array i16 (mk_usize 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_i16s
                    ((mk_usize 4 *! chunk_number <: usize) +! offset <: usize)
                    (Core_models.Num.impl_i16__wrapping_sub outcome_1_ outcome_2_ <: i16)
                in
                sampled_i16s))
  in
  sampled_i16s

let sample_from_binomial_distribution
      (v_ETA: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (randomness: t_Slice u8)
      (output: t_Array i16 (mk_usize 256))
     =
  let output:t_Array i16 (mk_usize 256) =
    match cast (v_ETA <: usize) <: u32 with
    | Rust_primitives.Integers.MkInt 2 ->
      sample_from_binomial_distribution_2_ #v_Vector randomness output
    | Rust_primitives.Integers.MkInt 3 ->
      sample_from_binomial_distribution_3_ #v_Vector randomness output
    | _ -> output
  in
  output
