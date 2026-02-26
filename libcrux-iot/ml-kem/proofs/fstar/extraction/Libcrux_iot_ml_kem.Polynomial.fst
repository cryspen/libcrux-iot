module Libcrux_iot_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Traits in
  ()

let zeta (i: usize) = v_ZETAS_TIMES_MONTGOMERY_R.[ i ]

let impl_2__ZERO
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (_: Prims.unit)
     =
  {
    f_coefficients
    =
    Rust_primitives.Hax.repeat (Libcrux_iot_ml_kem.Vector.Traits.f_ZERO #v_Vector
          #FStar.Tactics.Typeclasses.solve
          ()
        <:
        v_Vector)
      (mk_usize 16)
  }
  <:
  t_PolynomialRingElement v_Vector

let impl_2__poly_barrett_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun self temp_1_ ->
          let self:t_PolynomialRingElement v_Vector = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self i ->
          let self:t_PolynomialRingElement v_Vector = self in
          let i:usize = i in
          {
            self with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
              i
              (Libcrux_iot_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (self.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
            <:
            t_Array v_Vector (mk_usize 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  self

let impl_2__subtract_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self b: t_PolynomialRingElement v_Vector)
     =
  let b:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun b temp_1_ ->
          let b:t_PolynomialRingElement v_Vector = b in
          let _:usize = temp_1_ in
          true)
      b
      (fun b i ->
          let b:t_PolynomialRingElement v_Vector = b in
          let i:usize = i in
          let b:t_PolynomialRingElement v_Vector =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (b.f_coefficients.[ i ] <: v_Vector)
                    (mk_i16 1441)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let b:t_PolynomialRingElement v_Vector =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_sub #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (b.f_coefficients.[ i ] <: v_Vector)
                    (self.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let b:t_PolynomialRingElement v_Vector =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_negate #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (b.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let b:t_PolynomialRingElement v_Vector =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (b.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          b)
  in
  b

let impl_2__add_message_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self message result: t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
     =
  let (result: t_PolynomialRingElement v_Vector), (scratch: v_Vector) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun temp_0_ temp_1_ ->
          let (result: t_PolynomialRingElement v_Vector), (scratch: v_Vector) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (result, scratch <: (t_PolynomialRingElement v_Vector & v_Vector))
      (fun temp_0_ i ->
          let (result: t_PolynomialRingElement v_Vector), (scratch: v_Vector) = temp_0_ in
          let i:usize = i in
          let result:t_PolynomialRingElement v_Vector =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (result.f_coefficients.[ i ] <: v_Vector)
                    (mk_i16 1441)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let scratch:v_Vector = self.f_coefficients.[ i ] in
          let scratch:v_Vector =
            Libcrux_iot_ml_kem.Vector.Traits.f_add #v_Vector
              #FStar.Tactics.Typeclasses.solve
              scratch
              (message.f_coefficients.[ i ] <: v_Vector)
          in
          let result:t_PolynomialRingElement v_Vector =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_add #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (result.f_coefficients.[ i ] <: v_Vector)
                    scratch
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let result:t_PolynomialRingElement v_Vector =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                i
                (Libcrux_iot_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (result.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          result, scratch <: (t_PolynomialRingElement v_Vector & v_Vector))
  in
  result, scratch <: (t_PolynomialRingElement v_Vector & v_Vector)

let impl_2__add_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun self temp_1_ ->
          let self:t_PolynomialRingElement v_Vector = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self j ->
          let self:t_PolynomialRingElement v_Vector = self in
          let j:usize = j in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_iot_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (self.f_coefficients.[ j ] <: v_Vector)
                    (mk_i16 1441)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_iot_ml_kem.Vector.Traits.f_add #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (self.f_coefficients.[ j ] <: v_Vector)
                    (error.f_coefficients.[ j ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_iot_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (self.f_coefficients.[ j ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          self)
  in
  self

let impl_2__add_standard_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun self temp_1_ ->
          let self:t_PolynomialRingElement v_Vector = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self j ->
          let self:t_PolynomialRingElement v_Vector = self in
          let j:usize = j in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_iot_ml_kem.Vector.Traits.to_standard_domain #v_Vector
                    (self.f_coefficients.[ j ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_iot_ml_kem.Vector.Traits.f_add #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (self.f_coefficients.[ j ] <: v_Vector)
                    (error.f_coefficients.[ j ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let self:t_PolynomialRingElement v_Vector =
            {
              self with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_coefficients
                j
                (Libcrux_iot_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (self.f_coefficients.[ j ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          self)
  in
  self

let impl_2__accumulating_ntt_multiply_fill_cache
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
      (cache: t_PolynomialRingElement v_Vector)
     =
  let (accumulator: t_Array i32 (mk_usize 256)), (cache: t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun temp_0_ temp_1_ ->
          let (accumulator: t_Array i32 (mk_usize 256)), (cache: t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (accumulator, cache <: (t_Array i32 (mk_usize 256) & t_PolynomialRingElement v_Vector))
      (fun temp_0_ i ->
          let (accumulator: t_Array i32 (mk_usize 256)), (cache: t_PolynomialRingElement v_Vector) =
            temp_0_
          in
          let i:usize = i in
          let (tmp0: t_Slice i32), (tmp1: v_Vector) =
            Libcrux_iot_ml_kem.Vector.Traits.f_accumulating_ntt_multiply_fill_cache #v_Vector
              #FStar.Tactics.Typeclasses.solve (self.f_coefficients.[ i ] <: v_Vector)
              (rhs.f_coefficients.[ i ] <: v_Vector)
              (accumulator.[ {
                    Core_models.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                    Core_models.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice i32) (cache.f_coefficients.[ i ] <: v_Vector)
              (zeta (mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) <: i16)
              (zeta ((mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) +! mk_usize 1 <: usize)
                <:
                i16)
              (zeta ((mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) +! mk_usize 2 <: usize)
                <:
                i16)
              (zeta ((mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) +! mk_usize 3 <: usize)
                <:
                i16)
          in
          let accumulator:t_Array i32 (mk_usize 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range accumulator
              ({
                  Core_models.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                  Core_models.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              tmp0
          in
          let cache:t_PolynomialRingElement v_Vector =
            {
              cache with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize cache.f_coefficients
                i
                tmp1
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          accumulator, cache <: (t_Array i32 (mk_usize 256) & t_PolynomialRingElement v_Vector))
  in
  accumulator, cache <: (t_Array i32 (mk_usize 256) & t_PolynomialRingElement v_Vector)

let impl_2__accumulating_ntt_multiply_use_cache
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
      (cache: t_PolynomialRingElement v_Vector)
     =
  let accumulator:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun accumulator temp_1_ ->
          let accumulator:t_Array i32 (mk_usize 256) = accumulator in
          let _:usize = temp_1_ in
          true)
      accumulator
      (fun accumulator i ->
          let accumulator:t_Array i32 (mk_usize 256) = accumulator in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range accumulator
            ({
                Core_models.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                Core_models.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize)
            (Libcrux_iot_ml_kem.Vector.Traits.f_accumulating_ntt_multiply_use_cache #v_Vector
                #FStar.Tactics.Typeclasses.solve
                (self.f_coefficients.[ i ] <: v_Vector)
                (rhs.f_coefficients.[ i ] <: v_Vector)
                (accumulator.[ {
                      Core_models.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                      Core_models.Ops.Range.f_end
                      =
                      (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
                    }
                    <:
                    Core_models.Ops.Range.t_Range usize ]
                  <:
                  t_Slice i32)
                (cache.f_coefficients.[ i ] <: v_Vector)
              <:
              t_Slice i32)
          <:
          t_Array i32 (mk_usize 256))
  in
  accumulator

let impl_2__from_i16_array
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a: t_Slice i16)
      (out: t_PolynomialRingElement v_Vector)
     =
  let out:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun out temp_1_ ->
          let out:t_PolynomialRingElement v_Vector = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_PolynomialRingElement v_Vector = out in
          let i:usize = i in
          {
            out with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_coefficients
              i
              (Libcrux_iot_ml_kem.Vector.Traits.f_from_i16_array #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (a.[ {
                        Core_models.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice i16)
                  (out.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
            <:
            t_Array v_Vector (mk_usize 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  out

let impl_2__reducing_from_i32_array
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a: t_Slice i32)
      (out: t_PolynomialRingElement v_Vector)
     =
  let out:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun out temp_1_ ->
          let out:t_PolynomialRingElement v_Vector = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_PolynomialRingElement v_Vector = out in
          let i:usize = i in
          {
            out with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_coefficients
              i
              (Libcrux_iot_ml_kem.Vector.Traits.f_reducing_from_i32_array #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (a.[ {
                        Core_models.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice i32)
                  (out.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
            <:
            t_Array v_Vector (mk_usize 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  out

let impl_2__accumulating_ntt_multiply
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
     =
  let accumulator:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun accumulator temp_1_ ->
          let accumulator:t_Array i32 (mk_usize 256) = accumulator in
          let _:usize = temp_1_ in
          true)
      accumulator
      (fun accumulator i ->
          let accumulator:t_Array i32 (mk_usize 256) = accumulator in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range accumulator
            ({
                Core_models.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                Core_models.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize)
            (Libcrux_iot_ml_kem.Vector.Traits.f_accumulating_ntt_multiply #v_Vector
                #FStar.Tactics.Typeclasses.solve
                (self.f_coefficients.[ i ] <: v_Vector)
                (rhs.f_coefficients.[ i ] <: v_Vector)
                (accumulator.[ {
                      Core_models.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                      Core_models.Ops.Range.f_end
                      =
                      (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
                    }
                    <:
                    Core_models.Ops.Range.t_Range usize ]
                  <:
                  t_Slice i32)
                (zeta (mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) <: i16)
                (zeta ((mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) +! mk_usize 1 <: usize)
                  <:
                  i16)
                (zeta ((mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) +! mk_usize 2 <: usize)
                  <:
                  i16)
                (zeta ((mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) +! mk_usize 3 <: usize)
                  <:
                  i16)
              <:
              t_Slice i32)
          <:
          t_Array i32 (mk_usize 256))
  in
  accumulator
