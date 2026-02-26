module Libcrux_iot_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_ml_kem.Vector.Traits in
  ()

let v_ZETAS_TIMES_MONTGOMERY_R: t_Array i16 (mk_usize 128) =
  let list =
    [
      mk_i16 (-1044); mk_i16 (-758); mk_i16 (-359); mk_i16 (-1517); mk_i16 1493; mk_i16 1422;
      mk_i16 287; mk_i16 202; mk_i16 (-171); mk_i16 622; mk_i16 1577; mk_i16 182; mk_i16 962;
      mk_i16 (-1202); mk_i16 (-1474); mk_i16 1468; mk_i16 573; mk_i16 (-1325); mk_i16 264;
      mk_i16 383; mk_i16 (-829); mk_i16 1458; mk_i16 (-1602); mk_i16 (-130); mk_i16 (-681);
      mk_i16 1017; mk_i16 732; mk_i16 608; mk_i16 (-1542); mk_i16 411; mk_i16 (-205); mk_i16 (-1571);
      mk_i16 1223; mk_i16 652; mk_i16 (-552); mk_i16 1015; mk_i16 (-1293); mk_i16 1491;
      mk_i16 (-282); mk_i16 (-1544); mk_i16 516; mk_i16 (-8); mk_i16 (-320); mk_i16 (-666);
      mk_i16 (-1618); mk_i16 (-1162); mk_i16 126; mk_i16 1469; mk_i16 (-853); mk_i16 (-90);
      mk_i16 (-271); mk_i16 830; mk_i16 107; mk_i16 (-1421); mk_i16 (-247); mk_i16 (-951);
      mk_i16 (-398); mk_i16 961; mk_i16 (-1508); mk_i16 (-725); mk_i16 448; mk_i16 (-1065);
      mk_i16 677; mk_i16 (-1275); mk_i16 (-1103); mk_i16 430; mk_i16 555; mk_i16 843; mk_i16 (-1251);
      mk_i16 871; mk_i16 1550; mk_i16 105; mk_i16 422; mk_i16 587; mk_i16 177; mk_i16 (-235);
      mk_i16 (-291); mk_i16 (-460); mk_i16 1574; mk_i16 1653; mk_i16 (-246); mk_i16 778; mk_i16 1159;
      mk_i16 (-147); mk_i16 (-777); mk_i16 1483; mk_i16 (-602); mk_i16 1119; mk_i16 (-1590);
      mk_i16 644; mk_i16 (-872); mk_i16 349; mk_i16 418; mk_i16 329; mk_i16 (-156); mk_i16 (-75);
      mk_i16 817; mk_i16 1097; mk_i16 603; mk_i16 610; mk_i16 1322; mk_i16 (-1285); mk_i16 (-1465);
      mk_i16 384; mk_i16 (-1215); mk_i16 (-136); mk_i16 1218; mk_i16 (-1335); mk_i16 (-874);
      mk_i16 220; mk_i16 (-1187); mk_i16 (-1659); mk_i16 (-1185); mk_i16 (-1530); mk_i16 (-1278);
      mk_i16 794; mk_i16 (-1510); mk_i16 (-854); mk_i16 (-870); mk_i16 478; mk_i16 (-108);
      mk_i16 (-308); mk_i16 996; mk_i16 991; mk_i16 958; mk_i16 (-1460); mk_i16 1522; mk_i16 1628
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 128);
  Rust_primitives.Hax.array_of_list 128 list

val zeta (i: usize) : Prims.Pure i16 (requires i <. mk_usize 128) (fun _ -> Prims.l_True)

let v_VECTORS_IN_RING_ELEMENT: usize =
  Libcrux_iot_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /!
  Libcrux_iot_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR

type t_PolynomialRingElement
  (v_Vector: Type0) {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = { f_coefficients:t_Array v_Vector (mk_usize 16) }

val impl_2__ZERO:
    #v_Vector: Type0 ->
    {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |} ->
    Prims.unit
  -> Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__poly_barrett_reduce
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__subtract_reduce
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self b: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__add_message_error_reduce
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self message result: t_PolynomialRingElement v_Vector)
      (scratch: v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector & v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__add_error_reduce
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self error: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__add_standard_error_reduce
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self error: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__accumulating_ntt_multiply_fill_cache
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self rhs: t_PolynomialRingElement v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
      (cache: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array i32 (mk_usize 256) & t_PolynomialRingElement v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__accumulating_ntt_multiply_use_cache
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self rhs: t_PolynomialRingElement v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
      (cache: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array i32 (mk_usize 256)) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__from_i16_array
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a: t_Slice i16)
      (out: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector)
      (requires
        (v_VECTORS_IN_RING_ELEMENT *! mk_usize 16 <: usize) <=.
        (Core_models.Slice.impl__len #i16 a <: usize))
      (fun _ -> Prims.l_True)

val impl_2__reducing_from_i32_array
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a: t_Slice i32)
      (out: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector)
      (requires
        (v_VECTORS_IN_RING_ELEMENT *! mk_usize 16 <: usize) <=.
        (Core_models.Slice.impl__len #i32 a <: usize))
      (fun _ -> Prims.l_True)

val impl_2__accumulating_ntt_multiply
      (#v_Vector: Type0)
      {| i0: Libcrux_iot_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self rhs: t_PolynomialRingElement v_Vector)
      (accumulator: t_Array i32 (mk_usize 256))
    : Prims.Pure (t_Array i32 (mk_usize 256))
      (requires
        (Core_models.Slice.impl__len #i32 (accumulator <: t_Slice i32) <: usize) >=.
        (mk_usize 16 *! v_VECTORS_IN_RING_ELEMENT <: usize))
      (fun _ -> Prims.l_True)
