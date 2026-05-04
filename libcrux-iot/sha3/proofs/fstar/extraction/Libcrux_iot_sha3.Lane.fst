module Libcrux_iot_sha3.Lane
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

/// A lane of the Keccak state,
type t_Lane2U32 = | Lane2U32 : t_Array u32 (mk_usize 2) -> t_Lane2U32

let impl_2: Core_models.Clone.t_Clone t_Lane2U32 =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Marker.t_Copy t_Lane2U32

unfold
let impl_3 = impl_3'

let impl_Lane2U32__from_ints (value: t_Array u32 (mk_usize 2)) : t_Lane2U32 =
  Lane2U32 value <: t_Lane2U32

let impl_Lane2U32__zero (_: Prims.unit) : t_Lane2U32 =
  impl_Lane2U32__from_ints (Libcrux_secrets.Traits.f_classify #(t_Array u32 (mk_usize 2))
        #FStar.Tactics.Typeclasses.solve
        (let list = [mk_u32 0; mk_u32 0] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
      <:
      t_Array u32 (mk_usize 2))

let impl_Lane2U32__deinterleave (self: t_Lane2U32) : t_Lane2U32 =
  let even_bits:u32 = self._0.[ mk_usize 0 ] in
  let odd_bits:u32 = self._0.[ mk_usize 1 ] in
  let even_spaced_lo:u32 = even_bits &. mk_u32 65535 in
  let even_spaced_lo:u32 =
    (even_spaced_lo ^. (even_spaced_lo <<! mk_i32 16 <: u32) <: u32) &. mk_u32 65535
  in
  let even_spaced_lo:u32 =
    (even_spaced_lo ^. (even_spaced_lo <<! mk_i32 8 <: u32) <: u32) &. mk_u32 16711935
  in
  let even_spaced_lo:u32 =
    (even_spaced_lo ^. (even_spaced_lo <<! mk_i32 4 <: u32) <: u32) &. mk_u32 252645135
  in
  let even_spaced_lo:u32 =
    (even_spaced_lo ^. (even_spaced_lo <<! mk_i32 2 <: u32) <: u32) &. mk_u32 858993459
  in
  let even_spaced_lo:u32 =
    (even_spaced_lo ^. (even_spaced_lo <<! mk_i32 1 <: u32) <: u32) &. mk_u32 1431655765
  in
  let even_spaced_hi:u32 = even_bits >>! mk_i32 16 in
  let even_spaced_hi:u32 =
    (even_spaced_hi ^. (even_spaced_hi <<! mk_i32 16 <: u32) <: u32) &. mk_u32 65535
  in
  let even_spaced_hi:u32 =
    (even_spaced_hi ^. (even_spaced_hi <<! mk_i32 8 <: u32) <: u32) &. mk_u32 16711935
  in
  let even_spaced_hi:u32 =
    (even_spaced_hi ^. (even_spaced_hi <<! mk_i32 4 <: u32) <: u32) &. mk_u32 252645135
  in
  let even_spaced_hi:u32 =
    (even_spaced_hi ^. (even_spaced_hi <<! mk_i32 2 <: u32) <: u32) &. mk_u32 858993459
  in
  let even_spaced_hi:u32 =
    (even_spaced_hi ^. (even_spaced_hi <<! mk_i32 1 <: u32) <: u32) &. mk_u32 1431655765
  in
  let odd_spaced_lo:u32 = odd_bits &. mk_u32 65535 in
  let odd_spaced_lo:u32 =
    (odd_spaced_lo ^. (odd_spaced_lo <<! mk_i32 16 <: u32) <: u32) &. mk_u32 65535
  in
  let odd_spaced_lo:u32 =
    (odd_spaced_lo ^. (odd_spaced_lo <<! mk_i32 8 <: u32) <: u32) &. mk_u32 16711935
  in
  let odd_spaced_lo:u32 =
    (odd_spaced_lo ^. (odd_spaced_lo <<! mk_i32 4 <: u32) <: u32) &. mk_u32 252645135
  in
  let odd_spaced_lo:u32 =
    (odd_spaced_lo ^. (odd_spaced_lo <<! mk_i32 2 <: u32) <: u32) &. mk_u32 858993459
  in
  let odd_spaced_lo:u32 =
    (odd_spaced_lo ^. (odd_spaced_lo <<! mk_i32 1 <: u32) <: u32) &. mk_u32 1431655765
  in
  let odd_spaced_hi:u32 = odd_bits >>! mk_i32 16 in
  let odd_spaced_hi:u32 =
    (odd_spaced_hi ^. (odd_spaced_hi <<! mk_i32 16 <: u32) <: u32) &. mk_u32 65535
  in
  let odd_spaced_hi:u32 =
    (odd_spaced_hi ^. (odd_spaced_hi <<! mk_i32 8 <: u32) <: u32) &. mk_u32 16711935
  in
  let odd_spaced_hi:u32 =
    (odd_spaced_hi ^. (odd_spaced_hi <<! mk_i32 4 <: u32) <: u32) &. mk_u32 252645135
  in
  let odd_spaced_hi:u32 =
    (odd_spaced_hi ^. (odd_spaced_hi <<! mk_i32 2 <: u32) <: u32) &. mk_u32 858993459
  in
  let odd_spaced_hi:u32 =
    (odd_spaced_hi ^. (odd_spaced_hi <<! mk_i32 1 <: u32) <: u32) &. mk_u32 1431655765
  in
  Lane2U32
  (let list =
      [
        even_spaced_lo |. (odd_spaced_lo <<! mk_i32 1 <: u32);
        even_spaced_hi |. (odd_spaced_hi <<! mk_i32 1 <: u32)
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
    Rust_primitives.Hax.array_of_list 2 list)
  <:
  t_Lane2U32

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core_models.Ops.Index.t_Index t_Lane2U32 usize =
  {
    f_Output = u32;
    f_index_pre = (fun (self_: t_Lane2U32) (index: usize) -> index <. mk_usize 2);
    f_index_post = (fun (self: t_Lane2U32) (index: usize) (out: u32) -> true);
    f_index = fun (self: t_Lane2U32) (index: usize) -> self._0.[ index ]
  }

let impl_Lane2U32__interleave (self: t_Lane2U32) : t_Lane2U32 =
  let lane_u64:u64 =
    (Libcrux_secrets.Int.f_as_u64 #u32 #FStar.Tactics.Typeclasses.solve (self.[ mk_usize 0 ] <: u32)
      <:
      u64) |.
    ((Libcrux_secrets.Int.f_as_u64 #u32
          #FStar.Tactics.Typeclasses.solve
          (self.[ mk_usize 1 ] <: u32)
        <:
        u64) <<!
      mk_i32 32
      <:
      u64)
  in
  let even_bits:u64 = lane_u64 &. mk_u64 6148914691236517205 in
  let even_bits:u64 =
    (even_bits ^. (even_bits >>! mk_i32 1 <: u64) <: u64) &. mk_u64 3689348814741910323
  in
  let even_bits:u64 =
    (even_bits ^. (even_bits >>! mk_i32 2 <: u64) <: u64) &. mk_u64 1085102592571150095
  in
  let even_bits:u64 =
    (even_bits ^. (even_bits >>! mk_i32 4 <: u64) <: u64) &. mk_u64 71777214294589695
  in
  let even_bits:u64 =
    (even_bits ^. (even_bits >>! mk_i32 8 <: u64) <: u64) &. mk_u64 281470681808895
  in
  let even_bits:u64 = (even_bits ^. (even_bits >>! mk_i32 16 <: u64) <: u64) &. mk_u64 4294967295 in
  let odd_bits:u64 = (lane_u64 >>! mk_i32 1 <: u64) &. mk_u64 6148914691236517205 in
  let odd_bits:u64 =
    (odd_bits ^. (odd_bits >>! mk_i32 1 <: u64) <: u64) &. mk_u64 3689348814741910323
  in
  let odd_bits:u64 =
    (odd_bits ^. (odd_bits >>! mk_i32 2 <: u64) <: u64) &. mk_u64 1085102592571150095
  in
  let odd_bits:u64 =
    (odd_bits ^. (odd_bits >>! mk_i32 4 <: u64) <: u64) &. mk_u64 71777214294589695
  in
  let odd_bits:u64 =
    (odd_bits ^. (odd_bits >>! mk_i32 8 <: u64) <: u64) &. mk_u64 281470681808895
  in
  let odd_bits:u64 = (odd_bits ^. (odd_bits >>! mk_i32 16 <: u64) <: u64) &. mk_u64 4294967295 in
  impl_Lane2U32__from_ints (let list =
        [
          Libcrux_secrets.Int.f_as_u32 #u64 #FStar.Tactics.Typeclasses.solve even_bits <: u32;
          Libcrux_secrets.Int.f_as_u32 #u64 #FStar.Tactics.Typeclasses.solve odd_bits <: u32
        ]
      in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
      Rust_primitives.Hax.array_of_list 2 list)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Convert.t_From t_Lane2U32 (t_Array u32 (mk_usize 2)) =
  {
    f_from_pre = (fun (value: t_Array u32 (mk_usize 2)) -> true);
    f_from_post = (fun (value: t_Array u32 (mk_usize 2)) (out: t_Lane2U32) -> true);
    f_from = fun (value: t_Array u32 (mk_usize 2)) -> Lane2U32 value <: t_Lane2U32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Fmt.t_Debug t_Lane2U32

unfold
let impl_5 = impl_5'
