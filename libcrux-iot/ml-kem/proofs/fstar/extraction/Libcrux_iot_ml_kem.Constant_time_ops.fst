module Libcrux_iot_ml_kem.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

let inz (value: u8) =
  let e_orig_value:u8 = value in
  let value:u16 = Libcrux_secrets.Int.f_as_u16 #u8 #FStar.Tactics.Typeclasses.solve value in
  let result:u8 =
    Core_models.Hint.black_box #u8
      (Libcrux_secrets.Int.f_as_u8 #u16
          #FStar.Tactics.Typeclasses.solve
          ((Core_models.Num.impl_u16__wrapping_add (~.(Core_models.Hint.black_box #u16 value <: u16)
                  <:
                  u16)
                (mk_u16 1)
              <:
              u16) >>!
            mk_i32 8
            <:
            u16)
        <:
        u8)
  in
  let res:u8 = result &. mk_u8 1 in
  let _:Prims.unit =
    lognot_lemma value;
    logand_lemma (mk_u8 1) result
  in
  res

let is_non_zero (value: u8) = Core_models.Hint.black_box #u8 (inz value <: u8)

let compare (lhs rhs: t_Slice u8) =
  let (r: u8):u8 =
    Libcrux_secrets.Traits.f_classify #u8 #FStar.Tactics.Typeclasses.solve (mk_u8 0)
  in
  let r:u8 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core_models.Slice.impl__len #u8 lhs <: usize)
      (fun r i ->
          let r:u8 = r in
          let i:usize = i in
          v i <= Seq.length lhs /\
          (if (Seq.slice lhs 0 (v i) = Seq.slice rhs 0 (v i))
            then r == (mk_u8 0)
            else ~(r == (mk_u8 0))))
      r
      (fun r i ->
          let r:u8 = r in
          let i:usize = i in
          let nr:u8 = r |. ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) in
          let _:Prims.unit =
            if r =. (mk_u8 0)
            then
              (if (Seq.index lhs (v i) = Seq.index rhs (v i))
                then
                  (logxor_lemma (Seq.index lhs (v i)) (Seq.index rhs (v i));
                    assert (((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) = zero);
                    logor_lemma r ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8);
                    assert (nr = r);
                    assert (forall j. Seq.index (Seq.slice lhs 0 (v i)) j == Seq.index lhs j);
                    assert (forall j. Seq.index (Seq.slice rhs 0 (v i)) j == Seq.index rhs j);
                    eq_intro (Seq.slice lhs 0 ((v i) + 1)) (Seq.slice rhs 0 ((v i) + 1)))
                else
                  (logxor_lemma (Seq.index lhs (v i)) (Seq.index rhs (v i));
                    assert (((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) <> zero);
                    logor_lemma r ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8);
                    assert (v nr > 0);
                    assert (Seq.index (Seq.slice lhs 0 ((v i) + 1)) (v i) <>
                        Seq.index (Seq.slice rhs 0 ((v i) + 1)) (v i));
                    assert (Seq.slice lhs 0 ((v i) + 1) <> Seq.slice rhs 0 ((v i) + 1))))
            else
              (logor_lemma r ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8);
                assert (v nr >= v r);
                assert (Seq.slice lhs 0 (v i) <> Seq.slice rhs 0 (v i));
                if (Seq.slice lhs 0 ((v i) + 1) = Seq.slice rhs 0 ((v i) + 1))
                then
                  (assert (forall j.
                          j < (v i) + 1 ==>
                          Seq.index (Seq.slice lhs 0 ((v i) + 1)) j ==
                          Seq.index (Seq.slice rhs 0 ((v i) + 1)) j);
                    eq_intro (Seq.slice lhs 0 (v i)) (Seq.slice rhs 0 (v i));
                    assert (False)))
          in
          let r:u8 = nr in
          r)
  in
  is_non_zero r

let compare_ciphertexts_in_constant_time (lhs rhs: t_Slice u8) =
  Core_models.Hint.black_box #u8 (compare lhs rhs <: u8)

#push-options "--ifuel 0 --z3rlimit 50"

let select_ct (lhs rhs: t_Slice u8) (selector: u8) (out: t_Slice u8) =
  let (out_orig: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Slice.impl__to_vec #u8 out
  in
  let mask:u8 = Core_models.Num.impl_u8__wrapping_sub (is_non_zero selector <: u8) (mk_u8 1) in
  let _:Prims.unit =
    assert (if selector = (mk_u8 0) then mask = ones else mask = zero);
    lognot_lemma mask;
    assert (if selector = (mk_u8 0) then ~.mask = zero else ~.mask = ones)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core_models.Slice.impl__len #u8 lhs <: usize)
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          v i <= v (Core_models.Slice.impl__len #u8 lhs) /\
          (forall j.
              j < v i ==>
              (if (selector =. (mk_u8 0))
                then Seq.index out j == Seq.index lhs j
                else Seq.index out j == Seq.index rhs j)) /\ Seq.length out == Seq.length out_orig)
      out
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          let outi:u8 =
            ((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)
          in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out i outi
          in
          let _:Prims.unit =
            if (selector = (mk_u8 0))
            then
              (logand_lemma (lhs.[ i ] <: u8) mask;
                assert (((lhs.[ i ] <: u8) &. mask <: u8) == (lhs.[ i ] <: u8));
                logand_lemma (rhs.[ i ] <: u8) (~.mask);
                assert (((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) == zero);
                logor_lemma ((lhs.[ i ] <: u8) &. mask <: u8)
                  ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8);
                assert ((((lhs.[ i ] <: u8) &. mask <: u8) |.
                      ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)
                      <:
                      u8) ==
                    (lhs.[ i ] <: u8));
                logor_lemma (out.[ i ] <: u8) (lhs.[ i ] <: u8);
                assert (outi = (lhs.[ i ] <: u8)))
            else
              (logand_lemma (lhs.[ i ] <: u8) mask;
                assert (((lhs.[ i ] <: u8) &. mask <: u8) == zero);
                logand_lemma (rhs.[ i ] <: u8) (~.mask);
                assert (((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) == (rhs.[ i ] <: u8));
                logor_lemma (rhs.[ i ] <: u8) zero;
                assert ((logor zero (rhs.[ i ] <: u8)) == (rhs.[ i ] <: u8));
                assert ((((lhs.[ i ] <: u8) &. mask <: u8) |.
                      ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)) ==
                    (rhs.[ i ] <: u8));
                logor_lemma (out.[ i ] <: u8) (rhs.[ i ] <: u8);
                assert (outi = (rhs.[ i ] <: u8)))
          in
          out)
  in
  let _:Prims.unit = if (selector =. (mk_u8 0)) then (eq_intro out lhs) else (eq_intro out rhs) in
  out

#pop-options

let select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8) (out: t_Slice u8) =
  let (hoist1: Prims.unit), (out: t_Slice u8) =
    (), select_ct lhs rhs selector out <: (Prims.unit & t_Slice u8)
  in
  let _:Prims.unit = Core_models.Hint.black_box #Prims.unit hoist1 in
  out

let compare_ciphertexts_select_shared_secret_in_constant_time
      (lhs_c rhs_c lhs_s rhs_s out: t_Slice u8)
     =
  let selector:u8 = compare_ciphertexts_in_constant_time lhs_c rhs_c in
  let out:t_Slice u8 = select_shared_secret_in_constant_time lhs_s rhs_s selector out in
  out
