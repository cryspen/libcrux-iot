/-
  # Phase 1a prerequisite — Aeneas-Result lifts of `Lane2U32.interleave` /
  # `Lane2U32.deinterleave`.

  Bridges the impl's 13-stage bit-deposit code (`Extraction/Funs.lean` lines
  116-163 and 3993-4065) to the pure-`BitVec` models `interleave_bv` /
  `deinterleave_bv` already proved in `Sponge/Bytes.lean`.

  Both Triples post:
  - `interleave_spec`:  the two output halves equal `interleave_bv  lo hi`.
  - `deinterleave_spec`: the two output halves equal `deinterleave_bv e o`.

  Composing with `interleave_bv_lift_eq` / `deinterleave_bv_lift_eq` in
  `Sponge/Bytes.lean` recovers the LE-concatenated `u64` form for the
  byte-bridge layer.

  Technique: the proof is a pure `hax_mvcgen` walk through ~30 `Std.U32`/
  `Std.U64` ops, finishing with a single `BitVec` equality closed by
  `bv_decide` (after exposing the underlying `.bv` content through
  `Std.U32.bv_eq_imp_eq` / `Std.U64.bv_eq_imp_eq` + `UScalar.bv_*`).
-/
import LibcruxIotSha3.Sponge.Bytes

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Aeneas-`Result` lift of `Lane2U32.interleave`.

The impl (Extraction/Funs.lean:116-163) reads `self.val[0]!`/`self.val[1]!`
as the input halves `(lo, hi)`, casts to `u64`, ORs `(hi << 32) ||| lo`
into a 64-bit word, runs 11 sequential masking/shift/XOR stages on each of
the two parity tracks, and finally projects the low 32 bits of each track.
The pure model `interleave_bv` mirrors this exactly. -/
@[spec]
theorem lane.Lane2U32.interleave_spec (self : lane.Lane2U32) :
    ⦃ ⌜ True ⌝ ⦄
    lane.Lane2U32.interleave self
    ⦃ ⇓ r => ⌜ ((r.val[0]!).bv, (r.val[1]!).bv) =
                interleave_bv (self.val[0]!).bv (self.val[1]!).bv ⌝ ⦄ := by
  unfold lane.Lane2U32.interleave
  unfold libcrux_secrets.U32.Insts.Libcrux_secretsIntCastOps.as_u64
  unfold libcrux_secrets.U64.Insts.Libcrux_secretsIntCastOps.as_u32
  unfold lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index
  unfold lane.Lane2U32.from_ints
  hax_mvcgen
  all_goals
    first
    | scalar_tac
    | (simp only [interleave_bv, Std.UScalar.cast, BitVec.truncate_eq_setWidth,
                  Std.Array.make,
                  List.getElem!_cons_zero, List.getElem!_cons_succ,
                  Std.U32.bv, Std.U64.bv,
                  Std.UScalarTy.U32_numBits_eq, Std.UScalarTy.U64_numBits_eq,
                  Std.U64.ofNat_bv,
                  show ((0#usize : Std.Usize).val) = 0 from rfl,
                  show ((1#usize : Std.Usize).val) = 1 from rfl,
                  show (1#i32).toNat  = 1 from rfl,
                  show (2#i32).toNat  = 2 from rfl,
                  show (4#i32).toNat  = 4 from rfl,
                  show (8#i32).toNat  = 8 from rfl,
                  show (16#i32).toNat = 16 from rfl,
                  show (32#i32).toNat = 32 from rfl, *]
       try (refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩ <;> bv_decide))

/-! ## Aeneas-`Result` lift of `Lane2U32.deinterleave`.

The impl (Extraction/Funs.lean:3993-4065) reads `self.val[0]!` (even bits)
and `self.val[1]!` (odd bits), runs four parallel 11-stage deposit chains
(evlo, evhi, odlo, odhi), and assembles the two output halves as
`evlo5 ||| (odlo5 <<< 1)` and `evhi5 ||| (odhi5 <<< 1)`. The pure model
`deinterleave_bv` mirrors this exactly. -/
@[spec]
theorem lane.Lane2U32.deinterleave_spec (self : lane.Lane2U32) :
    ⦃ ⌜ True ⌝ ⦄
    lane.Lane2U32.deinterleave self
    ⦃ ⇓ r => ⌜ ((r.val[0]!).bv, (r.val[1]!).bv) =
                deinterleave_bv (self.val[0]!).bv (self.val[1]!).bv ⌝ ⦄ := by
  unfold lane.Lane2U32.deinterleave
  hax_mvcgen
  all_goals
    first
    | scalar_tac
    | (simp only [deinterleave_bv, Std.Array.make,
                  List.getElem!_cons_zero, List.getElem!_cons_succ,
                  Std.U32.bv,
                  Std.UScalarTy.U32_numBits_eq,
                  Std.U32.ofNat_bv,
                  show ((0#usize : Std.Usize).val) = 0 from rfl,
                  show ((1#usize : Std.Usize).val) = 1 from rfl,
                  show (1#i32).toNat  = 1 from rfl,
                  show (2#i32).toNat  = 2 from rfl,
                  show (4#i32).toNat  = 4 from rfl,
                  show (8#i32).toNat  = 8 from rfl,
                  show (16#i32).toNat = 16 from rfl, *]
       try (refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩ <;> bv_decide))

end libcrux_iot_sha3.Sponge
