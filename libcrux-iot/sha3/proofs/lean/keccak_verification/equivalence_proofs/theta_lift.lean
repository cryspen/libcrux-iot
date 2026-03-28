import keccak_verification.spec.hacspec_sha3
import keccak_verification.implementation.libcrux_iot_sha3
import keccak_verification.equivalence_proofs.spec_decomp
import keccak_verification.equivalence_proofs.lift_defs
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## Theta step: lifting proof

Proves that the bit-interleaved theta implementation produces the same result
as the standard u64 theta specification (after lifting).

### Architecture

The proof is split into two phases:
1. **Impl-only WP** (`theta_comp_spec_local`): Runs `hax_mvcgen` on just the
   implementation to extract concrete d-value equations. Cost: 2M heartbeats.
2. **Pure algebraic bridge** (`theta_lift_spec`): Connects the concrete d-values
   to `spec_theta_unrolled(lift(s))` using lifting lemmas (`lift_xor`, `lift_td`,
   `lift_xor5`). No hax_mvcgen on combined impl+spec.

### Key optimization: `@[local irreducible]`

`spread_to_even` and `lift_lane_bv` are marked irreducible after the lifting lemmas
are proven by `bv_decide`. This prevents simp from unfolding them during the algebraic
bridge, keeping terms at the opaque `lift_lane_bv` level (~50 bytes) instead of
expanding to 6-step bit-manipulation chains (~500 bytes each × 175 occurrences).

### Closing the vector equality

After simp normalizes both sides to `#v[...]` vectors of opaque `lift_lane_bv` terms,
we cannot use `rfl` (kernel `isDefEq` ignores `@[irreducible]` and would unfold
everything). Instead, `congr 1; repeat' congr 1` decomposes into per-element goals
that simp can close without kernel involvement. The rotation mismatch in the theta-d
values is resolved by `← lift_xor5` (collapsing XOR) and `lift_rot1` (odd rotation).
-/

-- Lifting lemmas: proven by bv_decide BEFORE marking irreducible.
-- These rewrite at the lift_lane_bv level without needing its body.

/-- XOR distributes through interleaved lifting. -/
private theorem lift_xor (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-- Theta-d structure lifts: interleaved (cL ⊕ rot(cR,1)) = lifted(cL) ⊕ rotateLeft(lifted(cR),1). -/
private theorem lift_td (cL0 cL1 cR0 cR1 : BitVec 32) :
    lift_lane_bv (cL0 ^^^ cR1.rotateLeft 1) (cL1 ^^^ cR0) =
    lift_lane_bv cL0 cL1 ^^^ (lift_lane_bv cR0 cR1).rotateLeft 1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-- Odd rotation by 1: halves swap with adjusted sub-rotations.
    rotateLeft(lift(z0,z1), 1) = lift(rot(z1,1), z0). -/
private theorem lift_rot1 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 1 = lift_lane_bv (z1.rotateLeft 1) z0 := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-- XOR of 5 lanes distributes through interleaved lifting. -/
private theorem lift_xor5 (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0 ^^^ c0 ^^^ d0 ^^^ e0) (a1 ^^^ b1 ^^^ c1 ^^^ d1 ^^^ e1) =
    lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 ^^^ lift_lane_bv c0 c1 ^^^ lift_lane_bv d0 d1 ^^^ lift_lane_bv e0 e1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

-- After proving all lifting lemmas, mark the bit-spreading functions irreducible.
-- All subsequent reasoning uses the lemmas above, never the function bodies.
attribute [local irreducible] spread_to_even lift_lane_bv

/-- Bridge lemma: indexing into `lift s` gives `UInt64.ofBitVec(lift_lane_bv(z0, z1))`
    without needing to unfold `lift` or `lift_lane` in the main proof. -/
private theorem lift_getElem (s : KeccakState) (i : Nat) (hi : i < (25 : usize).toNat) :
    (lift s).toVec[i] =
    UInt64.ofBitVec (lift_lane_bv s.st.toVec[i]._0.toVec[0].toBitVec s.st.toVec[i]._0.toVec[1].toBitVec) := by
  unfold lift lift_lane
  show (RustArray.ofVec (Vector.ofFn _)).toVec[i] = _
  simp only [RustArray.toVec, Vector.getElem_ofFn]
  rfl

-- Explicit simp lemmas for UInt32/UInt64 BitVec conversions.
-- These are all `rfl` but simp needs them stated explicitly to match patterns
-- like `(a ^^^ b).toBitVec` inside lift_lane_bv arguments.
private theorem u32_xor_toBitVec (a b : UInt32) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl
private theorem u32_ofBitVec_toBitVec (x : BitVec 32) : (UInt32.ofBitVec x).toBitVec = x := rfl
private theorem u64_ofBitVec_xor (a b : BitVec 64) : UInt64.ofBitVec (a ^^^ b) = UInt64.ofBitVec a ^^^ UInt64.ofBitVec b := rfl
private theorem u64_toBitVec_ofBitVec (x : BitVec 64) : (UInt64.ofBitVec x).toBitVec = x := rfl
private theorem u64_xor_toBitVec (a b : UInt64) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

/-- Per-lane theta application: XOR state lane with its d-value, then lift to u64.
    Using a concrete `#v[...]` literal (not `Vector.ofFn`) so that the algebraic bridge
    produces syntactically identical vector forms on both sides. -/
abbrev lta (st_z0 st_z1 d_z0 d_z1 : u32) : u64 :=
  UInt64.ofBitVec (lift_lane_bv ((st_z0 ^^^ d_z0).toBitVec) ((st_z1 ^^^ d_z1).toBitVec))

/-- The lifted result of the theta step: each lane XOR'd with its d-value group.
    Lanes 0-4 use d[0], lanes 5-9 use d[1], etc. -/
def lift_theta_applied (s : KeccakState) : RustArray u64 25 :=
  let d := s.d; let st := s.st
  RustArray.ofVec #v[
    lta st.toVec[0]._0.toVec[0] st.toVec[0]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[1]._0.toVec[0] st.toVec[1]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[2]._0.toVec[0] st.toVec[2]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[3]._0.toVec[0] st.toVec[3]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[4]._0.toVec[0] st.toVec[4]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[5]._0.toVec[0] st.toVec[5]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[6]._0.toVec[0] st.toVec[6]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[7]._0.toVec[0] st.toVec[7]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[8]._0.toVec[0] st.toVec[8]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[9]._0.toVec[0] st.toVec[9]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[10]._0.toVec[0] st.toVec[10]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[11]._0.toVec[0] st.toVec[11]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[12]._0.toVec[0] st.toVec[12]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[13]._0.toVec[0] st.toVec[13]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[14]._0.toVec[0] st.toVec[14]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[15]._0.toVec[0] st.toVec[15]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[16]._0.toVec[0] st.toVec[16]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[17]._0.toVec[0] st.toVec[17]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[18]._0.toVec[0] st.toVec[18]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[19]._0.toVec[0] st.toVec[19]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[20]._0.toVec[0] st.toVec[20]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1],
    lta st.toVec[21]._0.toVec[0] st.toVec[21]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1],
    lta st.toVec[22]._0.toVec[0] st.toVec[22]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1],
    lta st.toVec[23]._0.toVec[0] st.toVec[23]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1],
    lta st.toVec[24]._0.toVec[0] st.toVec[24]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1]]

/-! ### Phase 1: Impl-only Hoare triple for theta

Duplicates the `theta_comp_proof` tactic from step_equiv.lean.
Runs hax_mvcgen on just the theta implementation to extract concrete d-value equations.
The postcondition gives all 10 d-value halves (5 groups × z0/z1) plus st/i preservation.
-/
local macro "theta_comp_proof_local" : tactic =>
  `(tactic| (
    hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_keccak_verification]
    all_goals (first | intro h₁; subst h₁ | skip)
    all_goals simp (config := { decide := true }) only [getElemResult, core_models.ops.index.Index.index,
      ↓reduceDIte, USize64.reduceToNat, USize64.add_zero, USize64.toNat_zero, ↓reduceIte,
      USize64.toBitVec_ofNat, bind_pure_comp, pure_bind, USize64.reduceAdd, map_pure,
      Vector.size, Nat.zero_lt_succ, bind_pure, Std.Do.WP.pure, Vector.getElem_set,
      Std.Do.SPred.down_pure, rot32,
      show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl,
      show (2 : usize).toNat = 2 from rfl]
    all_goals (repeat' constructor)
    all_goals (first | subst_vars; rfl | rfl)))

-- Impl-only Hoare triple for theta: produces concrete d-value equations.
-- d[x].z0 = c[(x+4) mod 5].z0 XOR rot32(c[(x+1) mod 5].z1, 1)
-- d[x].z1 = c[(x+4) mod 5].z1 XOR c[(x+1) mod 5].z0
-- where c[x] = XOR of 5 lanes in column x.
set_option maxHeartbeats 2000000 in
open Std.Do in
private theorem theta_comp_spec_local (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜
      r.d.toVec[0]._0.toVec[0] =
        (s.st.toVec[20]._0.toVec[0] ^^^ s.st.toVec[21]._0.toVec[0] ^^^
         s.st.toVec[22]._0.toVec[0] ^^^ s.st.toVec[23]._0.toVec[0] ^^^
         s.st.toVec[24]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[5]._0.toVec[1] ^^^ s.st.toVec[6]._0.toVec[1] ^^^
               s.st.toVec[7]._0.toVec[1] ^^^ s.st.toVec[8]._0.toVec[1] ^^^
               s.st.toVec[9]._0.toVec[1]) 1
      ∧
      r.d.toVec[0]._0.toVec[1] =
        (s.st.toVec[20]._0.toVec[1] ^^^ s.st.toVec[21]._0.toVec[1] ^^^
         s.st.toVec[22]._0.toVec[1] ^^^ s.st.toVec[23]._0.toVec[1] ^^^
         s.st.toVec[24]._0.toVec[1]) ^^^
        (s.st.toVec[5]._0.toVec[0] ^^^ s.st.toVec[6]._0.toVec[0] ^^^
         s.st.toVec[7]._0.toVec[0] ^^^ s.st.toVec[8]._0.toVec[0] ^^^
         s.st.toVec[9]._0.toVec[0])
      ∧
      r.d.toVec[1]._0.toVec[0] =
        (s.st.toVec[0]._0.toVec[0] ^^^ s.st.toVec[1]._0.toVec[0] ^^^
         s.st.toVec[2]._0.toVec[0] ^^^ s.st.toVec[3]._0.toVec[0] ^^^
         s.st.toVec[4]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[10]._0.toVec[1] ^^^ s.st.toVec[11]._0.toVec[1] ^^^
               s.st.toVec[12]._0.toVec[1] ^^^ s.st.toVec[13]._0.toVec[1] ^^^
               s.st.toVec[14]._0.toVec[1]) 1
      ∧
      r.d.toVec[1]._0.toVec[1] =
        (s.st.toVec[0]._0.toVec[1] ^^^ s.st.toVec[1]._0.toVec[1] ^^^
         s.st.toVec[2]._0.toVec[1] ^^^ s.st.toVec[3]._0.toVec[1] ^^^
         s.st.toVec[4]._0.toVec[1]) ^^^
        (s.st.toVec[10]._0.toVec[0] ^^^ s.st.toVec[11]._0.toVec[0] ^^^
         s.st.toVec[12]._0.toVec[0] ^^^ s.st.toVec[13]._0.toVec[0] ^^^
         s.st.toVec[14]._0.toVec[0])
      ∧
      r.d.toVec[2]._0.toVec[0] =
        (s.st.toVec[5]._0.toVec[0] ^^^ s.st.toVec[6]._0.toVec[0] ^^^
         s.st.toVec[7]._0.toVec[0] ^^^ s.st.toVec[8]._0.toVec[0] ^^^
         s.st.toVec[9]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[15]._0.toVec[1] ^^^ s.st.toVec[16]._0.toVec[1] ^^^
               s.st.toVec[17]._0.toVec[1] ^^^ s.st.toVec[18]._0.toVec[1] ^^^
               s.st.toVec[19]._0.toVec[1]) 1
      ∧
      r.d.toVec[2]._0.toVec[1] =
        (s.st.toVec[5]._0.toVec[1] ^^^ s.st.toVec[6]._0.toVec[1] ^^^
         s.st.toVec[7]._0.toVec[1] ^^^ s.st.toVec[8]._0.toVec[1] ^^^
         s.st.toVec[9]._0.toVec[1]) ^^^
        (s.st.toVec[15]._0.toVec[0] ^^^ s.st.toVec[16]._0.toVec[0] ^^^
         s.st.toVec[17]._0.toVec[0] ^^^ s.st.toVec[18]._0.toVec[0] ^^^
         s.st.toVec[19]._0.toVec[0])
      ∧
      r.d.toVec[3]._0.toVec[0] =
        (s.st.toVec[10]._0.toVec[0] ^^^ s.st.toVec[11]._0.toVec[0] ^^^
         s.st.toVec[12]._0.toVec[0] ^^^ s.st.toVec[13]._0.toVec[0] ^^^
         s.st.toVec[14]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[20]._0.toVec[1] ^^^ s.st.toVec[21]._0.toVec[1] ^^^
               s.st.toVec[22]._0.toVec[1] ^^^ s.st.toVec[23]._0.toVec[1] ^^^
               s.st.toVec[24]._0.toVec[1]) 1
      ∧
      r.d.toVec[3]._0.toVec[1] =
        (s.st.toVec[10]._0.toVec[1] ^^^ s.st.toVec[11]._0.toVec[1] ^^^
         s.st.toVec[12]._0.toVec[1] ^^^ s.st.toVec[13]._0.toVec[1] ^^^
         s.st.toVec[14]._0.toVec[1]) ^^^
        (s.st.toVec[20]._0.toVec[0] ^^^ s.st.toVec[21]._0.toVec[0] ^^^
         s.st.toVec[22]._0.toVec[0] ^^^ s.st.toVec[23]._0.toVec[0] ^^^
         s.st.toVec[24]._0.toVec[0])
      ∧
      r.d.toVec[4]._0.toVec[0] =
        (s.st.toVec[15]._0.toVec[0] ^^^ s.st.toVec[16]._0.toVec[0] ^^^
         s.st.toVec[17]._0.toVec[0] ^^^ s.st.toVec[18]._0.toVec[0] ^^^
         s.st.toVec[19]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[0]._0.toVec[1] ^^^ s.st.toVec[1]._0.toVec[1] ^^^
               s.st.toVec[2]._0.toVec[1] ^^^ s.st.toVec[3]._0.toVec[1] ^^^
               s.st.toVec[4]._0.toVec[1]) 1
      ∧
      r.d.toVec[4]._0.toVec[1] =
        (s.st.toVec[15]._0.toVec[1] ^^^ s.st.toVec[16]._0.toVec[1] ^^^
         s.st.toVec[17]._0.toVec[1] ^^^ s.st.toVec[18]._0.toVec[1] ^^^
         s.st.toVec[19]._0.toVec[1]) ^^^
        (s.st.toVec[0]._0.toVec[0] ^^^ s.st.toVec[1]._0.toVec[0] ^^^
         s.st.toVec[2]._0.toVec[0] ^^^ s.st.toVec[3]._0.toVec[0] ^^^
         s.st.toVec[4]._0.toVec[0])
      ∧
      r.st = s.st ∧ r.i = s.i
    ⌝ ⦄ := by theta_comp_proof_local

/-! ### Phase 2: Algebraic bridge

Proves `spec_theta_unrolled(lift(s)) = lift_theta_applied(r)` where `r` is the
theta implementation output. The proof:

1. `Triple.bind` splits at the impl/spec boundary
2. `theta_comp_spec_local` provides concrete d-values for the impl side
3. `Triple.pure` + `SPred.pure_intro` extracts the pure algebraic equation
4. `simp` with lifting lemmas normalizes both sides to `#v[...]` of `lift_lane_bv` terms
5. `congr` decomposes the vector, `← lift_xor5` + `lift_rot1` close the rotation goals
-/
set_option maxHeartbeats 16000000 in
open Std.Do in
theorem theta_lift_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
       let r_spec ← spec_theta_unrolled (lift s)
       pure (r_spec = lift_theta_applied r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  -- Reduce spec_theta_unrolled(lift s) to pure (all let-bindings are non-monadic)
  show ⦃⌜True⌝⦄
    (libcrux_iot_sha3.keccak.keccakf1600_round0_theta s >>= fun r_impl =>
      spec_theta_unrolled (lift s) >>= fun r_spec =>
      pure (r_spec = lift_theta_applied r_impl))
    ⦃PostCond.noThrow fun r => ⌜r⌝⦄
  conv in spec_theta_unrolled _ >>= _ =>
    unfold spec_theta_unrolled
    simp only [pure_bind, RustArray.ofVec, Vector.getElem_ofFn, theta_result, theta_d_val, theta_col,
      show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl]
  -- Split: impl WP (via theta_comp_spec_local) then pure algebraic bridge
  apply Triple.bind
  case hx => exact theta_comp_spec_local s
  case hf =>
    intro r
    apply Triple.pure
    rw [← SPred.entails_true_intro]
    exact SPred.pure_intro fun ⟨hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1, hd3z0, hd3z1, hd4z0, hd4z1, hst, _hi⟩ => by
      -- Normalize both sides to #v[...] of lift_lane_bv terms
      simp only [lift_theta_applied, lta, hst,
                  hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1, hd3z0, hd3z1, hd4z0, hd4z1,
                  lift_getElem, lift_xor, lift_td, lift_xor5, rot32,
                  u64_ofBitVec_xor, u64_toBitVec_ofBitVec, u64_xor_toBitVec,
                  u32_xor_toBitVec, u32_ofBitVec_toBitVec,
                  Std.Do.SPred.down_pure]
      -- Decompose vector equality element-wise (avoids kernel isDefEq on irreducible terms)
      change (⟨_⟩ : RustArray _ _) = ⟨_⟩
      all_goals (repeat' congr 1)
      -- Close rotation goals: collapse XOR chain back, then apply odd-rotation lemma
      all_goals simp only [← lift_xor5, lift_rot1]
