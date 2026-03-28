import keccak_verification.equivalence_proofs.prc_lift
import keccak_verification.equivalence_proofs.spec_decomp

/-! ## Compositional round equivalence (round 0)

Proves that one full Keccak round (theta + rho + pi + chi + iota) on the bit-interleaved
implementation produces the same result as the standard u64 spec, after lifting.

### Proof strategy

1. Decompose `spec_round` into `spec_theta_unrolled >> spec_prc_unrolled` using
   `spec_round_decomp` + the unrolled equivalences from spec_decomp.lean.
2. Reduce `spec_theta_unrolled` to pure (all let-bindings are non-monadic).
3. Run `hax_mvcgen` on the combined impl (theta + prc1 + prc2) with spec terms
   kept opaque during WP computation.
4. Close residual goals with the same algebraic lifting lemmas as theta_lift + prc_lift.

### Performance

This replaces the monolithic `round_equiv.lean` which used 400M heartbeats per round
(1.6B total for 4 rounds). The compositional approach uses 40M heartbeats.

### Sorry dependencies

The only sorry's used are from `spec_decomp.lean`:
- `spec_theta_unrolled_eq`: spec_theta = spec_theta_unrolled (Vector.mapM unrolling)
- `spec_prc_unrolled_eq`: spec_prc = spec_prc_unrolled (Vector.mapM unrolling)

These are purely algebraic facts about the hacspec reference specification and are
independent of the implementation correctness.
-/

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

section RoundEquiv
attribute [local irreducible] spread_to_even lift_lane_bv

/-- Round 0 implementation: theta then prc1 then prc2. -/
def impl_round0 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s

/-- Round specification: theta, rho, pi, chi, iota (from hacspec). -/
def spec_round (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let s ← hacspec_sha3.keccak_f.theta state
  let s ← hacspec_sha3.keccak_f.rho s
  let s ← hacspec_sha3.keccak_f.pi s
  let s ← hacspec_sha3.keccak_f.chi s
  hacspec_sha3.keccak_f.iota s round

/-- Round 0 functional equivalence: the lifted implementation output equals the spec output.

    Specifically: running `impl_round0 s` and `spec_round (lift s) s.i` produces the
    same 25-lane array (modulo the impl's lane permutation).

    This is the compositional replacement for `round0_func_equiv'` in round_equiv.lean,
    reducing cost from 400M to 40M heartbeats. -/
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 5000 in
open Std.Do in
theorem round0_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round0 s
       let r_spec ← spec_round (lift s) s.i
       pure (r_spec = lift_perm r_impl impl_perm)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  unfold impl_round0 spec_round; round_equiv_proof

-- Rounds 1-3: structurally identical to round 0, just different function names
-- from hax's loop unrolling. Same proof pattern applies.

def impl_round1 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round1_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_2 s

def impl_round2 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round2_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_2 s

def impl_round3 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round3_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_2 s

def impl_perm2 (i : Fin 25) : Fin 25 := impl_perm (impl_perm i)
def impl_perm3 (i : Fin 25) : Fin 25 := impl_perm (impl_perm (impl_perm i))

-- Shared tactic for all 4 round proofs. Each round is identical modulo function names.
-- The tactic: decompose spec, mvcgen on impl only, algebraic bridge with lifting lemmas.
local macro "round_equiv_proof" : tactic =>
  `(tactic| (
    rw [spec_round_decomp, spec_theta_unrolled_eq, spec_prc_unrolled_eq]
    simp only [bind_assoc]
    conv in spec_theta_unrolled _ >>= _ =>
      unfold spec_theta_unrolled theta_result theta_d_val theta_col; simp only [pure_bind]
    unfold spec_prc_unrolled iota_lane chi_lane pi_lane rho_lane
    hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_keccak_verification,
                libcrux_secrets.traits.Classify.classify]
    all_goals (first | intro h₁; subst h₁ | skip)
    all_goals simp (config := { decide := true, maxSteps := 200000 }) only [getElemResult, core_models.ops.index.Index.index,
      ↓reduceDIte, USize64.reduceToNat, USize64.add_zero, USize64.toNat_zero, ↓reduceIte,
      USize64.toBitVec_ofNat, bind_pure_comp, pure_bind, USize64.reduceAdd, map_pure,
      Vector.size, Nat.zero_lt_succ, bind_pure, Std.Do.WP.pure, Vector.getElem_set,
      Std.Do.SPred.down_pure, rot32,
      show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl,
      show (2 : usize).toNat = 2 from rfl, show (255 : usize).toNat = 255 from rfl]
    all_goals (repeat' constructor)
    all_goals (first | subst_vars; rfl | rfl | skip)
    all_goals (first | (simp only [lift_theta_applied, lta, lift_perm, lift, lift_lane, lift_getElem,
      lift_xor, lift_and, lift_not, lift_chi, lift_theta_apply, lift_theta_d,
      rot32', impl_perm, impl_perm2, impl_perm3,
      rot_0, rot_1, rot_2, rot_3, rot_6, rot_8, rot_10, rot_14, rot_15, rot_18, rot_20, rot_21,
      rot_25, rot_27, rot_28, rot_36, rot_39, rot_41, rot_43, rot_44, rot_45, rot_55, rot_56, rot_61, rot_62,
      u64_ofBitVec_xor, u64_toBitVec_ofBitVec, u64_xor_toBitVec,
      u32_xor_toBitVec, u32_ofBitVec_toBitVec,
      Vector.getElem_set]; rfl) | skip)
    all_goals (first | omega | rfl | skip)
    all_goals (open Std.Do in
      delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
      have h255 : USize64.toNat s.i < 255 := by omega
      rw [dif_pos h255, dif_pos h255]
      have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
        simp [BitVec.uaddOverflow]; omega
      rw [if_neg huadd]
      delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
      first | rfl | simp_all)))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 5000 in
open Std.Do in
theorem round1_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round1 s
       let r_spec ← spec_round (lift_perm s impl_perm) s.i
       pure (r_spec = lift_perm r_impl impl_perm2)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  unfold impl_round1 spec_round; round_equiv_proof

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 5000 in
open Std.Do in
theorem round2_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round2 s
       let r_spec ← spec_round (lift_perm s impl_perm2) s.i
       pure (r_spec = lift_perm r_impl impl_perm3)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  unfold impl_round2 spec_round; round_equiv_proof

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 5000 in
open Std.Do in
theorem round3_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round3 s
       let r_spec ← spec_round (lift_perm s impl_perm3) s.i
       pure (r_spec = lift r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  unfold impl_round3 spec_round; round_equiv_proof

end RoundEquiv
