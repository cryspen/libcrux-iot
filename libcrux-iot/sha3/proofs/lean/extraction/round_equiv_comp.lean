import extraction.prc_lift
import extraction.spec_decomp

/-! ## Compositional round equivalence

Replaces the monolithic round_equiv.lean (4 × 400M heartbeats = 1.6B total).
Each round proof decomposes spec_round into spec_theta_unrolled >> spec_prc_unrolled,
then runs hax_mvcgen on the combined impl with spec terms kept opaque during WP.

The only remaining sorry's are in spec_decomp.lean:
- spec_theta_unrolled_eq: spec_theta = spec_theta_unrolled (Vector.mapM unrolling)
- spec_prc_unrolled_eq: spec_prc = spec_prc_unrolled (Vector.mapM unrolling)
These are purely algebraic facts about the hacspec spec, independent of the implementation.
-/

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

section RoundEquiv
attribute [local irreducible] spread_to_even lift_lane_bv

def impl_round0 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s

def spec_round (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let s ← hacspec_sha3.keccak_f.theta state
  let s ← hacspec_sha3.keccak_f.rho s
  let s ← hacspec_sha3.keccak_f.pi s
  let s ← hacspec_sha3.keccak_f.chi s
  hacspec_sha3.keccak_f.iota s round

-- Round 0 functional equivalence (80M heartbeats, ~2min wall-clock)
-- Proof: spec_round decomposed to unrolled theta+prc, then hax_mvcgen on combined impl+spec
-- with lift terms opaque during WP, lifting lemmas applied post-mvcgen.
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 5000 in
open Std.Do in
theorem round0_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round0 s
       let r_spec ← spec_round (lift s) s.i
       pure (r_spec = lift_perm r_impl impl_perm)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  unfold impl_round0 spec_round
  rw [spec_round_decomp, spec_theta_unrolled_eq, spec_prc_unrolled_eq]
  simp only [bind_assoc]
  conv in spec_theta_unrolled _ >>= _ => unfold spec_theta_unrolled; simp only [pure_bind]
  unfold spec_prc_unrolled
  hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
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
  all_goals (first | (simp only [lift_theta_applied, lta, lift_perm, lift_getElem,
    lift_xor, lift_and, lift_not, lift_chi, lift_theta_apply, lift_theta_d,
    rot32', rot_0, rot_1, rot_2, rot_3, rot_6, rot_8, rot_10, rot_14, rot_15, rot_18, rot_20, rot_21,
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
    first | rfl | simp_all)

end RoundEquiv
