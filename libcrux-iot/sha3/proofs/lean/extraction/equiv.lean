import extraction.step_equiv
import extraction.round_equiv

open libcrux_iot_sha3.lane
open libcrux_iot_sha3.state

/-! ## Single-round equivalence for rounds 1–3 (composed via Triple.bind) -/

-- Helper: weaken any postcondition to True
open Std.Do in
private theorem weaken_to_true {P : Assertion _} {Q : KeccakState → Prop}
    (m : RustM KeccakState) (h : ⦃P⦄ m ⦃⇓ r => ⌜Q r⌝⦄) :
    ⦃P⦄ m ⦃⇓ r => ⌜True⌝⦄ :=
  Triple.of_entails_right _ _ _ _ h
    (PostCond.entails.of_left_entails fun _ => by
      rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun _ => trivial)

-- Helper: strengthen precondition (Q ⊢ₛ True is trivial)
open Std.Do in
private theorem strengthen_pre {Q : Prop} {R : PostCond KeccakState _}
    (m : RustM KeccakState) (h : ⦃⌜True⌝⦄ m ⦃R⦄) :
    ⦃⌜Q⌝⦄ m ⦃R⦄ :=
  Triple.of_entails_left ⌜True⌝ _ _ _ h (by
    rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun _ => trivial)

-- Helper: vacuous triple when precondition is False
open Std.Do in
private theorem triple_of_false {R : PostCond KeccakState _}
    (m : RustM KeccakState) : ⦃⌜False⌝⦄ m ⦃R⦄ := by
  rw [Triple, ← SPred.entails_true_intro]
  exact SPred.pure_intro fun h => absurd h id

-- Helper: vacuous triple when precondition is ⌜P⌝ and ¬P holds
open Std.Do in
private theorem triple_of_neg {P : Prop} (hneg : ¬P) {R : PostCond KeccakState _}
    (m : RustM KeccakState) : ⦃⌜P⌝⦄ m ⦃R⦄ := by
  have : P = False := propext ⟨fun h => absurd h hneg, False.elim⟩
  rw [Triple, this, ← SPred.entails_true_intro]
  exact SPred.pure_intro fun h => absurd h id

open Std.Do in
private theorem roundK_equiv
    {theta prc1 prc2 : KeccakState → RustM KeccakState}
    (theta_spec : ∀ s, ⦃⌜True⌝⦄ theta s ⦃⇓ r => ⌜r.i = s.i⌝⦄)
    (prc1_spec : ∀ s, s.i.toNat < 24 → ⦃⌜True⌝⦄ prc1 s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄)
    (prc2_spec : ∀ s, ⦃⌜True⌝⦄ prc2 s ⦃⇓ r => ⌜r.i = s.i⌝⦄)
    (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃⌜True⌝⦄
    do let s ← theta s; let s ← prc1 s; prc2 s
    ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄ := by
  apply Triple.bind (Q := fun s₁ => ⌜s₁.i = s.i⌝)
  · exact theta_spec s
  · intro s₁
    by_cases hs₁ : s₁.i = s.i
    · have hi₁ : s₁.i.toNat < 24 := hs₁ ▸ hi
      apply Triple.bind (Q := fun s₂ => ⌜s₂.i = s.i + 1⌝)
      · exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (prc1_spec s₁ hi₁)
          (PostCond.entails.of_left_entails fun _ => by
            rw [← SPred.entails_true_intro]
            exact SPred.pure_intro fun h => by simp_all))
      · intro s₂
        by_cases hs₂ : s₂.i = s.i + 1
        · exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (prc2_spec s₂)
            (PostCond.entails.of_left_entails fun _ => by
              rw [← SPred.entails_true_intro]
              exact SPred.pure_intro fun h => by simp_all))
        · rw [Triple, show (s₂.i = s.i + 1) = False from propext ⟨(absurd · hs₂), False.elim⟩]
          rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => absurd h id
    · rw [Triple, show (s₁.i = s.i) = False from propext ⟨(absurd · hs₁), False.elim⟩]
      rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => absurd h id

/-! ## 4-round block equivalence.

Composes 4 single-round equivalences via Triple.bind.
Each round increments i by 1, so after 4 rounds i has increased by 4.
-/

-- Pre-weakened round0 specs (extract just i-tracking from the full specs)
open Std.Do in
private theorem round0_theta_i (s : KeccakState) :
    ⦃⌜True⌝⦄ libcrux_iot_sha3.keccak.keccakf1600_round0_theta s ⦃⇓ r => ⌜r.i = s.i⌝⦄ :=
  Triple.of_entails_right _ _ _ _ (theta_comp_spec s)
    (PostCond.entails.of_left_entails fun _ => by
      rw [← SPred.entails_true_intro]
      exact SPred.pure_intro fun ⟨_,_,_,_,_,_,_,_,_,_,_,h⟩ => h)

open Std.Do in
private theorem round0_prc1_i (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃⌜True⌝⦄ libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄ :=
  Triple.of_entails_right _ _ _ _ (pi_rho_chi_1_spec s hi)
    (PostCond.entails.of_left_entails fun _ => by
      rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun ⟨h, _⟩ => h)

set_option maxRecDepth 3000 in
open Std.Do in
private theorem round0_prc2_i (s : KeccakState) :
    ⦃⌜True⌝⦄ libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s ⦃⇓ r => ⌜r.i = s.i⌝⦄ :=
  Triple.of_entails_right _ _ _ _ (pi_rho_chi_2_spec s)
    (PostCond.entails.of_left_entails fun _ => by
      rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun ⟨_, h⟩ => h)

-- Helper: convert usize-preserving spec to Nat-level postcondition.
open Std.Do in
private theorem nat_step_preserve
    {f : KeccakState → RustM KeccakState}
    (spec : ∀ s, ⦃⌜True⌝⦄ f s ⦃⇓ r => ⌜r.i = s.i⌝⦄)
    (s : KeccakState) (n : Nat) :
    ⦃⌜s.i.toNat = n⌝⦄ f s ⦃⇓ r => ⌜r.i.toNat = n⌝⦄ := by
  by_cases hs : s.i.toNat = n
  · exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (spec s)
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]
        exact SPred.pure_intro fun h => by simp_all))
  · exact triple_of_neg hs _

-- Helper: convert usize-incrementing spec to Nat-level postcondition.
open Std.Do in
private theorem nat_step_increment
    {f : KeccakState → RustM KeccakState}
    (spec : ∀ s, s.i.toNat < 24 → ⦃⌜True⌝⦄ f s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄)
    (s : KeccakState) (n : Nat) (hn : n < 24) :
    ⦃⌜s.i.toNat = n⌝⦄ f s ⦃⇓ r => ⌜r.i.toNat = n + 1⌝⦄ := by
  by_cases hs : s.i.toNat = n
  · exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (spec s (hs ▸ hn))
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]
        exact SPred.pure_intro fun h => by omega))
  · exact triple_of_neg hs _

set_option maxRecDepth 2000 in
open Std.Do in
theorem four_rounds_equiv (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s
    ⦃ ⇓ r => ⌜ r.i.toNat = s.i.toNat + 4 ⌝ ⦄ := by
  -- Track s.i.toNat through 12 steps as Nat (avoids usize arithmetic issues).
  -- theta/prc2 preserve (nat_step_preserve), prc1 increments (nat_step_increment).
  unfold libcrux_iot_sha3.keccak.keccakf1600_4rounds
  -- Step 1: theta0 (preserves i)
  apply Triple.bind (Q := fun s₁ => ⌜s₁.i.toNat = s.i.toNat⌝)
  · exact Triple.of_entails_right _ _ _ _ (round0_theta_i s)
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => by simp_all)
  · intro s₁
    -- Step 2: prc1_0 (increments to n0 + 1)
    apply Triple.bind (Q := fun s₂ => ⌜s₂.i.toNat = s.i.toNat + 1⌝)
    · exact nat_step_increment (fun s hi => round0_prc1_i s hi) s₁ s.i.toNat (by omega)
    · intro s₂
      -- Step 3: prc2_0 (preserves n0 + 1)
      apply Triple.bind (Q := fun s₃ => ⌜s₃.i.toNat = s.i.toNat + 1⌝)
      · exact nat_step_preserve round0_prc2_i s₂ (s.i.toNat + 1)
      · intro s₃
        -- Step 4: theta1 (preserves n0 + 1)
        apply Triple.bind (Q := fun s₄ => ⌜s₄.i.toNat = s.i.toNat + 1⌝)
        · exact nat_step_preserve round1_theta_spec s₃ (s.i.toNat + 1)
        · intro s₄
          -- Step 5: prc1_1 (increments to n0 + 2)
          apply Triple.bind (Q := fun s₅ => ⌜s₅.i.toNat = s.i.toNat + 2⌝)
          · exact nat_step_increment (fun s hi => round1_prc1_spec s hi) s₄ (s.i.toNat + 1) (by omega)
          · intro s₅
            -- Step 6: prc2_1 (preserves n0 + 2)
            apply Triple.bind (Q := fun s₆ => ⌜s₆.i.toNat = s.i.toNat + 2⌝)
            · exact nat_step_preserve round1_prc2_spec s₅ (s.i.toNat + 2)
            · intro s₆
              -- Step 7: theta2 (preserves n0 + 2)
              apply Triple.bind (Q := fun s₇ => ⌜s₇.i.toNat = s.i.toNat + 2⌝)
              · exact nat_step_preserve round2_theta_spec s₆ (s.i.toNat + 2)
              · intro s₇
                -- Step 8: prc1_2 (increments to n0 + 3)
                apply Triple.bind (Q := fun s₈ => ⌜s₈.i.toNat = s.i.toNat + 3⌝)
                · exact nat_step_increment (fun s hi => round2_prc1_spec s hi) s₇ (s.i.toNat + 2) (by omega)
                · intro s₈
                  -- Step 9: prc2_2 (preserves n0 + 3)
                  apply Triple.bind (Q := fun s₉ => ⌜s₉.i.toNat = s.i.toNat + 3⌝)
                  · exact nat_step_preserve round2_prc2_spec s₈ (s.i.toNat + 3)
                  · intro s₉
                    -- Step 10: theta3 (preserves n0 + 3)
                    apply Triple.bind (Q := fun s₁₀ => ⌜s₁₀.i.toNat = s.i.toNat + 3⌝)
                    · exact nat_step_preserve round3_theta_spec s₉ (s.i.toNat + 3)
                    · intro s₁₀
                      -- Step 11: prc1_3 (increments to s.i.toNat + 4)
                      apply Triple.bind (Q := fun s₁₁ => ⌜s₁₁.i.toNat = s.i.toNat + 4⌝)
                      · exact nat_step_increment (fun s hi => round3_prc1_spec s hi) s₁₀ (s.i.toNat + 3) (by omega)
                      · intro s₁₁
                        -- Step 12: prc2_3 (preserves s.i.toNat + 4) + pure
                        apply Triple.bind (Q := fun s₁₂ => ⌜s₁₂.i.toNat = s.i.toNat + 4⌝)
                        · exact nat_step_preserve round3_prc2_spec s₁₁ (s.i.toNat + 4)
                        · intro s₁₂
                          -- pure just returns s₁₂
                          by_cases hs₁₂ : s₁₂.i.toNat = s.i.toNat + 4
                          · exact strengthen_pre _ (Triple.pure s₁₂ (by
                              rw [← SPred.entails_true_intro]
                              exact SPred.pure_intro fun _ => hs₁₂))
                          · exact triple_of_neg hs₁₂ _
/-! ## Main equivalence theorem. STATUS: sorry.

The full keccak is 6 repetitions of the 4-round block = 24 spec rounds.
Since each 4-round block returns the state to standard layout (impl_perm^4 = id),
the composition is straightforward.

TODO: Compose 6 × four_rounds_equiv. Since impl_perm^24 = id (24-cycle on
non-fixed points, and impl_perm^4 = id on each 4-cycle), the final lift
has no permutation adjustment.
-/

-- The implementation does not panic (totality): keccakf1600 always returns Except.ok.
-- This follows from composing 6 × four_rounds_equiv via the fold_range loop.
-- The initial state has i = 0 (from KeccakState.default or the caller), so i + 4 ≤ 24
-- holds at each iteration since four_rounds_equiv increments i by 4 each time.
-- Helper: one iteration of the fold body succeeds and tracks i
open Std.Do in
private theorem fold_body_spec (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s
    ⦃ ⇓ r => ⌜ r.i.toNat = s.i.toNat + 4 ⌝ ⦄ :=
  four_rounds_equiv s hi

-- keccakf1600 calls fold_range which invokes keccakf1600_4rounds 6 times.
-- The fold uses the @[spec] annotations on keccakf1600_4rounds and keccakf1600
-- to generate verification conditions via hax_mvcgen.
-- We use four_rounds_equiv to close the per-iteration VC.
-- Helper: one 4-round block as a Nat-level step (increments i by 4)
open Std.Do in
private theorem nat_4round_step (s : KeccakState) (n : Nat) (hn : n + 4 ≤ 24) :
    ⦃⌜s.i.toNat = n⌝⦄
    libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s
    ⦃⇓ r => ⌜r.i.toNat = n + 4⌝⦄ := by
  by_cases hs : s.i.toNat = n
  · have hi' : s.i.toNat + 4 ≤ 24 := by omega
    exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (four_rounds_equiv s hi')
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => by simp_all))
  · exact triple_of_neg hs _

set_option maxRecDepth 2000 in
set_option maxHeartbeats 8000000 in
open Std.Do in
theorem keccakf1600_succeeds (s : KeccakState) (hi : s.i.toNat = 0) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600 s
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  unfold libcrux_iot_sha3.keccak.keccakf1600
  simp only [rust_primitives.hax.folds.fold_range]
  -- Structure: (fold_range 0 6 ... s ...) >>= fun s => pure {s with i := 0}
  -- First split off the trailing pure
  apply Triple.bind (Q := fun _ => ⌜True⌝)
  · -- The fold: 6 iterations of keccakf1600_4rounds.
    -- Unroll one step at a time: unfold exposes 4rounds >>= fold_rest
    -- Block 1 (i: 0 → 4)
    unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
    apply Triple.bind (Q := fun s₁ => ⌜s₁.i.toNat = 4⌝)
    · exact Triple.of_entails_right _ _ _ _ (four_rounds_equiv s (by omega))
        (PostCond.entails.of_left_entails fun _ => by
          rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => by simp_all)
    · intro s₁
      -- Block 2 (i: 4 → 8)
      unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
      apply Triple.bind (Q := fun s₂ => ⌜s₂.i.toNat = 8⌝)
      · exact nat_4round_step s₁ 4 (by omega)
      · intro s₂
        -- Block 3 (i: 8 → 12)
        unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
        apply Triple.bind (Q := fun s₃ => ⌜s₃.i.toNat = 12⌝)
        · exact nat_4round_step s₂ 8 (by omega)
        · intro s₃
          -- Block 4 (i: 12 → 16)
          unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
          apply Triple.bind (Q := fun s₄ => ⌜s₄.i.toNat = 16⌝)
          · exact nat_4round_step s₃ 12 (by omega)
          · intro s₄
            -- Block 5 (i: 16 → 20)
            unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
            apply Triple.bind (Q := fun s₅ => ⌜s₅.i.toNat = 20⌝)
            · exact nat_4round_step s₄ 16 (by omega)
            · intro s₅
              -- Block 6 (i: 20 → 24) + base case (fold_range 6 6 = pure)
              unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
              apply Triple.bind (Q := fun _ => ⌜True⌝)
              · exact Triple.of_entails_right _ _ _ _
                  (nat_4round_step s₅ 20 (by omega))
                  (PostCond.entails.of_left_entails fun _ => by
                    rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun _ => trivial)
              · intro s₆
                unfold Int32.fold_range; simp (config := {decide := true}) only [ite_false]
                exact strengthen_pre _ (Triple.pure s₆ (SPred.entails.refl _))
  · intro s₇; exact Triple.pure _ (SPred.entails.refl _)

/-! ## Per-round functional equivalence

The core mathematical result: running one spec round on the lifted state equals
running one impl round and then lifting with the permutation.

Proven by hax_mvcgen on both spec and impl simultaneously — it generates VCs
that connect the u32 (impl) and u64 (spec) operations, closed by the algebraic
lifting lemmas (lift_lane_bv_{xor,and,not,or}, chi_lane_lift, etc.).
-/

-- One spec round: θ → ρ → π → χ → ι
def spec_round (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let s ← hacspec_sha3.keccak_f.theta state
  let s ← hacspec_sha3.keccak_f.rho s
  let s ← hacspec_sha3.keccak_f.pi s
  let s ← hacspec_sha3.keccak_f.chi s
  hacspec_sha3.keccak_f.iota s round

-- Impl round 0: theta → pi_rho_chi_1 → pi_rho_chi_2
def impl_round0 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s

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

-- Reusable tactic for round-level equivalence proofs
macro "round_equiv_proof" : tactic =>
  `(tactic| (
    hax_mvcgen [hacspec_sha3.keccak_f.get, hacspec_sha3.createi,
                core_models.array.from_fn, core_models.num.Impl_9.rotate_left,
                core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
                libcrux_secrets.traits.Classify.classify, spec_round, impl_round0, lift, lift_lane,
                lift_lane_bv, spread_to_even, impl_perm, lift_perm]
    all_goals (first | intro h₁; subst h₁ | skip)
    all_goals simp (config := { decide := true, maxSteps := 400000 }) [getElemResult, core_models.ops.index.Index.index]
    all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set]; try rfl) | skip)
    all_goals (reduce_usize_sizes; simp (config := { decide := true, maxSteps := 400000 }) [Vector.getElem_set]; try rfl)
    all_goals (repeat' constructor)
    all_goals (first | rfl | skip)
    all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set, rot32,
      lift_lane_bv_xor, lift_lane_bv_and, lift_lane_bv_not, lift_lane_bv_or,
      chi_lane_lift, theta_apply_lift, theta_d_lift, theta_c_lift]; try rfl) | skip)
    all_goals (first | omega | simp_all | rfl | skip)
    all_goals (
      delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
      have h255 : USize64.toNat s.i < 255 := by omega
      rw [dif_pos h255, dif_pos h255]
      have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
        simp [BitVec.uaddOverflow]; omega
      rw [if_neg huadd]
      delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
      first | rfl | simp_all)))

-- Bridge lemmas: primed defs from round_equiv.lean = unprimed defs here
private theorem bridge_lift (s : KeccakState) : lift' s = lift s := by
  unfold lift' lift lift_lane' lift_lane lift_lane_bv' lift_lane_bv spread_to_even' spread_to_even; rfl
private theorem bridge_lift_perm (s : KeccakState) (p : Fin 25 → Fin 25) : lift_perm' s p = lift_perm s p := by
  unfold lift_perm' lift_perm lift_lane' lift_lane lift_lane_bv' lift_lane_bv spread_to_even' spread_to_even; rfl
private theorem bridge_spec_round (st : RustArray u64 25) (r : usize) : spec_round' st r = spec_round st r := by
  unfold spec_round' spec_round; rfl
private theorem bridge_impl_round0 (s : KeccakState) : impl_round0' s = impl_round0 s := by
  unfold impl_round0' impl_round0; rfl
private theorem bridge_impl_round1 (s : KeccakState) : impl_round1' s = impl_round1 s := by
  unfold impl_round1' impl_round1; rfl
private theorem bridge_impl_round2 (s : KeccakState) : impl_round2' s = impl_round2 s := by
  unfold impl_round2' impl_round2; rfl
private theorem bridge_impl_round3 (s : KeccakState) : impl_round3' s = impl_round3 s := by
  unfold impl_round3' impl_round3; rfl
private theorem bridge_impl_perm : impl_perm' = impl_perm := by
  unfold impl_perm' impl_perm; rfl
private theorem bridge_impl_perm2 : impl_perm2' = impl_perm2 := by
  unfold impl_perm2' impl_perm2 impl_perm' impl_perm; rfl
private theorem bridge_impl_perm3 : impl_perm3' = impl_perm3 := by
  unfold impl_perm3' impl_perm3 impl_perm' impl_perm; rfl

-- Round func_equivs derived from round_equiv.lean via bridge lemmas
open Std.Do in
theorem round0_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round0 s
       let r_spec ← spec_round (lift s) s.i
       pure (r_spec = lift_perm r_impl impl_perm)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  simp only [← bridge_impl_round0, ← bridge_spec_round, ← bridge_lift,
    ← bridge_lift_perm, ← bridge_impl_perm]
  exact round0_func_equiv' s hi

open Std.Do in
theorem round1_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round1 s
       let r_spec ← spec_round (lift_perm s impl_perm) s.i
       pure (r_spec = lift_perm r_impl impl_perm2)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  simp only [← bridge_impl_round1, ← bridge_spec_round, ← bridge_lift_perm,
    ← bridge_impl_perm, ← bridge_impl_perm2]
  exact round1_func_equiv' s hi

/-! ## Top-level equivalence

The proof chains 6 applications of four_round_eq, rewriting each spec_4rounds
block into lift(4rounds_result). After all 6 blocks, LHS = RHS = pure (lift r₆).
-/

-- 4 consecutive spec rounds
def spec_4rounds (state : RustArray u64 25) (start_round : usize) : RustM (RustArray u64 25) := do
  let s ← spec_round state start_round
  let s ← spec_round s (start_round + 1)
  let s ← spec_round s (start_round + 2)
  spec_round s (start_round + 3)

-- keccak_f = 6 × spec_4rounds (fold unrolling)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem keccak_f_unfold (state : RustArray u64 25) :
    hacspec_sha3.keccak_f.keccak_f state =
    (do let s ← spec_4rounds state 0; let s ← spec_4rounds s 4
        let s ← spec_4rounds s 8; let s ← spec_4rounds s 12
        let s ← spec_4rounds s 16; spec_4rounds s 20) := by
  unfold hacspec_sha3.keccak_f.keccak_f
  simp only [rust_primitives.hax.folds.fold_range]
  -- Unroll USize64.fold_range (24 iterations)
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_false]
  -- Both sides are now 24 flat spec rounds. Unfold RHS and normalize usize arithmetic.
  simp (config := {decide := true}) only [spec_4rounds, spec_round, bind_assoc, pure_bind]
  rfl

open Std.Do in
theorem round2_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round2 s
       let r_spec ← spec_round (lift_perm s impl_perm2) s.i
       pure (r_spec = lift_perm r_impl impl_perm3)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  simp only [← bridge_impl_round2, ← bridge_spec_round, ← bridge_lift_perm,
    ← bridge_impl_perm2, ← bridge_impl_perm3]
  exact round2_func_equiv' s hi

open Std.Do in
theorem round3_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round3 s
       let r_spec ← spec_round (lift_perm s impl_perm3) s.i
       pure (r_spec = lift r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  simp only [← bridge_impl_round3, ← bridge_spec_round, ← bridge_lift_perm,
    ← bridge_impl_perm3, ← bridge_lift]
  exact round3_func_equiv' s hi

-- Pre-computed permutation compositions (placed AFTER roundK_func_equiv to
-- avoid polluting hax_mvcgen's simp context for those proofs)
def impl_perm2 (i : Fin 25) : Fin 25 := impl_perm (impl_perm i)
def impl_perm3 (i : Fin 25) : Fin 25 := impl_perm (impl_perm (impl_perm i))

-- Convert per-round Hoare triple to direct RustM equality
open Std.Do in
private theorem round_eq_of_func_equiv
    (m_impl : RustM KeccakState) (m_spec : RustM (RustArray u64 25))
    (f : KeccakState → RustArray u64 25)
    (h : ⦃⌜True⌝⦄ (do let a ← m_impl; let b ← m_spec; (pure (b = f a) : RustM Prop)) ⦃⇓ r => ⌜r⌝⦄) :
    m_spec = (m_impl >>= fun r => pure (f r)) := by
  match m_impl, m_spec with
  | .ok v₁, .ok v₂ =>
    show RustM.ok v₂ = RustM.ok (f v₁); congr 1
    rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Except.pure, Id.run, pure]
  | .ok _, .fail e =>
    exfalso; rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Id.run, pure, throwThe, throw, ExceptT.mk]
  | .ok _, .div =>
    exfalso; rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, PredTrans.const]
  | .fail e, _ =>
    exfalso; rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Id.run, pure, throwThe, throw, ExceptT.mk]
  | .div, _ =>
    exfalso; rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, PredTrans.const]

-- Per-round direct equalities (derived from func_equiv Hoare triples)
theorem round0_eq (s : KeccakState) (hi : s.i.toNat < 24) :
    spec_round (lift s) s.i = (impl_round0 s >>= fun r => pure (lift_perm r impl_perm)) :=
  round_eq_of_func_equiv _ _ _ (round0_func_equiv s hi)

theorem round1_eq (s : KeccakState) (hi : s.i.toNat < 24) :
    spec_round (lift_perm s impl_perm) s.i = (impl_round1 s >>= fun r => pure (lift_perm r impl_perm2)) :=
  round_eq_of_func_equiv _ _ _ (round1_func_equiv s hi)

theorem round2_eq (s : KeccakState) (hi : s.i.toNat < 24) :
    spec_round (lift_perm s impl_perm2) s.i = (impl_round2 s >>= fun r => pure (lift_perm r impl_perm3)) :=
  round_eq_of_func_equiv _ _ _ (round2_func_equiv s hi)

theorem round3_eq (s : KeccakState) (hi : s.i.toNat < 24) :
    spec_round (lift_perm s impl_perm3) s.i = (impl_round3 s >>= fun r => pure (lift r)) :=
  round_eq_of_func_equiv _ _ _ (round3_func_equiv s hi)

-- 4-round functional equivalence: compose 4 per-round equalities
-- keccakf1600_4rounds = impl_round0 >> impl_round1 >> impl_round2 >> impl_round3
-- spec_4rounds = spec_round >> spec_round >> spec_round >> spec_round
-- four_round_eq: extraction approach (no congr/funext, no sorry)
-- We need per-round ok extraction (same pattern as four_rounds_ok)
-- Each impl_roundK returns ok with i incremented by 1
open Std.Do in
private theorem impl_round_ok (f : KeccakState → RustM KeccakState)
    (spec : ∀ s, s.i.toNat < 24 → ⦃⌜True⌝⦄ f s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄)
    (s : KeccakState) (hi : s.i.toNat < 24) :
    ∃ r, f s = .ok r ∧ r.i.toNat = s.i.toNat + 1 := by
  have h := spec s hi
  match hm : f s with
  | .ok r =>
    refine ⟨r, rfl, ?_⟩
    rw [Triple] at h
    simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Except.pure, Id.run, pure, USize64.toNat_add]
    omega
  | .fail e =>
    exfalso; rw [Triple] at h
    simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Id.run, pure, throwThe, throw, ExceptT.mk]
  | .div =>
    exfalso; rw [Triple] at h
    simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, PredTrans.const]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem four_round_eq (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    spec_4rounds (lift s) s.i =
    (libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s >>= fun r => pure (lift r)) := by
  unfold spec_4rounds libcrux_iot_sha3.keccak.keccakf1600_4rounds
  simp only [bind_assoc]
  have ok_bind : ∀ {α β : Type} (a : α) (f : α → RustM β), RustM.ok a >>= f = f a := fun _ _ => rfl
  -- i-tracking specs for each impl round (instantiate roundK_equiv)
  have round0_i := roundK_equiv (fun s => theta_comp_spec s |>.of_entails_right _
    (PostCond.entails.of_left_entails fun _ => by rw [← SPred.entails_true_intro]
     exact SPred.pure_intro fun ⟨_,_,_,_,_,_,_,_,_,_,_,h⟩ => h))
    (fun s hi => pi_rho_chi_1_spec s hi |>.of_entails_right _
      (PostCond.entails.of_left_entails fun _ => by rw [← SPred.entails_true_intro]
       exact SPred.pure_intro fun ⟨h, _⟩ => h))
    (fun s => pi_rho_chi_2_spec s |>.of_entails_right _
      (PostCond.entails.of_left_entails fun _ => by rw [← SPred.entails_true_intro]
       exact SPred.pure_intro fun ⟨_, h⟩ => h))
  have round1_i := roundK_equiv round1_theta_spec (fun s hi => round1_prc1_spec s hi) round1_prc2_spec
  have round2_i := roundK_equiv round2_theta_spec (fun s hi => round2_prc1_spec s hi) round2_prc2_spec
  have round3_i := roundK_equiv round3_theta_spec (fun s hi => round3_prc1_spec s hi) round3_prc2_spec
  -- Extract concrete impl results with i-tracking
  obtain ⟨r₁, hr₁, hi₁⟩ := impl_round_ok _ (fun s hi => round0_i s hi) s (by omega)
  obtain ⟨r₂, hr₂, hi₂⟩ := impl_round_ok _ (fun s hi => round1_i s hi) r₁ (by omega)
  obtain ⟨r₃, hr₃, hi₃⟩ := impl_round_ok _ (fun s hi => round2_i s hi) r₂ (by omega)
  obtain ⟨r₄, hr₄, _⟩ := impl_round_ok _ (fun s hi => round3_i s hi) r₃ (by omega)
  -- Substitute impl results on RHS
  simp only [hr₁, ok_bind, hr₂, hr₃, hr₄, pure_bind]
  -- Rewrite each spec round using roundK_eq
  rw [round0_eq s (by omega)]; simp only [hr₁, ok_bind, pure_bind]
  rw [round1_eq r₁ (by omega)]; simp only [hr₂, ok_bind, pure_bind]
  rw [round2_eq r₂ (by omega)]; simp only [hr₃, ok_bind, pure_bind]
  rw [round3_eq r₃ (by omega)]; simp only [hr₄, ok_bind]

-- 4-round block returns ok and increments i by 4
-- Derived from four_rounds_equiv by case-splitting on the RustM result
open Std.Do in
theorem four_rounds_ok (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    ∃ r, libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s = .ok r ∧ r.i.toNat = s.i.toNat + 4 := by
  have h := four_rounds_equiv s hi
  match hm : libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s with
  | .ok r =>
    refine ⟨r, rfl, ?_⟩
    rw [Triple] at h; simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept,
      PredTrans.pure, PredTrans.trans, ExceptT.run, Except.pure, Id.run, pure]
  | .fail e =>
    exfalso; rw [Triple] at h; simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept,
      PredTrans.pure, PredTrans.trans, ExceptT.run, Id.run, pure, throwThe, throw, ExceptT.mk]
  | .div =>
    exfalso; rw [Triple] at h; simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept,
      PredTrans.pure, PredTrans.trans, PredTrans.const]

-- lift ignores the i field
theorem lift_reset_i (s : KeccakState) (v : usize) : lift { s with i := v } = lift s := by
  unfold lift lift_lane lift_lane_bv spread_to_even; rfl

-- Helper: usize equality from toNat equality
private theorem usize_eq (a b : usize) (ha : a.toNat = b.toNat) : a = b :=
  USize64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq ha)

-- Full equivalence
set_option maxRecDepth 2000 in
set_option maxHeartbeats 8000000 in
theorem equivalence (s : KeccakState) (hi : s.i.toNat = 0) :
    hacspec_sha3.keccak_f.keccak_f (lift s) =
    (libcrux_iot_sha3.keccak.keccakf1600 s >>= fun r => pure (lift r)) := by
  -- Unfold impl fold into 6 × keccakf1600_4rounds
  unfold libcrux_iot_sha3.keccak.keccakf1600
  simp only [rust_primitives.hax.folds.fold_range]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_false]
  -- Rewrite spec as 6 × spec_4rounds
  rw [keccak_f_unfold]
  -- Extract impl block results
  obtain ⟨r₁, hr₁, hi₁⟩ := four_rounds_ok s (by omega)
  obtain ⟨r₂, hr₂, hi₂⟩ := four_rounds_ok r₁ (by omega)
  obtain ⟨r₃, hr₃, hi₃⟩ := four_rounds_ok r₂ (by omega)
  obtain ⟨r₄, hr₄, hi₄⟩ := four_rounds_ok r₃ (by omega)
  obtain ⟨r₅, hr₅, hi₅⟩ := four_rounds_ok r₄ (by omega)
  obtain ⟨r₆, hr₆, hi₆⟩ := four_rounds_ok r₅ (by omega)
  -- Substitute all impl results on RHS and reduce binds
  -- RustM.ok = pure, so pure_bind applies
  have ok_bind : ∀ {α β : Type} (a : α) (f : α → RustM β), RustM.ok a >>= f = f a := fun _ _ => rfl
  simp only [hr₁, ok_bind, hr₂, hr₃, hr₄, hr₅, hr₆, pure_bind, lift_reset_i]
  -- Rewrite each spec_4rounds block using four_round_eq
  -- Need: spec_4rounds (lift rₖ) rₖ.i = pure (lift rₖ₊₁)  [from four_round_eq + hrₖ₊₁]
  -- Bridge: numeric literal n = rₖ.i  [via usize_eq]
  -- Block 1: spec_4rounds (lift s) 0 → pure (lift r₁)
  rw [show (0 : usize) = s.i from (usize_eq _ _ hi).symm,
      four_round_eq s (by omega), hr₁, ok_bind]
  -- Blocks 2-6: need pure_bind to reduce `pure (lift rₖ) >>= spec_4rounds`
  -- then usize_eq to match the round number with rₖ.i
  simp only [pure_bind]
  -- Compute rₖ.i values as Nat, then convert to usize equality
  have h1 : r₁.i.toNat = 4 := by omega
  have h2 : r₂.i.toNat = 8 := by omega
  have h3 : r₃.i.toNat = 12 := by omega
  have h4 : r₄.i.toNat = 16 := by omega
  have h5 : r₅.i.toNat = 20 := by omega
  -- Block 2
  rw [show (4 : usize) = r₁.i from (usize_eq _ _ (by rw [h1]; native_decide)).symm,
      four_round_eq r₁ (by omega), hr₂, ok_bind, pure_bind]
  -- Block 3
  rw [show (8 : usize) = r₂.i from (usize_eq _ _ (by rw [h2]; native_decide)).symm,
      four_round_eq r₂ (by omega), hr₃, ok_bind, pure_bind]
  -- Block 4
  rw [show (12 : usize) = r₃.i from (usize_eq _ _ (by rw [h3]; native_decide)).symm,
      four_round_eq r₃ (by omega), hr₄, ok_bind, pure_bind]
  -- Block 5
  rw [show (16 : usize) = r₄.i from (usize_eq _ _ (by rw [h4]; native_decide)).symm,
      four_round_eq r₄ (by omega), hr₅, ok_bind, pure_bind]
  -- Block 6
  rw [show (20 : usize) = r₅.i from (usize_eq _ _ (by rw [h5]; native_decide)).symm,
      four_round_eq r₅ (by omega), hr₆, ok_bind]
