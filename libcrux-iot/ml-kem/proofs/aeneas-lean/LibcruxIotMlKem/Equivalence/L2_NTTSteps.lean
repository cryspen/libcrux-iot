/-
  # `Equivalence/L2_NTTSteps.lean` — Layer 2 intra-PortableVector NTT step Triples.

  L2.x Triples for the per-PortableVector NTT butterflies in
  `vector/portable/ntt.rs`:

  - **L2.1 `ntt_step_spec`** — single Cooley-Tukey butterfly inside a
    PortableVector at indices `(i, j)` with ζ. Post is bound-only
    (unchanged lanes + 3·3328 → 4·3328 propagation), matching F* upstream
    parity (`Vector.Portable.Ntt.ntt_step`). The modular congruence
    content (`r[i] ≡ a + ζb`, `r[j] ≡ a - ζb` mod 3329) is deferred to
    `BitMlKem.Commute` (Layer M).

  See `Plan.lean:1157-1208` for the sketch and F* port reference.
-/
import LibcruxIotMlKem.Plan
import LibcruxIotMlKem.Extraction.Funs
import LibcruxIotMlKem.Util.PortableVector
import LibcruxIotMlKem.Equivalence.L0_FieldArith

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Equivalence

open Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Util

/-! ## Local helpers — Triple ↔ Result.ok bridges. -/

/-- The Triple `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v`. -/
private theorem triple_of_ok_l2 {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

/-- Extract the `.ok` witness from a true-pre Triple. Used by L2.1 to
    consume L0.4's `@[spec]`. -/
private theorem triple_exists_ok_l2 {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp])

/-! ## L2.1 — `ntt_step_spec`

    The impl is a straight chain of 8 binds:
      1. read `vec[j]`
      2. classify ζ        (identity)
      3. L0.4 montgomery_multiply: `t = mont_mult(vec[j], ζ)`
      4. read `vec[i]`
      5. `a_minus_t = vec[i] - t`   (wrapping_sub)
      6. `a_plus_t  = vec[i] + t`   (wrapping_add)
      7. write `vec[j] := a_minus_t`
      8. write `vec[i] := a_plus_t`

    Under the L0.4 bound (`|t.val| ≤ 3328`), and `|vec[i]|, |vec[j]|
    ≤ 3·3328`, the two sums `vec[i] ± t` satisfy `| · | ≤ 4·3328 =
    13312 < 2^15 = 32768`, so the wrappings are the identity and
    `(vec[i] ± t).val = vec[i].val ± t.val`. -/

/-- Reduction of `core_models.num.I16.wrapping_sub` to the underlying
    Aeneas `Std.I16.wrapping_sub`. -/
private theorem cm_wrapping_sub_ok_eq (x y : Std.I16) :
    core_models.num.I16.wrapping_sub x y = .ok (Std.I16.wrapping_sub x y) := by
  unfold core_models.num.I16.wrapping_sub
  unfold rust_primitives.arithmetic.wrapping_sub_i16
  rfl

/-- Reduction of `core_models.num.I16.wrapping_add` to the underlying
    Aeneas `Std.I16.wrapping_add`. -/
private theorem cm_wrapping_add_ok_eq (x y : Std.I16) :
    core_models.num.I16.wrapping_add x y = .ok (Std.I16.wrapping_add x y) := by
  unfold core_models.num.I16.wrapping_add
  unfold rust_primitives.arithmetic.wrapping_add_i16
  rfl

/-- Reduction of `classify` to identity. -/
private theorem classify_ok_eq {T : Type} (x : T) :
    libcrux_secrets.traits.Classify.Blanket.classify x = .ok x := rfl

/-- Under `|a.val| ≤ B·3328`, `|t.val| ≤ 3328`, and `B ≤ 8`, the I16-wrapped
    sum `a + t` has `.val = a.val + t.val` and `.val.natAbs ≤ (B+1)·3328`. -/
private theorem add_no_overflow_value_B (a t : Std.I16) (B : Nat)
    (h_a : a.val.natAbs ≤ B * 3328) (h_t : t.val.natAbs ≤ 3328) (h_B : B ≤ 8) :
    (Std.I16.wrapping_add a t).val = a.val + t.val
      ∧ (Std.I16.wrapping_add a t).val.natAbs ≤ (B + 1) * 3328 := by
  -- |a + t| ≤ |a| + |t| ≤ B·3328 + 3328 = (B+1)·3328 ≤ 9·3328 = 29952 < 2^15 = 32768.
  have h_sum_abs : ((a.val + t.val : Int)).natAbs ≤ (B + 1) * 3328 := by
    have h_tri : (a.val + t.val).natAbs ≤ a.val.natAbs + t.val.natAbs := Int.natAbs_add_le _ _
    omega
  -- No-overflow ⇒ bmod is identity.
  have h_lb : -(2 ^ 15 : Int) ≤ a.val + t.val := by
    have h_natAbs : ((a.val + t.val : Int)).natAbs ≤ (B + 1) * 3328 := h_sum_abs
    have h_bound : (B + 1) * 3328 ≤ 9 * 3328 := by
      have : B + 1 ≤ 9 := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  have h_ub : a.val + t.val < (2 ^ 15 : Int) := by
    have h_natAbs : ((a.val + t.val : Int)).natAbs ≤ (B + 1) * 3328 := h_sum_abs
    have h_bound : (B + 1) * 3328 ≤ 9 * 3328 := by
      have : B + 1 ≤ 9 := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  have h_bmod : Int.bmod (a.val + t.val) (2 ^ 16) = a.val + t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_add_val_eq a t
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact h_sum_abs

/-- Under `|a.val| ≤ B·3328`, `|t.val| ≤ 3328`, and `B ≤ 8`, the I16-wrapped
    diff `a - t` has `.val = a.val - t.val` and `.val.natAbs ≤ (B+1)·3328`. -/
private theorem sub_no_overflow_value_B (a t : Std.I16) (B : Nat)
    (h_a : a.val.natAbs ≤ B * 3328) (h_t : t.val.natAbs ≤ 3328) (h_B : B ≤ 8) :
    (Std.I16.wrapping_sub a t).val = a.val - t.val
      ∧ (Std.I16.wrapping_sub a t).val.natAbs ≤ (B + 1) * 3328 := by
  have h_diff_abs : ((a.val - t.val : Int)).natAbs ≤ (B + 1) * 3328 := by
    have h_neg_natAbs : (-t.val).natAbs = t.val.natAbs := Int.natAbs_neg _
    have h_eq : a.val - t.val = a.val + (-t.val) := by ring
    rw [h_eq]
    have h_tri : (a.val + (-t.val)).natAbs ≤ a.val.natAbs + (-t.val).natAbs :=
      Int.natAbs_add_le _ _
    rw [h_neg_natAbs] at h_tri
    omega
  have h_lb : -(2 ^ 15 : Int) ≤ a.val - t.val := by
    have h_natAbs : ((a.val - t.val : Int)).natAbs ≤ (B + 1) * 3328 := h_diff_abs
    have h_bound : (B + 1) * 3328 ≤ 9 * 3328 := by
      have : B + 1 ≤ 9 := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  have h_ub : a.val - t.val < (2 ^ 15 : Int) := by
    have h_natAbs : ((a.val - t.val : Int)).natAbs ≤ (B + 1) * 3328 := h_diff_abs
    have h_bound : (B + 1) * 3328 ≤ 9 * 3328 := by
      have : B + 1 ≤ 9 := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  have h_bmod : Int.bmod (a.val - t.val) (2 ^ 16) = a.val - t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_sub_val_eq a t
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact h_diff_abs

/-- Specialised form (B = 3) — preserves the original signature for callers. -/
private theorem add_no_overflow_value (a t : Std.I16)
    (h_a : a.val.natAbs ≤ 3 * 3328) (h_t : t.val.natAbs ≤ 3328) :
    (Std.I16.wrapping_add a t).val = a.val + t.val
      ∧ (Std.I16.wrapping_add a t).val.natAbs ≤ 4 * 3328 :=
  add_no_overflow_value_B a t 3 h_a h_t (by decide)

/-- Specialised form (B = 3) — preserves the original signature for callers. -/
private theorem sub_no_overflow_value (a t : Std.I16)
    (h_a : a.val.natAbs ≤ 3 * 3328) (h_t : t.val.natAbs ≤ 3328) :
    (Std.I16.wrapping_sub a t).val = a.val - t.val
      ∧ (Std.I16.wrapping_sub a t).val.natAbs ≤ 4 * 3328 :=
  sub_no_overflow_value_B a t 3 h_a h_t (by decide)

@[spec]
theorem ntt_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (h_i : i.val < 16) (h_j : j.val < 16) (h_ne : i.val ≠ j.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_a : (vec.elements.val[i.val]!).val.natAbs ≤ 3 * 3328)
    (h_b : (vec.elements.val[j.val]!).val.natAbs ≤ 3 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  r.elements.val[k]! = vec.elements.val[k]!)
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ 4 * 3328
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  have h_vec_len : vec.elements.length = 16 := PortableVector_elements_length vec
  -- Step 1: read vec[j].
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    array_index_usize_ok_eq vec.elements j (by rw [h_vec_len]; exact h_j)
  -- Step 2: classify ζ.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    classify_ok_eq zeta
  -- Step 3: L0.4 montgomery_multiply on (vec[j], ζ).
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  obtain ⟨t, h_t_eq_ok, h_t_bd, _h_t_mod⟩ :=
    triple_exists_ok_l2 (montgomery_multiply_fe_by_fer_spec b zeta h_zeta)
  -- Step 4: read vec[i].
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    array_index_usize_ok_eq vec.elements i (by rw [h_vec_len]; exact h_i)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  -- Step 5: wrapping_sub a t.
  have h_sub_eq : core_models.num.I16.wrapping_sub a t = .ok (Std.I16.wrapping_sub a t) :=
    cm_wrapping_sub_ok_eq a t
  -- Step 6: wrapping_add a t.
  have h_add_eq : core_models.num.I16.wrapping_add a t = .ok (Std.I16.wrapping_add a t) :=
    cm_wrapping_add_ok_eq a t
  set a_minus_t : Std.I16 := Std.I16.wrapping_sub a t with hamt_def
  set a_plus_t  : Std.I16 := Std.I16.wrapping_add a t with hapt_def
  -- Step 7: update vec at index j with a_minus_t.
  have h_upd_j :
      Aeneas.Std.Array.update vec.elements j a_minus_t
        = .ok (vec.elements.set j a_minus_t) :=
    array_update_ok_eq vec.elements j a_minus_t (by rw [h_vec_len]; exact h_j)
  -- Step 8: update at index i with a_plus_t.
  have h_upd_i :
      Aeneas.Std.Array.update (vec.elements.set j a_minus_t) i a_plus_t
        = .ok ((vec.elements.set j a_minus_t).set i a_plus_t) := by
    have h_len : (vec.elements.set j a_minus_t).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact array_update_ok_eq _ i a_plus_t (by rw [h_len]; exact h_i)
  -- Compose the whole do-block into one `.ok` equation.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set j a_minus_t).set i a_plus_t with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_step
    rw [h_idx_j]; simp only [bind_tc_ok]
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_t_eq_ok]; simp only [bind_tc_ok]
    rw [h_idx_i]; simp only [bind_tc_ok]
    rw [h_sub_eq]; simp only [bind_tc_ok]
    rw [h_add_eq]; simp only [bind_tc_ok]
    rw [h_upd_j]; simp only [bind_tc_ok]
    rw [h_upd_i]; simp only [bind_tc_ok]; rfl
  -- Bound facts on the two touched lanes.
  have h_add := add_no_overflow_value a t h_a h_t_bd
  have h_sub := sub_no_overflow_value a t h_a h_t_bd
  -- Close the Triple.
  apply triple_of_ok_l2 h_body
  refine ⟨?_, ?_, ?_⟩
  · -- Unchanged lanes: k ≠ i.val and k ≠ j.val.
    intro k hk_lt hk_ne_i hk_ne_j
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[k]!
          = (vec.elements.set j a_minus_t)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i k _ (Ne.symm hk_ne_i)
    have h_set_j_ne :
        (vec.elements.set j a_minus_t)[k]! = (vec.elements)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ j k _ (Ne.symm hk_ne_j)
    show final_vec.elements.val[k]! = vec.elements.val[k]!
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[k]! = vec.elements.val[k]!
    -- Convert .val[k]! ↔ [k]! using getElem!_Nat_eq, then chain set_ne rewrites.
    rw [← Aeneas.Std.Array.getElem!_Nat_eq, ← Aeneas.Std.Array.getElem!_Nat_eq,
        h_set_i_ne, h_set_j_ne]
  · -- Bound on r.elements.val[i.val]!.
    show (final_vec.elements.val[i.val]!).val.natAbs ≤ 4 * 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!).val.natAbs ≤ 4 * 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_set_i_eq :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! = a_plus_t := by
      have h_len : (vec.elements.set j a_minus_t).length = 16 := by
        rw [Std.Array.set_length]; exact h_vec_len
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ i i.val _ ⟨rfl, by rw [h_len]; exact h_i⟩
    rw [h_eq1, h_set_i_eq]
    exact h_add.2
  · -- Bound on r.elements.val[j.val]!.
    show (final_vec.elements.val[j.val]!).val.natAbs ≤ 4 * 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!).val.natAbs ≤ 4 * 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_ne_ij : i.val ≠ j.val := h_ne
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]!
          = (vec.elements.set j a_minus_t)[j.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i j.val _ h_ne_ij
    have h_set_j_eq :
        (vec.elements.set j a_minus_t)[j.val]! = a_minus_t := by
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ j j.val _ ⟨rfl, by rw [h_vec_len]; exact h_j⟩
    have h_eq2 :
        (vec.elements.set j a_minus_t)[j.val]!
          = (vec.elements.set j a_minus_t).val[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    rw [h_eq1, h_set_i_ne, h_set_j_eq]
    exact h_sub.2

/-! ## Parameterised L2.1 — `ntt_step_spec_B`

    Same shape as `ntt_step_spec` but with a configurable lane bound `B ≤ 8`.
    Each touched lane goes from `≤ B·3328` to `≤ (B+1)·3328`. Used by the
    L2.2/L2.3/L2.4 bundled-butterfly proofs which need different inbound
    bounds (7·3328 / 6·3328 / 5·3328 respectively).

    The proof body is identical to `ntt_step_spec` except that
    `add_no_overflow_value` / `sub_no_overflow_value` are replaced by their
    `_B` counterparts.

    `h_B : B ≤ 8` ensures no I16 overflow: `(B+1)·3328 ≤ 9·3328 = 29952 < 2^15`.
-/

@[spec]
theorem ntt_step_spec_B
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize) (B : Nat)
    (h_i : i.val < 16) (h_j : j.val < 16) (h_ne : i.val ≠ j.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_a : (vec.elements.val[i.val]!).val.natAbs ≤ B * 3328)
    (h_b : (vec.elements.val[j.val]!).val.natAbs ≤ B * 3328)
    (h_B : B ≤ 8) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  r.elements.val[k]! = vec.elements.val[k]!)
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ (B + 1) * 3328
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ (B + 1) * 3328 ⌝ ⦄ := by
  have h_vec_len : vec.elements.length = 16 := PortableVector_elements_length vec
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    array_index_usize_ok_eq vec.elements j (by rw [h_vec_len]; exact h_j)
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    classify_ok_eq zeta
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  obtain ⟨t, h_t_eq_ok, h_t_bd, _h_t_mod⟩ :=
    triple_exists_ok_l2 (montgomery_multiply_fe_by_fer_spec b zeta h_zeta)
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    array_index_usize_ok_eq vec.elements i (by rw [h_vec_len]; exact h_i)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  have h_sub_eq : core_models.num.I16.wrapping_sub a t = .ok (Std.I16.wrapping_sub a t) :=
    cm_wrapping_sub_ok_eq a t
  have h_add_eq : core_models.num.I16.wrapping_add a t = .ok (Std.I16.wrapping_add a t) :=
    cm_wrapping_add_ok_eq a t
  set a_minus_t : Std.I16 := Std.I16.wrapping_sub a t with hamt_def
  set a_plus_t  : Std.I16 := Std.I16.wrapping_add a t with hapt_def
  have h_upd_j :
      Aeneas.Std.Array.update vec.elements j a_minus_t
        = .ok (vec.elements.set j a_minus_t) :=
    array_update_ok_eq vec.elements j a_minus_t (by rw [h_vec_len]; exact h_j)
  have h_upd_i :
      Aeneas.Std.Array.update (vec.elements.set j a_minus_t) i a_plus_t
        = .ok ((vec.elements.set j a_minus_t).set i a_plus_t) := by
    have h_len : (vec.elements.set j a_minus_t).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact array_update_ok_eq _ i a_plus_t (by rw [h_len]; exact h_i)
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set j a_minus_t).set i a_plus_t with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_step
    rw [h_idx_j]; simp only [bind_tc_ok]
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_t_eq_ok]; simp only [bind_tc_ok]
    rw [h_idx_i]; simp only [bind_tc_ok]
    rw [h_sub_eq]; simp only [bind_tc_ok]
    rw [h_add_eq]; simp only [bind_tc_ok]
    rw [h_upd_j]; simp only [bind_tc_ok]
    rw [h_upd_i]; simp only [bind_tc_ok]; rfl
  have h_add := add_no_overflow_value_B a t B h_a h_t_bd h_B
  have h_sub := sub_no_overflow_value_B a t B h_a h_t_bd h_B
  apply triple_of_ok_l2 h_body
  refine ⟨?_, ?_, ?_⟩
  · intro k hk_lt hk_ne_i hk_ne_j
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[k]!
          = (vec.elements.set j a_minus_t)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i k _ (Ne.symm hk_ne_i)
    have h_set_j_ne :
        (vec.elements.set j a_minus_t)[k]! = (vec.elements)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ j k _ (Ne.symm hk_ne_j)
    show final_vec.elements.val[k]! = vec.elements.val[k]!
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[k]! = vec.elements.val[k]!
    rw [← Aeneas.Std.Array.getElem!_Nat_eq, ← Aeneas.Std.Array.getElem!_Nat_eq,
        h_set_i_ne, h_set_j_ne]
  · show (final_vec.elements.val[i.val]!).val.natAbs ≤ (B + 1) * 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!).val.natAbs ≤ (B + 1) * 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_set_i_eq :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! = a_plus_t := by
      have h_len : (vec.elements.set j a_minus_t).length = 16 := by
        rw [Std.Array.set_length]; exact h_vec_len
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ i i.val _ ⟨rfl, by rw [h_len]; exact h_i⟩
    rw [h_eq1, h_set_i_eq]
    exact h_add.2
  · show (final_vec.elements.val[j.val]!).val.natAbs ≤ (B + 1) * 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!).val.natAbs ≤ (B + 1) * 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_ne_ij : i.val ≠ j.val := h_ne
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]!
          = (vec.elements.set j a_minus_t)[j.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i j.val _ h_ne_ij
    have h_set_j_eq :
        (vec.elements.set j a_minus_t)[j.val]! = a_minus_t := by
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ j j.val _ ⟨rfl, by rw [h_vec_len]; exact h_j⟩
    have h_eq2 :
        (vec.elements.set j a_minus_t)[j.val]!
          = (vec.elements.set j a_minus_t).val[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    rw [h_eq1, h_set_i_ne, h_set_j_eq]
    exact h_sub.2

/-! ## L2.2 — `ntt_layer_1_step_spec`

    Eight disjoint butterflies on pairs `(0,2)ζ0`, `(1,3)ζ0`, `(4,6)ζ1`,
    `(5,7)ζ1`, `(8,10)ζ2`, `(9,11)ζ2`, `(12,14)ζ3`, `(13,15)ζ3`. Each call
    of `ntt_step_spec_B` with `B = 7` raises the two touched lanes from
    `≤ 7·3328` to `≤ 8·3328`; pairs are pairwise disjoint and cover all
    16 lanes, so every lane is touched exactly once.

    Bookkeeping idiom: we maintain, after the k-th call, the invariant
    "for every lane index ℓ ∈ [0,16), if ℓ is among the lanes touched
    so far, lane_k[ℓ] ≤ 8·3328; else lane_k[ℓ] = vec[ℓ] (and so
    ≤ 7·3328 ≤ 8·3328)". The post conjuncts of `ntt_step_spec_B`
    immediately give us each step's contribution.
-/

@[spec]
theorem ntt_layer_1_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hz2 : zeta2.val.natAbs ≤ 1664) (hz3 : zeta3.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 7 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 8 * 3328 ⌝ ⦄ := by
  -- Index abbreviations.
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  -- Initial bounds: hpre gives ≤ 7·3328 on all lanes.
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 7 * 3328 := hpre
  -- Step 1: (0, 2) ζ0. Pair untouched ⇒ both lanes ≤ 7·3328 from hpre.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B vec zeta0 0#usize 2#usize 7
      h0lt h2lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 2 h2lt) (by decide))
  -- After step 1: lane 0 and lane 2 are ≤ 8·3328 (h_v1_i, h_v1_j); other lanes
  -- unchanged from vec (h_v1_unc), so still ≤ 7·3328 from hpre.
  -- Step 2: (1, 3) ζ0. Disjoint from {0, 2}, so lanes 1, 3 are still vec[1], vec[3] ≤ 7·3328.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_3 : (v1.elements.val[3]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v1_unc 3 h3lt (by decide) (by decide)]; exact hb_init 3 h3lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v1 zeta0 1#usize 3#usize 7
      h1lt h3lt (by decide) hz0 h_v1_1 h_v1_3 (by decide))
  -- Step 3: (4, 6) ζ1. v2[4], v2[6] not touched in steps 1,2 ⇒ = vec[4], vec[6] ≤ 7·3328.
  have h_v2_4 : (v2.elements.val[4]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v2_unc 4 h4lt (by decide) (by decide), h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v2 zeta1 4#usize 6#usize 7
      h4lt h6lt (by decide) hz1 h_v2_4 h_v2_6 (by decide))
  -- Step 4: (5, 7) ζ1.
  have h_v3_5 : (v3.elements.val[5]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v3 zeta1 5#usize 7#usize 7
      h5lt h7lt (by decide) hz1 h_v3_5 h_v3_7 (by decide))
  -- Step 5: (8, 10) ζ2.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_10 : (v4.elements.val[10]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v4 zeta2 8#usize 10#usize 7
      h8lt h10lt (by decide) hz2 h_v4_8 h_v4_10 (by decide))
  -- Step 6: (9, 11) ζ2.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_11 : (v5.elements.val[11]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v5 zeta2 9#usize 11#usize 7
      h9lt h11lt (by decide) hz2 h_v5_9 h_v5_11 (by decide))
  -- Step 7: (12, 14) ζ3.
  have h_v6_12 : (v6.elements.val[12]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v6_unc 12 h12lt (by decide) (by decide),
        h_v5_unc 12 h12lt (by decide) (by decide),
        h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v6 zeta3 12#usize 14#usize 7
      h12lt h14lt (by decide) hz3 h_v6_12 h_v6_14 (by decide))
  -- Step 8: (13, 15) ζ3.
  have h_v7_13 : (v7.elements.val[13]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v7_unc 13 h13lt (by decide) (by decide),
        h_v6_unc 13 h13lt (by decide) (by decide),
        h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v7 zeta3 13#usize 15#usize 7
      h13lt h15lt (by decide) hz3 h_v7_13 h_v7_15 (by decide))
  -- Compose the whole 8-step chain into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  -- Close the Triple: prove every lane ≤ 8·3328 by case-split on which step touched it.
  -- Strategy: for each lane ℓ, identify the step that touched it (giving h_v{k}_i or h_v{k}_j
  -- with bound ≤ 8·3328), then propagate v_k[ℓ] = ... = v8[ℓ] via the later steps' h_v{m}_unc.
  apply triple_of_ok_l2 h_body
  intro i hi
  interval_cases i
  -- Lane 0: touched in step 1 as i-lane ⇒ v1[0] ≤ 8·3328. v8[0] = v1[0].
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_i
  -- Lane 1: touched in step 2 as i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_i
  -- Lane 2: touched in step 1 as j-lane.
  · have h_eq : v8.elements.val[2]! = v1.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide),
          h_v3_unc 2 h2lt (by decide) (by decide),
          h_v2_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_j
  -- Lane 3: touched in step 2 as j-lane.
  · have h_eq : v8.elements.val[3]! = v2.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide),
          h_v4_unc 3 h3lt (by decide) (by decide),
          h_v3_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_j
  -- Lane 4: touched in step 3 as i-lane.
  · have h_eq : v8.elements.val[4]! = v3.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_i
  -- Lane 5: touched in step 4 as i-lane.
  · have h_eq : v8.elements.val[5]! = v4.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_i
  -- Lane 6: touched in step 3 as j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_j
  -- Lane 7: touched in step 4 as j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_j
  -- Lane 8: touched in step 5 as i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_i
  -- Lane 9: touched in step 6 as i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_i
  -- Lane 10: touched in step 5 as j-lane.
  · have h_eq : v8.elements.val[10]! = v5.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_j
  -- Lane 11: touched in step 6 as j-lane.
  · have h_eq : v8.elements.val[11]! = v6.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_j
  -- Lane 12: touched in step 7 as i-lane.
  · have h_eq : v8.elements.val[12]! = v7.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_i
  -- Lane 13: touched in step 8 as i-lane.
  · exact h_v8_i
  -- Lane 14: touched in step 7 as j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_j
  -- Lane 15: touched in step 8 as j-lane.
  · exact h_v8_j

/-! ## L2.3 — `ntt_layer_2_step_spec`

    Eight disjoint butterflies on pairs `(0,4)ζ0`, `(1,5)ζ0`, `(2,6)ζ0`,
    `(3,7)ζ0`, `(8,12)ζ1`, `(9,13)ζ1`, `(10,14)ζ1`, `(11,15)ζ1`. Same
    bookkeeping pattern as L2.2 but with `B = 6`.
-/

@[spec]
theorem ntt_layer_2_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 : Std.I16)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 6 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec zeta0 zeta1
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 7 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 6 * 3328 := hpre
  -- Step 1: (0, 4) ζ0.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B vec zeta0 0#usize 4#usize 6
      h0lt h4lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 4 h4lt) (by decide))
  -- Step 2: (1, 5) ζ0.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_5 : (v1.elements.val[5]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v1_unc 5 h5lt (by decide) (by decide)]; exact hb_init 5 h5lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v1 zeta0 1#usize 5#usize 6
      h1lt h5lt (by decide) hz0 h_v1_1 h_v1_5 (by decide))
  -- Step 3: (2, 6) ζ0.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v2 zeta0 2#usize 6#usize 6
      h2lt h6lt (by decide) hz0 h_v2_2 h_v2_6 (by decide))
  -- Step 4: (3, 7) ζ0.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v3 zeta0 3#usize 7#usize 6
      h3lt h7lt (by decide) hz0 h_v3_3 h_v3_7 (by decide))
  -- Step 5: (8, 12) ζ1.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v4 zeta1 8#usize 12#usize 6
      h8lt h12lt (by decide) hz1 h_v4_8 h_v4_12 (by decide))
  -- Step 6: (9, 13) ζ1.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v5 zeta1 9#usize 13#usize 6
      h9lt h13lt (by decide) hz1 h_v5_9 h_v5_13 (by decide))
  -- Step 7: (10, 14) ζ1.
  have h_v6_10 : (v6.elements.val[10]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v6_unc 10 h10lt (by decide) (by decide),
        h_v5_unc 10 h10lt (by decide) (by decide),
        h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v6 zeta1 10#usize 14#usize 6
      h10lt h14lt (by decide) hz1 h_v6_10 h_v6_14 (by decide))
  -- Step 8: (11, 15) ζ1.
  have h_v7_11 : (v7.elements.val[11]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v7_unc 11 h11lt (by decide) (by decide),
        h_v6_unc 11 h11lt (by decide) (by decide),
        h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v7 zeta1 11#usize 15#usize 6
      h11lt h15lt (by decide) hz1 h_v7_11 h_v7_15 (by decide))
  -- Compose into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec zeta0 zeta1
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  -- Close: per-lane case split.
  apply triple_of_ok_l2 h_body
  intro i hi
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_i
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_i
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_i
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_i
  -- Lane 4: step 1 j-lane.
  · have h_eq : v8.elements.val[4]! = v1.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide),
          h_v3_unc 4 h4lt (by decide) (by decide),
          h_v2_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_j
  -- Lane 5: step 2 j-lane.
  · have h_eq : v8.elements.val[5]! = v2.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide),
          h_v4_unc 5 h5lt (by decide) (by decide),
          h_v3_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_j
  -- Lane 6: step 3 j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_j
  -- Lane 7: step 4 j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_j
  -- Lane 8: step 5 i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_i
  -- Lane 9: step 6 i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_i
  -- Lane 10: step 7 i-lane.
  · have h_eq : v8.elements.val[10]! = v7.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_i
  -- Lane 11: step 8 i-lane.
  · exact h_v8_i
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_j
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_j
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_j
  -- Lane 15: step 8 j-lane.
  · exact h_v8_j

/-! ## L2.4 — `ntt_layer_3_step_spec`

    Eight disjoint butterflies on pairs `(0,8)`, `(1,9)`, `(2,10)`, `(3,11)`,
    `(4,12)`, `(5,13)`, `(6,14)`, `(7,15)` — all with the single ζ. Same
    bookkeeping pattern as L2.2/L2.3 but with `B = 5`.
-/

@[spec]
theorem ntt_layer_3_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (hz : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 5 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec zeta
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 6 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 5 * 3328 := hpre
  -- Step 1: (0, 8).
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B vec zeta 0#usize 8#usize 5
      h0lt h8lt (by decide) hz (hb_init 0 h0lt) (hb_init 8 h8lt) (by decide))
  -- Step 2: (1, 9).
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_9 : (v1.elements.val[9]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v1_unc 9 h9lt (by decide) (by decide)]; exact hb_init 9 h9lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v1 zeta 1#usize 9#usize 5
      h1lt h9lt (by decide) hz h_v1_1 h_v1_9 (by decide))
  -- Step 3: (2, 10).
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_10 : (v2.elements.val[10]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v2_unc 10 h10lt (by decide) (by decide), h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v2 zeta 2#usize 10#usize 5
      h2lt h10lt (by decide) hz h_v2_2 h_v2_10 (by decide))
  -- Step 4: (3, 11).
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_11 : (v3.elements.val[11]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v3 zeta 3#usize 11#usize 5
      h3lt h11lt (by decide) hz h_v3_3 h_v3_11 (by decide))
  -- Step 5: (4, 12).
  have h_v4_4 : (v4.elements.val[4]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v4_unc 4 h4lt (by decide) (by decide),
        h_v3_unc 4 h4lt (by decide) (by decide),
        h_v2_unc 4 h4lt (by decide) (by decide),
        h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v4 zeta 4#usize 12#usize 5
      h4lt h12lt (by decide) hz h_v4_4 h_v4_12 (by decide))
  -- Step 6: (5, 13).
  have h_v5_5 : (v5.elements.val[5]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v5_unc 5 h5lt (by decide) (by decide),
        h_v4_unc 5 h5lt (by decide) (by decide),
        h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v5 zeta 5#usize 13#usize 5
      h5lt h13lt (by decide) hz h_v5_5 h_v5_13 (by decide))
  -- Step 7: (6, 14).
  have h_v6_6 : (v6.elements.val[6]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v6_unc 6 h6lt (by decide) (by decide),
        h_v5_unc 6 h6lt (by decide) (by decide),
        h_v4_unc 6 h6lt (by decide) (by decide),
        h_v3_unc 6 h6lt (by decide) (by decide),
        h_v2_unc 6 h6lt (by decide) (by decide),
        h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v6 zeta 6#usize 14#usize 5
      h6lt h14lt (by decide) hz h_v6_6 h_v6_14 (by decide))
  -- Step 8: (7, 15).
  have h_v7_7 : (v7.elements.val[7]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v7_unc 7 h7lt (by decide) (by decide),
        h_v6_unc 7 h7lt (by decide) (by decide),
        h_v5_unc 7 h7lt (by decide) (by decide),
        h_v4_unc 7 h7lt (by decide) (by decide),
        h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v7 zeta 7#usize 15#usize 5
      h7lt h15lt (by decide) hz h_v7_7 h_v7_15 (by decide))
  -- Compose into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec zeta = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  -- Close: per-lane case split.
  apply triple_of_ok_l2 h_body
  intro i hi
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_i
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_i
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_i
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_i
  -- Lane 4: step 5 i-lane.
  · have h_eq : v8.elements.val[4]! = v5.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_i
  -- Lane 5: step 6 i-lane.
  · have h_eq : v8.elements.val[5]! = v6.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_i
  -- Lane 6: step 7 i-lane.
  · have h_eq : v8.elements.val[6]! = v7.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_i
  -- Lane 7: step 8 i-lane.
  · exact h_v8_i
  -- Lane 8: step 1 j-lane.
  · have h_eq : v8.elements.val[8]! = v1.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide),
          h_v5_unc 8 h8lt (by decide) (by decide),
          h_v4_unc 8 h8lt (by decide) (by decide),
          h_v3_unc 8 h8lt (by decide) (by decide),
          h_v2_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_j
  -- Lane 9: step 2 j-lane.
  · have h_eq : v8.elements.val[9]! = v2.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide),
          h_v6_unc 9 h9lt (by decide) (by decide),
          h_v5_unc 9 h9lt (by decide) (by decide),
          h_v4_unc 9 h9lt (by decide) (by decide),
          h_v3_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_j
  -- Lane 10: step 3 j-lane.
  · have h_eq : v8.elements.val[10]! = v3.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide),
          h_v5_unc 10 h10lt (by decide) (by decide),
          h_v4_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_j
  -- Lane 11: step 4 j-lane.
  · have h_eq : v8.elements.val[11]! = v4.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide),
          h_v6_unc 11 h11lt (by decide) (by decide),
          h_v5_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_j
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_j
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_j
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_j
  -- Lane 15: step 8 j-lane.
  · exact h_v8_j

/-! ## L2.5 — `inv_ntt_step_spec` (Gentleman–Sande inverse butterfly)

    The impl is a straight chain of 9 binds:
      1. read `vec[j]`             (= `i1`)
      2. read `vec[i]`             (= `i2`)
      3. `a_minus_b = vec[j] - vec[i]`   (wrapping_sub i1 i2)
      4. `a_plus_b  = vec[j] + vec[i]`   (wrapping_add i1 i2)
      5. `o0 = barrett_reduce_element a_plus_b`        (L0.2)
      6. classify ζ                  (identity)
      7. `o1 = montgomery_multiply_fe_by_fer a_minus_b ζ`  (L0.4)
      8. write `vec[i] := o0`        (barrett-reduced sum)
      9. write `vec[j] := o1`        (mont-mul diff by ζ)

    With pre `|vec[i]|, |vec[j]| ≤ B·3328` and `B ≤ 4`:
      `|a_plus_b|, |a_minus_b| ≤ 2·B·3328 ≤ 8·3328 = 26624 ≤ 28296` (L0.2 pre).
      L0.2 post: `|o0| ≤ 3328`.
      L0.4 post: `|o1| ≤ 3328`.
    So both touched lanes end ≤ 3328 (tight). Coarsenings (≤ 2·3328, ≤ 4·3328)
    are derived at the layer level.

    The shape of the parameterized post mirrors `ntt_step_spec_B`: explicit
    unchanged-lane equality + two tight bounds on the touched lanes.
-/

/-- Tight parameterized inverse butterfly Triple. `B` is the input lane bound;
    output bound on touched lanes is the tight `3328`. -/
@[spec]
theorem inv_ntt_step_spec_B
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize) (B : Nat)
    (h_i : i.val < 16) (h_j : j.val < 16) (h_ne : i.val ≠ j.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_a : (vec.elements.val[i.val]!).val.natAbs ≤ B * 3328)
    (h_b : (vec.elements.val[j.val]!).val.natAbs ≤ B * 3328)
    (h_B : B ≤ 4) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  r.elements.val[k]! = vec.elements.val[k]!)
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ 3328
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ 3328 ⌝ ⦄ := by
  have h_vec_len : vec.elements.length = 16 := PortableVector_elements_length vec
  -- Step 1: read vec[j] (= i1 in impl).
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    array_index_usize_ok_eq vec.elements j (by rw [h_vec_len]; exact h_j)
  -- Step 2: read vec[i] (= i2 in impl).
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    array_index_usize_ok_eq vec.elements i (by rw [h_vec_len]; exact h_i)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  -- Step 3: wrapping_sub b a (= a_minus_b).
  have h_sub_eq : core_models.num.I16.wrapping_sub b a = .ok (Std.I16.wrapping_sub b a) :=
    cm_wrapping_sub_ok_eq b a
  -- Step 4: wrapping_add b a (= a_plus_b).
  have h_add_eq : core_models.num.I16.wrapping_add b a = .ok (Std.I16.wrapping_add b a) :=
    cm_wrapping_add_ok_eq b a
  set a_minus_b : Std.I16 := Std.I16.wrapping_sub b a with hamb_def
  set a_plus_b  : Std.I16 := Std.I16.wrapping_add b a with hapb_def
  -- Direct no-overflow proof for b ± a with |b|, |a| ≤ B·3328, B ≤ 4.
  -- (`add_no_overflow_value_B` requires |t| ≤ 3328 on the second arg; we have
  --  the stronger |a| ≤ B·3328, so we re-derive in this generality.)
  have h_add_eq_val : (Std.I16.wrapping_add b a).val = b.val + a.val
      ∧ (Std.I16.wrapping_add b a).val.natAbs ≤ 2 * B * 3328 := by
    have h_sum_abs : ((b.val + a.val : Int)).natAbs ≤ 2 * B * 3328 := by
      have h_tri : (b.val + a.val).natAbs ≤ b.val.natAbs + a.val.natAbs :=
        Int.natAbs_add_le _ _
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val + a.val := by
      have h_bound : 2 * B * 3328 ≤ 8 * 3328 := by
        have : 2 * B ≤ 8 := by omega
        exact Nat.mul_le_mul_right _ this
      omega
    have h_ub : b.val + a.val < (2 ^ 15 : Int) := by
      have h_bound : 2 * B * 3328 ≤ 8 * 3328 := by
        have : 2 * B ≤ 8 := by omega
        exact Nat.mul_le_mul_right _ this
      omega
    have h_bmod : Int.bmod (b.val + a.val) (2 ^ 16) = b.val + a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_add_val_eq b a
    exact ⟨by rw [h_val, h_bmod], by rw [h_val, h_bmod]; exact h_sum_abs⟩
  have h_sub_eq_val : (Std.I16.wrapping_sub b a).val = b.val - a.val
      ∧ (Std.I16.wrapping_sub b a).val.natAbs ≤ 2 * B * 3328 := by
    have h_diff_abs : ((b.val - a.val : Int)).natAbs ≤ 2 * B * 3328 := by
      have h_neg_natAbs : (-a.val).natAbs = a.val.natAbs := Int.natAbs_neg _
      have h_eq : b.val - a.val = b.val + (-a.val) := by ring
      rw [h_eq]
      have h_tri : (b.val + (-a.val)).natAbs ≤ b.val.natAbs + (-a.val).natAbs :=
        Int.natAbs_add_le _ _
      rw [h_neg_natAbs] at h_tri
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val - a.val := by
      have h_bound : 2 * B * 3328 ≤ 8 * 3328 := by
        have : 2 * B ≤ 8 := by omega
        exact Nat.mul_le_mul_right _ this
      omega
    have h_ub : b.val - a.val < (2 ^ 15 : Int) := by
      have h_bound : 2 * B * 3328 ≤ 8 * 3328 := by
        have : 2 * B ≤ 8 := by omega
        exact Nat.mul_le_mul_right _ this
      omega
    have h_bmod : Int.bmod (b.val - a.val) (2 ^ 16) = b.val - a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_sub_val_eq b a
    exact ⟨by rw [h_val, h_bmod], by rw [h_val, h_bmod]; exact h_diff_abs⟩
  -- Bound on a_plus_b for L0.2: 2·B·3328 ≤ 8·3328 = 26624 ≤ 28296.
  have h_apb_bd : a_plus_b.val.natAbs ≤ 28296 := by
    rw [hapb_def]
    have h_step : 2 * B * 3328 ≤ 8 * 3328 := by
      have : 2 * B ≤ 8 := by omega
      exact Nat.mul_le_mul_right _ this
    have h := h_add_eq_val.2
    omega
  -- Step 5: L0.2 barrett_reduce_element on a_plus_b.
  obtain ⟨o0, h_o0_eq_ok, _h_o0_mod, h_o0_bd⟩ :=
    triple_exists_ok_l2 (barrett_reduce_element_spec a_plus_b h_apb_bd)
  -- Step 6: classify ζ.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    classify_ok_eq zeta
  -- Step 7: L0.4 montgomery_multiply on (a_minus_b, ζ).
  obtain ⟨o1, h_o1_eq_ok, h_o1_bd, _h_o1_mod⟩ :=
    triple_exists_ok_l2 (montgomery_multiply_fe_by_fer_spec a_minus_b zeta h_zeta)
  -- Step 8: update vec at index i with o0.
  have h_upd_i :
      Aeneas.Std.Array.update vec.elements i o0
        = .ok (vec.elements.set i o0) :=
    array_update_ok_eq vec.elements i o0 (by rw [h_vec_len]; exact h_i)
  -- Step 9: update at index j with o1.
  have h_upd_j :
      Aeneas.Std.Array.update (vec.elements.set i o0) j o1
        = .ok ((vec.elements.set i o0).set j o1) := by
    have h_len : (vec.elements.set i o0).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact array_update_ok_eq _ j o1 (by rw [h_len]; exact h_j)
  -- Compose into one `.ok` equation.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set i o0).set j o1 with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step
    rw [h_idx_j]; simp only [bind_tc_ok]
    rw [h_idx_i]; simp only [bind_tc_ok]
    rw [h_sub_eq]; simp only [bind_tc_ok]
    rw [h_add_eq]; simp only [bind_tc_ok]
    rw [h_o0_eq_ok]; simp only [bind_tc_ok]
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_o1_eq_ok]; simp only [bind_tc_ok]
    rw [h_upd_i]; simp only [bind_tc_ok]
    rw [h_upd_j]; simp only [bind_tc_ok]; rfl
  -- Close the Triple.
  apply triple_of_ok_l2 h_body
  refine ⟨?_, ?_, ?_⟩
  · -- Unchanged lanes: k ≠ i.val and k ≠ j.val.
    intro k hk_lt hk_ne_i hk_ne_j
    have h_set_j_ne :
        ((vec.elements.set i o0).set j o1)[k]!
          = (vec.elements.set i o0)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ j k _ (Ne.symm hk_ne_j)
    have h_set_i_ne :
        (vec.elements.set i o0)[k]! = (vec.elements)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i k _ (Ne.symm hk_ne_i)
    show final_vec.elements.val[k]! = vec.elements.val[k]!
    show ((vec.elements.set i o0).set j o1).val[k]! = vec.elements.val[k]!
    rw [← Aeneas.Std.Array.getElem!_Nat_eq, ← Aeneas.Std.Array.getElem!_Nat_eq,
        h_set_j_ne, h_set_i_ne]
  · -- Bound on r.elements.val[i.val]!. Lane i gets o0 (barrett-reduced sum).
    show (final_vec.elements.val[i.val]!).val.natAbs ≤ 3328
    show (((vec.elements.set i o0).set j o1).val[i.val]!).val.natAbs ≤ 3328
    have h_eq1 :
        ((vec.elements.set i o0).set j o1).val[i.val]!
          = ((vec.elements.set i o0).set j o1)[i.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_ne_ji : j.val ≠ i.val := (Ne.symm h_ne)
    have h_set_j_ne :
        ((vec.elements.set i o0).set j o1)[i.val]!
          = (vec.elements.set i o0)[i.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ j i.val _ h_ne_ji
    have h_set_i_eq :
        (vec.elements.set i o0)[i.val]! = o0 :=
      Aeneas.Std.Array.getElem!_Nat_set_eq _ i i.val _ ⟨rfl, by rw [h_vec_len]; exact h_i⟩
    rw [h_eq1, h_set_j_ne, h_set_i_eq]
    exact h_o0_bd
  · -- Bound on r.elements.val[j.val]!. Lane j gets o1 (mont-mul diff).
    show (final_vec.elements.val[j.val]!).val.natAbs ≤ 3328
    show (((vec.elements.set i o0).set j o1).val[j.val]!).val.natAbs ≤ 3328
    have h_eq1 :
        ((vec.elements.set i o0).set j o1).val[j.val]!
          = ((vec.elements.set i o0).set j o1)[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_set_j_eq :
        ((vec.elements.set i o0).set j o1)[j.val]! = o1 := by
      have h_len : (vec.elements.set i o0).length = 16 := by
        rw [Std.Array.set_length]; exact h_vec_len
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ j j.val _ ⟨rfl, by rw [h_len]; exact h_j⟩
    rw [h_eq1, h_set_j_eq]
    exact h_o1_bd

/-- Named (B = 4) form matching the brief: `≤ 4·3328 → ≤ 4·3328` on all lanes. -/
@[spec]
theorem inv_ntt_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (h_i : i.val < 16) (h_j : j.val < 16) (h_ne : i.val ≠ j.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ k : Nat, k < 16 → (vec.elements.val[k]!).val.natAbs ≤ 4 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ ∀ k : Nat, k < 16 → (r.elements.val[k]!).val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  obtain ⟨r, h_eq, h_unc, h_i_bd, h_j_bd⟩ :=
    triple_exists_ok_l2
      (inv_ntt_step_spec_B vec zeta i j 4 h_i h_j h_ne h_zeta (hpre i.val h_i)
        (hpre j.val h_j) (by decide))
  apply triple_of_ok_l2 h_eq
  intro k hk
  by_cases h_ki : k = i.val
  · subst h_ki
    have h_3328_le : (3328 : Nat) ≤ 4 * 3328 := by decide
    exact le_trans h_i_bd h_3328_le
  · by_cases h_kj : k = j.val
    · subst h_kj
      have h_3328_le : (3328 : Nat) ≤ 4 * 3328 := by decide
      exact le_trans h_j_bd h_3328_le
    · rw [h_unc k hk h_ki h_kj]
      exact hpre k hk

/-! ## L2.6 — `inv_ntt_layer_1_step_spec`

    Eight disjoint inverse butterflies on pairs `(0,2)ζ0`, `(1,3)ζ0`, `(4,6)ζ1`,
    `(5,7)ζ1`, `(8,10)ζ2`, `(9,11)ζ2`, `(12,14)ζ3`, `(13,15)ζ3`. Input lanes
    `≤ 3328` (B=1); each touched lane lands at `≤ 3328`; pairs cover all 16
    lanes, so post is `≤ 3328 ≤ 2·3328`.
-/

@[spec]
theorem inv_ntt_layer_1_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hz2 : zeta2.val.natAbs ≤ 1664) (hz3 : zeta3.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step
      vec zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 2 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 1 * 3328 := by
    intro i hi; have := hpre i hi; omega
  -- Step 1: (0, 2) ζ0.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B vec zeta0 0#usize 2#usize 1
      h0lt h2lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 2 h2lt) (by decide))
  -- Step 2: (1, 3) ζ0.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_3 : (v1.elements.val[3]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v1_unc 3 h3lt (by decide) (by decide)]; exact hb_init 3 h3lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v1 zeta0 1#usize 3#usize 1
      h1lt h3lt (by decide) hz0 h_v1_1 h_v1_3 (by decide))
  -- Step 3: (4, 6) ζ1.
  have h_v2_4 : (v2.elements.val[4]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v2_unc 4 h4lt (by decide) (by decide), h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v2 zeta1 4#usize 6#usize 1
      h4lt h6lt (by decide) hz1 h_v2_4 h_v2_6 (by decide))
  -- Step 4: (5, 7) ζ1.
  have h_v3_5 : (v3.elements.val[5]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v3 zeta1 5#usize 7#usize 1
      h5lt h7lt (by decide) hz1 h_v3_5 h_v3_7 (by decide))
  -- Step 5: (8, 10) ζ2.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_10 : (v4.elements.val[10]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v4 zeta2 8#usize 10#usize 1
      h8lt h10lt (by decide) hz2 h_v4_8 h_v4_10 (by decide))
  -- Step 6: (9, 11) ζ2.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_11 : (v5.elements.val[11]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v5 zeta2 9#usize 11#usize 1
      h9lt h11lt (by decide) hz2 h_v5_9 h_v5_11 (by decide))
  -- Step 7: (12, 14) ζ3.
  have h_v6_12 : (v6.elements.val[12]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v6_unc 12 h12lt (by decide) (by decide),
        h_v5_unc 12 h12lt (by decide) (by decide),
        h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v6 zeta3 12#usize 14#usize 1
      h12lt h14lt (by decide) hz3 h_v6_12 h_v6_14 (by decide))
  -- Step 8: (13, 15) ζ3.
  have h_v7_13 : (v7.elements.val[13]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v7_unc 13 h13lt (by decide) (by decide),
        h_v6_unc 13 h13lt (by decide) (by decide),
        h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v7 zeta3 13#usize 15#usize 1
      h13lt h15lt (by decide) hz3 h_v7_13 h_v7_15 (by decide))
  -- Compose into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_l2 h_body
  intro i hi
  -- Each lane is touched exactly once and ends at ≤ 3328 ≤ 2·3328.
  have h_3328 : (3328 : Nat) ≤ 2 * 3328 := by decide
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_i h_3328
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_i h_3328
  -- Lane 2: step 1 j-lane.
  · have h_eq : v8.elements.val[2]! = v1.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide),
          h_v3_unc 2 h2lt (by decide) (by decide),
          h_v2_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_j h_3328
  -- Lane 3: step 2 j-lane.
  · have h_eq : v8.elements.val[3]! = v2.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide),
          h_v4_unc 3 h3lt (by decide) (by decide),
          h_v3_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_j h_3328
  -- Lane 4: step 3 i-lane.
  · have h_eq : v8.elements.val[4]! = v3.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_i h_3328
  -- Lane 5: step 4 i-lane.
  · have h_eq : v8.elements.val[5]! = v4.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_i h_3328
  -- Lane 6: step 3 j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_j h_3328
  -- Lane 7: step 4 j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_j h_3328
  -- Lane 8: step 5 i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_i h_3328
  -- Lane 9: step 6 i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_i h_3328
  -- Lane 10: step 5 j-lane.
  · have h_eq : v8.elements.val[10]! = v5.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_j h_3328
  -- Lane 11: step 6 j-lane.
  · have h_eq : v8.elements.val[11]! = v6.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_j h_3328
  -- Lane 12: step 7 i-lane.
  · have h_eq : v8.elements.val[12]! = v7.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_i h_3328
  -- Lane 13: step 8 i-lane.
  · exact le_trans h_v8_i h_3328
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_j h_3328
  -- Lane 15: step 8 j-lane.
  · exact le_trans h_v8_j h_3328

/-! ## L2.7a — `inv_ntt_layer_2_step_spec`

    Eight disjoint inverse butterflies on pairs `(0,4)ζ0`, `(1,5)ζ0`, `(2,6)ζ0`,
    `(3,7)ζ0`, `(8,12)ζ1`, `(9,13)ζ1`, `(10,14)ζ1`, `(11,15)ζ1`. Input bound
    `≤ 2·3328` (B=2); each touched lane lands at `≤ 3328 ≤ 4·3328`.
-/

@[spec]
theorem inv_ntt_layer_2_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 : Std.I16)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 2 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step vec zeta0 zeta1
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 2 * 3328 := hpre
  -- Step 1: (0, 4) ζ0.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B vec zeta0 0#usize 4#usize 2
      h0lt h4lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 4 h4lt) (by decide))
  -- Step 2: (1, 5) ζ0.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_5 : (v1.elements.val[5]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v1_unc 5 h5lt (by decide) (by decide)]; exact hb_init 5 h5lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v1 zeta0 1#usize 5#usize 2
      h1lt h5lt (by decide) hz0 h_v1_1 h_v1_5 (by decide))
  -- Step 3: (2, 6) ζ0.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v2 zeta0 2#usize 6#usize 2
      h2lt h6lt (by decide) hz0 h_v2_2 h_v2_6 (by decide))
  -- Step 4: (3, 7) ζ0.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v3 zeta0 3#usize 7#usize 2
      h3lt h7lt (by decide) hz0 h_v3_3 h_v3_7 (by decide))
  -- Step 5: (8, 12) ζ1.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v4 zeta1 8#usize 12#usize 2
      h8lt h12lt (by decide) hz1 h_v4_8 h_v4_12 (by decide))
  -- Step 6: (9, 13) ζ1.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v5 zeta1 9#usize 13#usize 2
      h9lt h13lt (by decide) hz1 h_v5_9 h_v5_13 (by decide))
  -- Step 7: (10, 14) ζ1.
  have h_v6_10 : (v6.elements.val[10]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v6_unc 10 h10lt (by decide) (by decide),
        h_v5_unc 10 h10lt (by decide) (by decide),
        h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v6 zeta1 10#usize 14#usize 2
      h10lt h14lt (by decide) hz1 h_v6_10 h_v6_14 (by decide))
  -- Step 8: (11, 15) ζ1.
  have h_v7_11 : (v7.elements.val[11]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v7_unc 11 h11lt (by decide) (by decide),
        h_v6_unc 11 h11lt (by decide) (by decide),
        h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v7 zeta1 11#usize 15#usize 2
      h11lt h15lt (by decide) hz1 h_v7_11 h_v7_15 (by decide))
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step vec zeta0 zeta1
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_l2 h_body
  intro i hi
  have h_3328 : (3328 : Nat) ≤ 4 * 3328 := by decide
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_i h_3328
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_i h_3328
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_i h_3328
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_i h_3328
  -- Lane 4: step 1 j-lane.
  · have h_eq : v8.elements.val[4]! = v1.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide),
          h_v3_unc 4 h4lt (by decide) (by decide),
          h_v2_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_j h_3328
  -- Lane 5: step 2 j-lane.
  · have h_eq : v8.elements.val[5]! = v2.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide),
          h_v4_unc 5 h5lt (by decide) (by decide),
          h_v3_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_j h_3328
  -- Lane 6: step 3 j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_j h_3328
  -- Lane 7: step 4 j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_j h_3328
  -- Lane 8: step 5 i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_i h_3328
  -- Lane 9: step 6 i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_i h_3328
  -- Lane 10: step 7 i-lane.
  · have h_eq : v8.elements.val[10]! = v7.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_i h_3328
  -- Lane 11: step 8 i-lane.
  · exact le_trans h_v8_i h_3328
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_j h_3328
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_j h_3328
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_j h_3328
  -- Lane 15: step 8 j-lane.
  · exact le_trans h_v8_j h_3328

/-! ## L2.7b — `inv_ntt_layer_3_step_spec`

    Eight disjoint inverse butterflies on pairs `(0,8)`, `(1,9)`, …, `(7,15)`
    all with the single ζ. Input bound `≤ 2·3328` (B=2); each touched lane
    lands at `≤ 3328 ≤ 4·3328`.
-/

@[spec]
theorem inv_ntt_layer_3_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (hz : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 2 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step vec zeta
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 2 * 3328 := hpre
  -- Step 1: (0, 8).
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B vec zeta 0#usize 8#usize 2
      h0lt h8lt (by decide) hz (hb_init 0 h0lt) (hb_init 8 h8lt) (by decide))
  -- Step 2: (1, 9).
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_9 : (v1.elements.val[9]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v1_unc 9 h9lt (by decide) (by decide)]; exact hb_init 9 h9lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v1 zeta 1#usize 9#usize 2
      h1lt h9lt (by decide) hz h_v1_1 h_v1_9 (by decide))
  -- Step 3: (2, 10).
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_10 : (v2.elements.val[10]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v2_unc 10 h10lt (by decide) (by decide), h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v2 zeta 2#usize 10#usize 2
      h2lt h10lt (by decide) hz h_v2_2 h_v2_10 (by decide))
  -- Step 4: (3, 11).
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_11 : (v3.elements.val[11]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v3 zeta 3#usize 11#usize 2
      h3lt h11lt (by decide) hz h_v3_3 h_v3_11 (by decide))
  -- Step 5: (4, 12).
  have h_v4_4 : (v4.elements.val[4]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v4_unc 4 h4lt (by decide) (by decide),
        h_v3_unc 4 h4lt (by decide) (by decide),
        h_v2_unc 4 h4lt (by decide) (by decide),
        h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v4 zeta 4#usize 12#usize 2
      h4lt h12lt (by decide) hz h_v4_4 h_v4_12 (by decide))
  -- Step 6: (5, 13).
  have h_v5_5 : (v5.elements.val[5]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v5_unc 5 h5lt (by decide) (by decide),
        h_v4_unc 5 h5lt (by decide) (by decide),
        h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v5 zeta 5#usize 13#usize 2
      h5lt h13lt (by decide) hz h_v5_5 h_v5_13 (by decide))
  -- Step 7: (6, 14).
  have h_v6_6 : (v6.elements.val[6]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v6_unc 6 h6lt (by decide) (by decide),
        h_v5_unc 6 h6lt (by decide) (by decide),
        h_v4_unc 6 h6lt (by decide) (by decide),
        h_v3_unc 6 h6lt (by decide) (by decide),
        h_v2_unc 6 h6lt (by decide) (by decide),
        h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v6 zeta 6#usize 14#usize 2
      h6lt h14lt (by decide) hz h_v6_6 h_v6_14 (by decide))
  -- Step 8: (7, 15).
  have h_v7_7 : (v7.elements.val[7]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v7_unc 7 h7lt (by decide) (by decide),
        h_v6_unc 7 h7lt (by decide) (by decide),
        h_v5_unc 7 h7lt (by decide) (by decide),
        h_v4_unc 7 h7lt (by decide) (by decide),
        h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v7 zeta 7#usize 15#usize 2
      h7lt h15lt (by decide) hz h_v7_7 h_v7_15 (by decide))
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step vec zeta = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_l2 h_body
  intro i hi
  have h_3328 : (3328 : Nat) ≤ 4 * 3328 := by decide
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_i h_3328
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_i h_3328
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_i h_3328
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_i h_3328
  -- Lane 4: step 5 i-lane.
  · have h_eq : v8.elements.val[4]! = v5.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_i h_3328
  -- Lane 5: step 6 i-lane.
  · have h_eq : v8.elements.val[5]! = v6.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_i h_3328
  -- Lane 6: step 7 i-lane.
  · have h_eq : v8.elements.val[6]! = v7.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_i h_3328
  -- Lane 7: step 8 i-lane.
  · exact le_trans h_v8_i h_3328
  -- Lane 8: step 1 j-lane.
  · have h_eq : v8.elements.val[8]! = v1.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide),
          h_v5_unc 8 h8lt (by decide) (by decide),
          h_v4_unc 8 h8lt (by decide) (by decide),
          h_v3_unc 8 h8lt (by decide) (by decide),
          h_v2_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_j h_3328
  -- Lane 9: step 2 j-lane.
  · have h_eq : v8.elements.val[9]! = v2.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide),
          h_v6_unc 9 h9lt (by decide) (by decide),
          h_v5_unc 9 h9lt (by decide) (by decide),
          h_v4_unc 9 h9lt (by decide) (by decide),
          h_v3_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_j h_3328
  -- Lane 10: step 3 j-lane.
  · have h_eq : v8.elements.val[10]! = v3.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide),
          h_v5_unc 10 h10lt (by decide) (by decide),
          h_v4_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_j h_3328
  -- Lane 11: step 4 j-lane.
  · have h_eq : v8.elements.val[11]! = v4.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide),
          h_v6_unc 11 h11lt (by decide) (by decide),
          h_v5_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_j h_3328
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_j h_3328
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_j h_3328
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_j h_3328
  -- Lane 15: step 8 j-lane.
  · exact le_trans h_v8_j h_3328

end libcrux_iot_ml_kem.Equivalence
