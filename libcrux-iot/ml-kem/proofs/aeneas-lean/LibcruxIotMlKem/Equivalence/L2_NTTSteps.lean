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

/-- Under `|a.val| ≤ 3·3328` and `|t.val| ≤ 3328`, the I16-wrapped sum
    `a + t` has `.val = a.val + t.val` and `.val.natAbs ≤ 4·3328`. -/
private theorem add_no_overflow_value (a t : Std.I16)
    (h_a : a.val.natAbs ≤ 3 * 3328) (h_t : t.val.natAbs ≤ 3328) :
    (Std.I16.wrapping_add a t).val = a.val + t.val
      ∧ (Std.I16.wrapping_add a t).val.natAbs ≤ 4 * 3328 := by
  -- |a + t| ≤ |a| + |t| ≤ 3·3328 + 3328 = 4·3328 = 13312 < 2^15 = 32768.
  have h_sum_abs : ((a.val + t.val : Int)).natAbs ≤ 4 * 3328 := by
    have h_tri : (a.val + t.val).natAbs ≤ a.val.natAbs + t.val.natAbs := Int.natAbs_add_le _ _
    omega
  -- No-overflow ⇒ bmod is identity.
  have h_lb : -(2 ^ 15 : Int) ≤ a.val + t.val := by
    have : ((a.val + t.val : Int)).natAbs ≤ 4 * 3328 := h_sum_abs
    omega
  have h_ub : a.val + t.val < (2 ^ 15 : Int) := by
    have : ((a.val + t.val : Int)).natAbs ≤ 4 * 3328 := h_sum_abs
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

/-- Under `|a.val| ≤ 3·3328` and `|t.val| ≤ 3328`, the I16-wrapped diff
    `a - t` has `.val = a.val - t.val` and `.val.natAbs ≤ 4·3328`. -/
private theorem sub_no_overflow_value (a t : Std.I16)
    (h_a : a.val.natAbs ≤ 3 * 3328) (h_t : t.val.natAbs ≤ 3328) :
    (Std.I16.wrapping_sub a t).val = a.val - t.val
      ∧ (Std.I16.wrapping_sub a t).val.natAbs ≤ 4 * 3328 := by
  have h_diff_abs : ((a.val - t.val : Int)).natAbs ≤ 4 * 3328 := by
    -- a - t = a + (-t), and natAbs (-t) = natAbs t.
    have h_neg_natAbs : (-t.val).natAbs = t.val.natAbs := Int.natAbs_neg _
    have h_eq : a.val - t.val = a.val + (-t.val) := by ring
    rw [h_eq]
    have h_tri : (a.val + (-t.val)).natAbs ≤ a.val.natAbs + (-t.val).natAbs :=
      Int.natAbs_add_le _ _
    rw [h_neg_natAbs] at h_tri
    omega
  have h_lb : -(2 ^ 15 : Int) ≤ a.val - t.val := by
    have : ((a.val - t.val : Int)).natAbs ≤ 4 * 3328 := h_diff_abs
    omega
  have h_ub : a.val - t.val < (2 ^ 15 : Int) := by
    have : ((a.val - t.val : Int)).natAbs ≤ 4 * 3328 := h_diff_abs
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

end libcrux_iot_ml_kem.Equivalence
