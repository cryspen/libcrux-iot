/-
  # `BitMlKem/Commute.lean` — M.2 commute lemmas (Block A).

  Layer-0 scalar `Std.I16 → ZMod 3329` field-element commute lemmas.
  Each lemma consumes an impl-level "value-equation" precondition
  (already produced by L0/L1 Triples in the `Equivalence/` tree) and
  produces the matching `ZMod 3329` algebraic equation through one of
  the M.1 lane lifts `i16_to_spec_fe_{plain,mont}`.

  Port of `Hacspec_ml_kem.Commute.Chunk.fst` lines 35-680 (the
  Layer-0 / "scalar" portion of Block A); blocks B, C, D land in
  subsequent dispatches per the campaign plan §C.2-C.4.

  ## Discipline (Plan.lean §X.2 K.1)

  Each lemma carries `@[scoped grind]` and lives inside the
  `libcrux_iot_ml_kem.BitMlKem.Commute` namespace, so consumers
  enable `grind` over the commute set with
  `open libcrux_iot_ml_kem.BitMlKem.Commute` (no global pollution).

  ## File-shape notes

  - F* uses `v r % 3329 == ... % 3329` (Int arithmetic mod q). We
    translate by stating the precondition directly as a `ZMod 3329`
    equation — the M.1 lane lifts already give us the cast.
  - F* uses `v r == v a + v b` (strict Int equality) for the strict
    `_plain`/`_mont` variants. We mirror this with `r.val = a.val + b.val`
    on `Std.I16.val : Int`.
  - In `ZMod 3329`, `mont_i16_to_spec_fe x = x.val · 169` and
    `i16_to_spec_fe_plain x = x.val`, so each F* `lemma_mod_*_distr_*`
    chain collapses to a single `rw [hr]; ring`.
-/
import LibcruxIotMlKem.BitMlKem.Spec
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace libcrux_iot_ml_kem.BitMlKem.Commute

open Aeneas Aeneas.Std
open libcrux_iot_ml_kem.BitMlKem

/-! ## A.1 / A.2 — pointwise addition commutes (plain and Mont). -/

/-- A.1 `lemma_add_fe_commute_plain` (F*: Chunk.fst:35). Strict
    Int-equality precondition: the impl returns the exact integer
    sum (no overflow), and the plain-domain lift respects this. -/
@[scoped grind]
theorem lemma_add_fe_commute_plain (a b r : Std.I16)
    (hr : r.val = a.val + b.val) :
    i16_to_spec_fe_plain a + i16_to_spec_fe_plain b = i16_to_spec_fe_plain r := by
  unfold i16_to_spec_fe_plain
  rw [hr]; push_cast; ring

/-- A.2 `lemma_add_fe_commute_mont` (F*: Chunk.fst:41). Same shape
    as A.1 but lifts through `mont` (extra `· 169` factor). -/
@[scoped grind]
theorem lemma_add_fe_commute_mont (a b r : Std.I16)
    (hr : r.val = a.val + b.val) :
    i16_to_spec_fe_mont a + i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; push_cast; ring

/-! ## A.3 / A.4 — pointwise subtraction commutes. -/

/-- A.3 `lemma_sub_fe_commute_plain` (F*: Chunk.fst:48). -/
@[scoped grind]
theorem lemma_sub_fe_commute_plain (a b r : Std.I16)
    (hr : r.val = a.val - b.val) :
    i16_to_spec_fe_plain a - i16_to_spec_fe_plain b = i16_to_spec_fe_plain r := by
  unfold i16_to_spec_fe_plain
  rw [hr]; push_cast; ring

/-- A.4 `lemma_sub_fe_commute_mont` (F*: Chunk.fst:54). -/
@[scoped grind]
theorem lemma_sub_fe_commute_mont (a b r : Std.I16)
    (hr : r.val = a.val - b.val) :
    i16_to_spec_fe_mont a - i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; push_cast; ring

/-! ## A.5 — Barrett reduction commutes (plain). -/

/-- A.5 `lemma_barrett_fe_commute` (F*: Chunk.fst:63). Barrett
    reduction preserves residue mod q, so the plain lift is identity
    on the reduced value.

    Statement uses `r = a` order (matching F*) — that is,
    `i16_to_spec_fe_plain r = i16_to_spec_fe_plain a`. -/
@[scoped grind]
theorem lemma_barrett_fe_commute (a r : Std.I16)
    (hr : (r.val : ZMod 3329) = (a.val : ZMod 3329)) :
    i16_to_spec_fe_plain r = i16_to_spec_fe_plain a := by
  unfold i16_to_spec_fe_plain
  exact hr

/-! ## A.6 — Mont zeta cancellation (mont ↔ plain bridge). -/

/-- A.6 `lemma_mont_zeta_cancel` (F*: Chunk.fst:71). The impl stores
    zetas pre-multiplied by `R`, so the Mont lift recovers the plain
    abstract zeta when paired with a residue-equality precondition. -/
@[scoped grind]
theorem lemma_mont_zeta_cancel (zeta_mont zeta_plain : Std.I16)
    (hr : (zeta_mont.val : ZMod 3329) * 169 = (zeta_plain.val : ZMod 3329)) :
    i16_to_spec_fe_mont zeta_mont = i16_to_spec_fe_plain zeta_plain := by
  unfold i16_to_spec_fe_mont i16_to_spec_fe_plain
  exact hr

/-! ## A.7 / A.8 — mod-aware add/sub commutes (residue precondition). -/

/-- A.7 `lemma_add_fe_commute_mont_mod` (F*: Chunk.fst:151). The
    precondition is a `ZMod 3329` equality rather than a strict Int
    sum — used by butterfly outputs whose impl post is mod q. -/
@[scoped grind]
theorem lemma_add_fe_commute_mont_mod (a b r : Std.I16)
    (hr : (r.val : ZMod 3329) = (a.val : ZMod 3329) + (b.val : ZMod 3329)) :
    i16_to_spec_fe_mont a + i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-- A.8 `lemma_sub_fe_commute_mont_mod` (F*: Chunk.fst:159). -/
@[scoped grind]
theorem lemma_sub_fe_commute_mont_mod (a b r : Std.I16)
    (hr : (r.val : ZMod 3329) = (a.val : ZMod 3329) - (b.val : ZMod 3329)) :
    i16_to_spec_fe_mont a - i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-! ## A.9 / A.10 — butterfly commute (plus and minus halves). -/

/-- A.9 `lemma_butterfly_fe_commute_plus` (F*: Chunk.fst:187). The
    `+` output of a `ntt_layer_*_step` butterfly: in the Mont domain,
    the impl post `result_i ≡ vec_i + vec_j · zeta · 169 (mod q)`
    collapses to the FE equation `mont_fe result_i = mont_fe vec_i +
    mont_fe zeta · mont_fe vec_j` because the Montgomery factor
    cancels exactly with the `· 169` in the residue. -/
@[scoped grind]
theorem lemma_butterfly_fe_commute_plus
    (vec_i vec_j zeta result_i : Std.I16)
    (hr : (result_i.val : ZMod 3329) =
          (vec_i.val : ZMod 3329) +
          (vec_j.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_i =
      i16_to_spec_fe_mont vec_i +
      i16_to_spec_fe_mont zeta * i16_to_spec_fe_mont vec_j := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-- A.10 `lemma_butterfly_fe_commute_minus` (F*: Chunk.fst:217). -/
@[scoped grind]
theorem lemma_butterfly_fe_commute_minus
    (vec_i vec_j zeta result_j : Std.I16)
    (hr : (result_j.val : ZMod 3329) =
          (vec_i.val : ZMod 3329) -
          (vec_j.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_j =
      i16_to_spec_fe_mont vec_i -
      i16_to_spec_fe_mont zeta * i16_to_spec_fe_mont vec_j := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-! ## A.11 — combined butterfly pair (both halves). -/

/-- A.11 `lemma_butterfly_pair_commute` (F*: Chunk.fst:234). Bundles
    A.9 and A.10 into a single ∧ — one call per butterfly pair
    instead of two. The F* version threads through `Seq.index`; we
    stay scalar at Block A and take the four `Std.I16` lanes
    directly. Block B re-introduces the array machinery. -/
@[scoped grind]
theorem lemma_butterfly_pair_commute
    (vec_i vec_j result_i result_j zeta : Std.I16)
    (hr_i : (result_i.val : ZMod 3329) =
            (vec_i.val : ZMod 3329) +
            (vec_j.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169)
    (hr_j : (result_j.val : ZMod 3329) =
            (vec_i.val : ZMod 3329) -
            (vec_j.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_i =
      i16_to_spec_fe_mont vec_i +
      i16_to_spec_fe_mont zeta * i16_to_spec_fe_mont vec_j
    ∧
    i16_to_spec_fe_mont result_j =
      i16_to_spec_fe_mont vec_i -
      i16_to_spec_fe_mont zeta * i16_to_spec_fe_mont vec_j := by
  exact ⟨lemma_butterfly_fe_commute_plus vec_i vec_j zeta result_i hr_i,
         lemma_butterfly_fe_commute_minus vec_i vec_j zeta result_j hr_j⟩

/-! ## A.12 — inverse butterfly multiply-diff. -/

/-- A.12 `lemma_inv_butterfly_fe_commute_mul_diff` (F*: Chunk.fst:279).
    The `j` output of the Gentleman–Sande inverse butterfly. -/
@[scoped grind]
theorem lemma_inv_butterfly_fe_commute_mul_diff
    (vec_i vec_j zeta result_j : Std.I16)
    (hr : (result_j.val : ZMod 3329) =
          ((vec_j.val : ZMod 3329) - (vec_i.val : ZMod 3329)) *
          (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_j =
      i16_to_spec_fe_mont zeta *
      (i16_to_spec_fe_mont vec_j - i16_to_spec_fe_mont vec_i) := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-! ## A.16 / A.17 — base-case multiply commutes (even and odd halves).

    These are the upstream `Z3rlimit 400` lemmas (~80 LOC F* each
    with explicit `lemma_mod_*_distr_*` chains). In Lean the same
    statement falls to `rw [hr]; ring` in `ZMod 3329` because the
    Montgomery-factor algebra is just commutative-ring distribution. -/

/-- A.16 `lemma_base_case_mult_even_fe_commute` (F*: Chunk.fst:414). -/
@[scoped grind]
theorem lemma_base_case_mult_even_fe_commute
    (a0 b0 a1 b1 zeta result : Std.I16)
    (hr : (result.val : ZMod 3329) =
          ((a0.val : ZMod 3329) * (b0.val : ZMod 3329) +
           (a1.val : ZMod 3329) * (b1.val : ZMod 3329) *
           (zeta.val : ZMod 3329) * 169) * 169) :
    i16_to_spec_fe_mont result =
      i16_to_spec_fe_mont a0 * i16_to_spec_fe_mont b0 +
      i16_to_spec_fe_mont a1 * i16_to_spec_fe_mont b1 *
      i16_to_spec_fe_mont zeta := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-- A.17 `lemma_base_case_mult_odd_fe_commute` (F*: Chunk.fst:523). -/
@[scoped grind]
theorem lemma_base_case_mult_odd_fe_commute
    (a0 b1 a1 b0 result : Std.I16)
    (hr : (result.val : ZMod 3329) =
          ((a0.val : ZMod 3329) * (b1.val : ZMod 3329) +
           (a1.val : ZMod 3329) * (b0.val : ZMod 3329)) * 169) :
    i16_to_spec_fe_mont result =
      i16_to_spec_fe_mont a0 * i16_to_spec_fe_mont b1 +
      i16_to_spec_fe_mont a1 * i16_to_spec_fe_mont b0 := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-! ## A.18 — combined base-case multiply pair (both halves). -/

/-- A.18 `lemma_base_case_mult_pair_commute` (F*: Chunk.fst:547).
    Bundles A.16 / A.17 — one call per binomial pair. -/
@[scoped grind]
theorem lemma_base_case_mult_pair_commute
    (a0 b0 a1 b1 zeta result_even result_odd : Std.I16)
    (hr_e : (result_even.val : ZMod 3329) =
            ((a0.val : ZMod 3329) * (b0.val : ZMod 3329) +
             (a1.val : ZMod 3329) * (b1.val : ZMod 3329) *
             (zeta.val : ZMod 3329) * 169) * 169)
    (hr_o : (result_odd.val : ZMod 3329) =
            ((a0.val : ZMod 3329) * (b1.val : ZMod 3329) +
             (a1.val : ZMod 3329) * (b0.val : ZMod 3329)) * 169) :
    i16_to_spec_fe_mont result_even =
      i16_to_spec_fe_mont a0 * i16_to_spec_fe_mont b0 +
      i16_to_spec_fe_mont a1 * i16_to_spec_fe_mont b1 *
      i16_to_spec_fe_mont zeta
    ∧
    i16_to_spec_fe_mont result_odd =
      i16_to_spec_fe_mont a0 * i16_to_spec_fe_mont b1 +
      i16_to_spec_fe_mont a1 * i16_to_spec_fe_mont b0 := by
  exact ⟨lemma_base_case_mult_even_fe_commute a0 b0 a1 b1 zeta result_even hr_e,
         lemma_base_case_mult_odd_fe_commute a0 b1 a1 b0 result_odd hr_o⟩

/-! ## A.19 / A.20 — Montgomery multiplication commutes. -/

/-- A.19 `lemma_mont_mul_fe_commute_mont_mont` (F*: Chunk.fst:615).
    Two Mont-domain operands: the impl's `· R⁻¹` cancels the Mont
    lift's extra factor, yielding plain FE multiplication. -/
@[scoped grind]
theorem lemma_mont_mul_fe_commute_mont_mont (a b r : Std.I16)
    (hr : (r.val : ZMod 3329) =
          (a.val : ZMod 3329) * (b.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont a * i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-- A.20 `lemma_mont_mul_fe_commute_mont_plain` (F*: Chunk.fst:624).
    Mixed mode: `a` Mont, `b` plain, result plain. -/
@[scoped grind]
theorem lemma_mont_mul_fe_commute_mont_plain (a b r : Std.I16)
    (hr : (r.val : ZMod 3329) =
          (a.val : ZMod 3329) * (b.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont a * i16_to_spec_fe_plain b = i16_to_spec_fe_plain r := by
  unfold i16_to_spec_fe_mont i16_to_spec_fe_plain
  rw [hr]; ring

/-! ## A.21 — plain multiplication by a constant. -/

/-- A.21 `lemma_mul_const_fe_commute_plain` (F*: Chunk.fst:633).
    Strict Int-product precondition (no overflow), plain-domain
    lift on both sides. -/
@[scoped grind]
theorem lemma_mul_const_fe_commute_plain (a c r : Std.I16)
    (hr : r.val = a.val * c.val) :
    i16_to_spec_fe_plain a * i16_to_spec_fe_plain c = i16_to_spec_fe_plain r := by
  unfold i16_to_spec_fe_plain
  rw [hr]; push_cast; ring

/-! ## A.22 — combined inverse-butterfly pair. -/

/-- A.22 `lemma_inv_butterfly_pair_commute` (F*: Chunk.fst:588).
    Bundles the `add_mont_mod` (lane `i`) and `mul_diff` (lane `j`)
    sides of one Gentleman–Sande inverse butterfly. -/
@[scoped grind]
theorem lemma_inv_butterfly_pair_commute
    (vec_i vec_j result_i result_j zeta : Std.I16)
    (hr_i : (result_i.val : ZMod 3329) =
            (vec_j.val : ZMod 3329) + (vec_i.val : ZMod 3329))
    (hr_j : (result_j.val : ZMod 3329) =
            ((vec_j.val : ZMod 3329) - (vec_i.val : ZMod 3329)) *
            (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_i =
      i16_to_spec_fe_mont vec_i + i16_to_spec_fe_mont vec_j
    ∧
    i16_to_spec_fe_mont result_j =
      i16_to_spec_fe_mont zeta *
      (i16_to_spec_fe_mont vec_j - i16_to_spec_fe_mont vec_i) := by
  refine ⟨?_, ?_⟩
  · -- Reuse A.7 with operands swapped via `add_comm`; A.7's ensures is
    -- `mont_fe a + mont_fe b = mont_fe r`, so the goal direction needs `.symm`.
    have hr_i' : (result_i.val : ZMod 3329) =
        (vec_i.val : ZMod 3329) + (vec_j.val : ZMod 3329) := by
      rw [hr_i]; ring
    exact (lemma_add_fe_commute_mont_mod vec_i vec_j result_i hr_i').symm
  · exact lemma_inv_butterfly_fe_commute_mul_diff vec_i vec_j zeta result_j hr_j

end libcrux_iot_ml_kem.BitMlKem.Commute
