/-
  # `BitMlKem/SpecPure.lean` — Open Question I.7 resolution.

  The hacspec ML-KEM extraction (`HacspecMlKem.Extraction.Funs`) wraps
  every spec function in the Aeneas `Result` monad, even when the
  body is mathematically pure (no panic / divergence). The bit-side
  intermediate spec (`BitMlKem.Spec`) operates on `MontPoly =
  Vector (ZMod 3329) 256`, which is genuinely pure.

  Layer M.4 alg-equiv lemmas state equations of the form
    `bit_<op> (lift hacspec_input) = lift (Spec.<op>_pure hacspec_input)`
  where `Spec.<op>_pure` is the panic-stripped projection of the
  hacspec `Result`-monadic spec. This file defines those `_pure`
  aliases.

  Per arch plan §F.2 option (b): each alias is defined by pattern
  match on the `Result`. The companion *side lemmas* of the form
  `Spec.<op> args = .ok (Spec.<op>_pure args)` are panic-freedom
  obligations and can be discharged once panic-free is established
  for the `parameters.FieldElement.{add,sub,mul,neg}` primitives.

  ## Scope

  - Scalar `parameters.FieldElement.{add,sub,mul,neg}` get `_pure`
    aliases — they are used pointwise inside every `polynomial.*`
    closure in the hacspec extraction.
  - The three poly-level hacspec wrappers used by M.4 easy cluster
    (`polynomial.add_to_ring_element`, `polynomial.poly_barrett_reduce`,
    `polynomial.subtract_reduce`) get `_pure` aliases.

  ## Discipline

  - All `_pure` defs are `noncomputable` because the match-on-Result
    extraction does not reduce by `decide` for arbitrary inputs;
    callers reason about them via the side lemmas (TODO) or by
    direct `simp only [<op>_pure]` rewriting through M.4 proofs.
  - No Mathlib imports needed; this file lives above the M.1 barrier
    inheriting `ZMod 3329` transitively via `BitMlKem.Spec`.
-/
import LibcruxIotMlKem.BitMlKem.Spec

namespace libcrux_iot_ml_kem.BitMlKem.SpecPure

open Aeneas Aeneas.Std
open hacspec_ml_kem

/-! ## Default `FieldElement` (used as fall-through in `_pure` match). -/

/-- Canonical default for `parameters.FieldElement` — the zero element.
    Used as the fall-through branch in the `match` definitions below;
    chosen to be in canonical range so the lift through `zmodOfFE`
    gives `0 : ZMod 3329`. -/
def defaultFE : parameters.FieldElement := { val := (0#u16 : Std.U16) }

instance : Inhabited parameters.FieldElement := ⟨defaultFE⟩

/-! ## Scalar `_pure` aliases. -/

/-- Pure projection of `parameters.FieldElement.add`. The hacspec body
    computes `(self.val + other.val) % q` via U32 lifts, all of which
    are panic-free; this `_pure` extracts the `.ok` value. -/
noncomputable def FieldElement.add_pure
    (self other : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.add self other with
  | .ok r => r
  | _ => defaultFE

/-- Pure projection of `parameters.FieldElement.sub`. Mirrors
    `add_pure`; hacspec body computes `(self.val + q - other.val) % q`. -/
noncomputable def FieldElement.sub_pure
    (self other : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.sub self other with
  | .ok r => r
  | _ => defaultFE

/-- Pure projection of `parameters.FieldElement.mul`. -/
noncomputable def FieldElement.mul_pure
    (self other : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.mul self other with
  | .ok r => r
  | _ => defaultFE

/-- Pure projection of `parameters.FieldElement.neg`. -/
noncomputable def FieldElement.neg_pure
    (self : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.neg self with
  | .ok r => r
  | _ => defaultFE

/-! ## Poly-level `_pure` aliases.

    These wrap the 256-coefficient Aeneas-`Array` results into a pure
    `SpecPoly = Vector parameters.FieldElement 256` via per-lane
    extraction. The wrapper is panic-free at the M.4 caller level
    because `parameters.createi` itself is panic-free for the
    256-element shape. -/

/-- Pure projection of `polynomial.add_to_ring_element`. -/
noncomputable def polynomial.add_to_ring_element_pure
    (lhs rhs : Std.Array parameters.FieldElement 256#usize) :
    Std.Array parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.polynomial.add_to_ring_element lhs rhs with
  | .ok r => r
  | _ => lhs

/-- Pure projection of `polynomial.poly_barrett_reduce`. -/
noncomputable def polynomial.poly_barrett_reduce_pure
    (p : Std.Array parameters.FieldElement 256#usize) :
    Std.Array parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.polynomial.poly_barrett_reduce p with
  | .ok r => r
  | _ => p

/-- Pure projection of `polynomial.subtract_reduce`. -/
noncomputable def polynomial.subtract_reduce_pure
    (a b : Std.Array parameters.FieldElement 256#usize) :
    Std.Array parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.polynomial.subtract_reduce a b with
  | .ok r => r
  | _ => a

/-! ## Side lemmas — panic-freedom (Phase 1.1 of FC campaign).

    `add_eq_ok` and `mul_eq_ok` are UNCONDITIONALLY true because U32
    widening prevents overflow in both cases (`a.val + b.val < 2^17`,
    `a.val * b.val ≤ (2^16 - 1)² < 2^32`).

    `sub_eq_ok` and `neg_eq_ok` require a CANONICITY PRECONDITION
    `Canonical a := a.val.val < q`. The Aeneas extraction dropped the
    Rust source's `#[refine(val < FIELD_MODULUS)]` refinement on
    `parameters.FieldElement::new` (see `specs/ml-kem/src/parameters.rs:319`),
    leaving any `U16` admissible. Counterexamples for arbitrary U16
    (verified via `#eval`):
    * `sub ⟨0#u16⟩ ⟨65535#u16⟩ = .fail` (U32 underflow after `+ q`).
    * `neg ⟨65535#u16⟩ = .fail` (U16 underflow `q - val`, no widening).

    Audit (2026-05-23) of the 3 call-sites of `sub`/`neg` in the
    hacspec extraction confirms ALL callers feed canonical inputs:
    * `ntt.butterfly` and `invert_ntt.inv_butterfly` — inputs `a, b`
      assumed canonical by caller; `mul`'s output is always canonical
      by construction.
    * `ntt.base_case_multiply_n` — `neg fe` where `fe` is from the
      compile-time zetas table (all canonical).

    Canonicity is also the natural invariant of the bit-side lifts:
    `feOfZMod : ZMod 3329 → FieldElement` produces canonical FEs by
    construction (the lift packs `z.val < 3329 < 2^16` into a U16).

    Canonicity preservation lemmas (`Canonical_add_pure`,
    `Canonical_mul_pure`, etc.) are deferred to Phase 1.2 when the
    poly-wrapper side lemmas need them; the U16-cast simp residue
    requires non-trivial unfolding that's better tackled with
    downstream context. -/

/-- A `parameters.FieldElement` is canonical iff its underlying U16
    holds a value strictly below the field modulus `q = 3329`. This
    is the invariant the Rust source maintains via
    `#[refine(val < FIELD_MODULUS)]` on `FieldElement::new` — the
    Aeneas extraction drops the refinement, so we carry canonicity
    as an explicit predicate.

    The bit-side lift `feOfZMod` produces canonical FEs by
    construction; downstream wrappers (`butterfly`, etc.) take
    canonical inputs and produce canonical outputs. -/
def Canonical (fe : parameters.FieldElement) : Prop :=
  fe.val.val < parameters.FIELD_MODULUS.val

private theorem uscalar_rem_ok_U32 (z m : Std.U32) (hm : m.val ≠ 0) :
    ∃ w : Std.U32, (z % m : Result Std.U32) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U32) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

/-- U16 variant of `uscalar_rem_ok_U32` — used by `neg_eq_ok` whose
    `% q` step is at U16 width (no widening). -/
private theorem uscalar_rem_ok_U16 (z m : Std.U16) (hm : m.val ≠ 0) :
    ∃ w : Std.U16, (z % m : Result Std.U16) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U16) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

/-- `parameters.FieldElement.add` is panic-free for ALL `FieldElement`
    inputs (no canonicity precondition). The U32 widening bounds the
    sum strictly below `2^32`. -/
theorem FieldElement.add_eq_ok (a b : parameters.FieldElement) :
    parameters.FieldElement.add a b = .ok (FieldElement.add_pure a b) := by
  unfold FieldElement.add_pure
  suffices h : ∃ r, parameters.FieldElement.add a b = .ok r by
    obtain ⟨r, hr⟩ := h; rw [hr]
  unfold parameters.FieldElement.add
  simp only [lift, bind_tc_ok]
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.add_equiv x y
  cases hxy : (x + y) with
  | ok z =>
    rw [hxy] at hae; simp at hae
    obtain ⟨_, _, _⟩ := hae
    have hmod_val :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329 := by
      unfold parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, _⟩ := uscalar_rem_ok_U32 z m hmod_ne
    simp only [bind_tc_ok, hw_eq]
    exact ⟨_, rfl⟩
  | fail e =>
    rw [hxy] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hyval] at hae; omega
  | div => rw [hxy] at hae; exact hae.elim

/-- `parameters.FieldElement.mul` is panic-free for ALL `FieldElement`
    inputs. The U32 widening bounds the product strictly below `2^32`. -/
theorem FieldElement.mul_eq_ok (a b : parameters.FieldElement) :
    parameters.FieldElement.mul a b = .ok (FieldElement.mul_pure a b) := by
  unfold FieldElement.mul_pure
  suffices h : ∃ r, parameters.FieldElement.mul a b = .ok r by
    obtain ⟨r, hr⟩ := h; rw [hr]
  unfold parameters.FieldElement.mul
  simp only [lift, bind_tc_ok]
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.mul_equiv x y
  have heqmul : (x * y : Result Std.U32) = Std.UScalar.mul x y := rfl
  cases hxy : (x * y : Result Std.U32) with
  | ok z =>
    rw [heqmul] at hxy; rw [hxy] at hae; simp at hae
    obtain ⟨_, _, _⟩ := hae
    have hmod_val :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329 := by
      unfold parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, _⟩ := uscalar_rem_ok_U32 z m hmod_ne
    simp only [bind_tc_ok, hw_eq]
    exact ⟨_, rfl⟩
  | fail e =>
    rw [heqmul] at hxy; rw [hxy] at hae
    simp only [Std.UScalar.max, Std.UScalarTy.numBits] at hae
    rw [hxval, hyval] at hae
    have : a.val.val * b.val.val < 2^32 := by
      have h1 : a.val.val * b.val.val ≤ (2^16 - 1) * (2^16 - 1) := by
        apply Nat.mul_le_mul <;> omega
      have heq : (2^16 - 1) * (2^16 - 1) = 2^32 - 2*2^16 + 1 := by decide
      omega
    omega
  | div => rw [heqmul] at hxy; rw [hxy] at hae; exact hae.elim

/-- `parameters.FieldElement.sub` is panic-free for CANONICAL inputs.
    The U32 sum `a.val + q` reaches `q + (q-1) < 2·q` without overflow
    (q = 3329), and the subsequent `% q` is well-defined since q ≠ 0.

    For non-canonical inputs the impl can panic — see the doc block
    above and `parameters.FieldElement.sub ⟨0⟩ ⟨65535⟩` counterexample. -/
theorem FieldElement.sub_eq_ok (a b : parameters.FieldElement)
    (ha : Canonical a) (hb : Canonical b) :
    parameters.FieldElement.sub a b = .ok (FieldElement.sub_pure a b) := by
  unfold Canonical at ha hb
  unfold parameters.FIELD_MODULUS at ha hb
  simp at ha hb
  unfold FieldElement.sub_pure
  suffices h : ∃ r, parameters.FieldElement.sub a b = .ok r by
    obtain ⟨r, hr⟩ := h; rw [hr]
  unfold parameters.FieldElement.sub
  simp only [lift, bind_tc_ok]
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  set q : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hqval : q.val = 3329 := by
    show (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329
    unfold parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.add_equiv x q
  cases hxq : (x + q : Result Std.U32) with
  | ok s =>
    rw [hxq] at hae; simp at hae
    obtain ⟨_, hsval, _⟩ := hae
    simp only [bind_tc_ok]
    have hae2 := Std.UScalar.sub_equiv s y
    cases hsy : (s - y : Result Std.U32) with
    | ok u =>
      rw [hsy] at hae2; simp at hae2
      simp only [bind_tc_ok]
      have hq_ne : q.val ≠ 0 := by rw [hqval]; decide
      obtain ⟨w, hw_eq, _⟩ := uscalar_rem_ok_U32 u q hq_ne
      rw [hw_eq]; simp only [bind_tc_ok]
      exact ⟨_, rfl⟩
    | fail e =>
      rw [hsy] at hae2; simp [Std.UScalar.inBounds] at hae2
      rw [hsval, hxval, hqval, hyval] at hae2
      omega
    | div => rw [hsy] at hae2; exact hae2.elim
  | fail e =>
    rw [hxq] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hqval] at hae
    omega
  | div => rw [hxq] at hae; exact hae.elim

/-- `parameters.FieldElement.neg` is panic-free for CANONICAL input.
    The impl computes `q - self.val` in U16 (NO widening), which only
    avoids underflow when `self.val ≤ q`. The subsequent `% q` is
    well-defined since q ≠ 0.

    For non-canonical inputs the impl can panic — see the doc block
    above and `parameters.FieldElement.neg ⟨65535⟩` counterexample. -/
theorem FieldElement.neg_eq_ok (a : parameters.FieldElement)
    (ha : Canonical a) :
    parameters.FieldElement.neg a = .ok (FieldElement.neg_pure a) := by
  unfold Canonical at ha
  unfold parameters.FIELD_MODULUS at ha
  simp at ha
  unfold FieldElement.neg_pure
  suffices h : ∃ r, parameters.FieldElement.neg a = .ok r by
    obtain ⟨r, hr⟩ := h; rw [hr]
  unfold parameters.FieldElement.neg
  have hA := a.val.hBounds
  simp [Std.UScalarTy.numBits] at hA
  have hqval : (parameters.FIELD_MODULUS : Std.U16).val = 3329 := by
    unfold parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.sub_equiv (parameters.FIELD_MODULUS : Std.U16) a.val
  cases hqa : ((parameters.FIELD_MODULUS : Std.U16) - a.val : Result Std.U16) with
  | ok i =>
    rw [hqa] at hae; simp at hae
    obtain ⟨_, _, _⟩ := hae
    simp only [bind_tc_ok]
    have hq_ne : (parameters.FIELD_MODULUS : Std.U16).val ≠ 0 := by
      rw [hqval]; decide
    obtain ⟨w, hw_eq, _⟩ := uscalar_rem_ok_U16 i parameters.FIELD_MODULUS hq_ne
    rw [hw_eq]; simp only [bind_tc_ok]
    exact ⟨_, rfl⟩
  | fail e =>
    rw [hqa] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hqval] at hae
    omega
  | div => rw [hqa] at hae; exact hae.elim

/-! ## Canonicity preservation lemmas (Phase 1.2 of FC campaign).

    Each `Canonical_<op>_pure` shows the `_pure` projection produces a
    canonical FE. Proof shape (mirrors the corresponding `_eq_ok` side
    lemma): chain through the do-block via `<op>_equiv`, extract `w`
    from the final `% q` via `uscalar_rem_ok_U{32,16}`, then bound
    `(UScalar.cast .U16 w).val = w.val < 3329` via
    `Std.UScalar.cast_val_mod_pow_of_inBounds_eq`. -/

/-- Canonicity preservation for `FieldElement.add_pure`. Unconditional:
    the result is the modular reduction `(a.val + b.val) % q < q`.

    Proof strategy: rewrite `parameters.FieldElement.add` to `.ok`
    via `add_eq_ok`, unfold the do-block, case on the U32 `+`/`%`
    branches (the `.ok` branch fires by assumption; `.fail`/`.div`
    discharge via `add_equiv` + `omega`/`hae.elim`), and bound the
    final U16 cast through `cast_val_mod_pow_of_inBounds_eq`. -/
theorem Canonical_add_pure (a b : parameters.FieldElement) :
    Canonical (FieldElement.add_pure a b) := by
  have hadd : parameters.FieldElement.add a b = .ok (FieldElement.add_pure a b) :=
    FieldElement.add_eq_ok a b
  unfold parameters.FieldElement.add at hadd
  simp only [lift, bind_tc_ok] at hadd
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.add_equiv x y
  cases hxy : (x + y) with
  | ok z =>
    rw [hxy] at hae hadd; simp at hae
    obtain ⟨_, _, _⟩ := hae
    simp only [bind_tc_ok] at hadd
    have hmod_val :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329 := by
      unfold parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32 z m hmod_ne
    rw [hw_eq] at hadd; simp only [bind_tc_ok] at hadd
    unfold parameters.FieldElement.new at hadd
    simp at hadd
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Std.UScalarTy.numBits]; omega
    unfold Canonical
    rw [← hadd]
    show (Std.UScalar.cast .U16 w).val < parameters.FIELD_MODULUS.val
    unfold parameters.FIELD_MODULUS
    simp
    rw [hwcast]; exact hwbnd
  | fail e =>
    rw [hxy] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hyval] at hae; omega
  | div => rw [hxy] at hae; exact hae.elim

/-- Canonicity preservation for `FieldElement.mul_pure`. Unconditional.

    Proof strategy: same shape as `Canonical_add_pure` but using
    `mul_equiv` and the `mul`-impl's U32 product `% q`. The `.fail`
    branch's panic-impossibility follows from
    `a.val * b.val ≤ (2^16-1)^2 < 2^32`. -/
theorem Canonical_mul_pure (a b : parameters.FieldElement) :
    Canonical (FieldElement.mul_pure a b) := by
  have hmul : parameters.FieldElement.mul a b = .ok (FieldElement.mul_pure a b) :=
    FieldElement.mul_eq_ok a b
  unfold parameters.FieldElement.mul at hmul
  simp only [lift, bind_tc_ok] at hmul
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.mul_equiv x y
  have heqmul : (x * y : Result Std.U32) = Std.UScalar.mul x y := rfl
  cases hxy : (x * y : Result Std.U32) with
  | ok z =>
    rw [hxy] at hmul
    rw [heqmul] at hxy
    rw [hxy] at hae; simp at hae
    obtain ⟨_, _, _⟩ := hae
    simp only [bind_tc_ok] at hmul
    have hmod_val :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329 := by
      unfold parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32 z m hmod_ne
    rw [hw_eq] at hmul; simp only [bind_tc_ok] at hmul
    unfold parameters.FieldElement.new at hmul
    simp at hmul
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Std.UScalarTy.numBits]; omega
    unfold Canonical
    rw [← hmul]
    show (Std.UScalar.cast .U16 w).val < parameters.FIELD_MODULUS.val
    unfold parameters.FIELD_MODULUS
    simp
    rw [hwcast]; exact hwbnd
  | fail e =>
    rw [heqmul] at hxy; rw [hxy] at hae
    simp only [Std.UScalar.max, Std.UScalarTy.numBits] at hae
    rw [hxval, hyval] at hae
    have : a.val.val * b.val.val < 2^32 := by
      have h1 : a.val.val * b.val.val ≤ (2^16 - 1) * (2^16 - 1) := by
        apply Nat.mul_le_mul <;> omega
      have heq : (2^16 - 1) * (2^16 - 1) = 2^32 - 2*2^16 + 1 := by decide
      omega
    omega
  | div => rw [heqmul] at hxy; rw [hxy] at hae; exact hae.elim

/-- Canonicity preservation for `FieldElement.sub_pure`. Requires both
    inputs canonical (the impl panics on non-canonical inputs — see
    `sub_eq_ok`'s precondition).

    Proof strategy: two-step do-block — first `x + q` (panic-impossible
    by `hb` canonical, since `x.val + q.val ≤ q.val + (q.val-1) < 2^32`),
    then `s - y` (panic-impossible by `hb` canonical, since
    `s.val = x.val + q.val ≥ q.val > y.val`), then `% q` and U16 cast
    as in `Canonical_add_pure`. -/
theorem Canonical_sub_pure (a b : parameters.FieldElement)
    (ha : Canonical a) (hb : Canonical b) :
    Canonical (FieldElement.sub_pure a b) := by
  have hsub : parameters.FieldElement.sub a b = .ok (FieldElement.sub_pure a b) :=
    FieldElement.sub_eq_ok a b ha hb
  unfold Canonical at ha hb
  unfold parameters.FIELD_MODULUS at ha hb
  simp at ha hb
  unfold parameters.FieldElement.sub at hsub
  simp only [lift, bind_tc_ok] at hsub
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  set q : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hqval : q.val = 3329 := by
    show (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329
    unfold parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.add_equiv x q
  cases hxq : (x + q : Result Std.U32) with
  | ok s =>
    rw [hxq] at hae hsub; simp at hae
    obtain ⟨_, hsval, _⟩ := hae
    simp only [bind_tc_ok] at hsub
    have hae2 := Std.UScalar.sub_equiv s y
    cases hsy : (s - y : Result Std.U32) with
    | ok u =>
      rw [hsy] at hae2 hsub; simp at hae2
      obtain ⟨_, _, _⟩ := hae2
      simp only [bind_tc_ok] at hsub
      have hq_ne : q.val ≠ 0 := by rw [hqval]; decide
      obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32 u q hq_ne
      rw [hw_eq] at hsub; simp only [bind_tc_ok] at hsub
      unfold parameters.FieldElement.new at hsub
      simp at hsub
      have hwbnd : w.val < 3329 := by
        rw [hwval, hqval]; exact Nat.mod_lt _ (by decide)
      have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
        apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
        simp [Std.UScalarTy.numBits]; omega
      unfold Canonical
      rw [← hsub]
      show (Std.UScalar.cast .U16 w).val < parameters.FIELD_MODULUS.val
      unfold parameters.FIELD_MODULUS
      simp
      rw [hwcast]; exact hwbnd
    | fail e =>
      rw [hsy] at hae2; simp at hae2
      rw [hsval, hxval, hqval, hyval] at hae2
      omega
    | div => rw [hsy] at hae2; exact hae2.elim
  | fail e =>
    rw [hxq] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hqval] at hae
    omega
  | div => rw [hxq] at hae; exact hae.elim

/-- Canonicity preservation for `FieldElement.neg_pure`. Requires
    the input canonical.

    Proof strategy: the impl does NOT widen to U32 — it computes
    `q - self.val` directly in U16 (panic-impossible by `ha`
    canonical, since `q.val > a.val.val`), then `% q` at U16 width
    via `uscalar_rem_ok_U16`. The output IS the U16 (no narrowing
    cast), so the canonical bound is direct from `hwbnd`. -/
theorem Canonical_neg_pure (a : parameters.FieldElement)
    (ha : Canonical a) :
    Canonical (FieldElement.neg_pure a) := by
  have hneg : parameters.FieldElement.neg a = .ok (FieldElement.neg_pure a) :=
    FieldElement.neg_eq_ok a ha
  unfold Canonical at ha
  unfold parameters.FIELD_MODULUS at ha
  simp at ha
  unfold parameters.FieldElement.neg at hneg
  have hA := a.val.hBounds
  simp [Std.UScalarTy.numBits] at hA
  have hqval : (parameters.FIELD_MODULUS : Std.U16).val = 3329 := by
    unfold parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.sub_equiv (parameters.FIELD_MODULUS : Std.U16) a.val
  cases hqa : ((parameters.FIELD_MODULUS : Std.U16) - a.val : Result Std.U16) with
  | ok i =>
    rw [hqa] at hae hneg; simp at hae
    obtain ⟨_, _, _⟩ := hae
    simp only [bind_tc_ok] at hneg
    have hq_ne : (parameters.FIELD_MODULUS : Std.U16).val ≠ 0 := by
      rw [hqval]; decide
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U16 i parameters.FIELD_MODULUS hq_ne
    rw [hw_eq] at hneg; simp only [bind_tc_ok] at hneg
    unfold parameters.FieldElement.new at hneg
    simp at hneg
    have hwbnd : w.val < 3329 := by
      rw [hwval, hqval]; exact Nat.mod_lt _ (by decide)
    unfold Canonical
    rw [← hneg]
    show w.val < parameters.FIELD_MODULUS.val
    unfold parameters.FIELD_MODULUS
    simp
    exact hwbnd
  | fail e =>
    rw [hqa] at hae; simp at hae
    rw [hqval] at hae
    omega
  | div => rw [hqa] at hae; exact hae.elim

end libcrux_iot_ml_kem.BitMlKem.SpecPure
