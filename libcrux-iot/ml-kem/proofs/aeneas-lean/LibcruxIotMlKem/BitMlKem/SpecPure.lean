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

    Partial closure 2026-05-23: `add_eq_ok` and `mul_eq_ok` are
    UNCONDITIONALLY true because U32 widening prevents overflow
    in both cases (`a.val + b.val ≤ 2·(2^16 - 1) < 2^17 < 2^32`,
    `a.val * b.val ≤ (2^16 - 1)² < 2^32`).

    `sub_eq_ok` and `neg_eq_ok` are GENUINELY FALSE in the current
    extraction — the Rust source carries `#[refine(val < FIELD_MODULUS)]`
    on `parameters.FieldElement::new` (see
    `specs/ml-kem/src/parameters.rs:319`), but the Aeneas extraction
    drops the refinement, leaving the Lean `parameters.FieldElement`
    as `{ val : Std.U16 }` with any U16 admissible.

    Counterexamples (verified via `#eval`):
    * `parameters.FieldElement.sub ⟨0#u16⟩ ⟨65535#u16⟩ = .fail` —
      the impl computes `i = 0`, `i1 = 3329`, `i2 = 3329`, then
      `i2 - 65535` panics in U32.
    * `parameters.FieldElement.neg ⟨65535#u16⟩ = .fail` —
      the impl computes `3329 - 65535` directly in U16 (no widening),
      panicking immediately when `self.val > 3329`.

    STOP triggered per campaign discipline D.9 — awaiting decision:
    (a) add `(ha : a.val.val < q) (hb : b.val.val < q)` precondition
        to `sub_eq_ok` / `neg_eq_ok`, OR
    (b) strengthen `parameters.FieldElement` to carry the refinement
        (requires spec-side edit), OR
    (c) establish global canonicity invariant propagated through
        bit-side proofs.

    Option (a) is the smallest delta and matches the Rust contract;
    pending user decision. -/

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

-- `FieldElement.sub_eq_ok` and `FieldElement.neg_eq_ok` are BLOCKED;
-- see `STOP` block above. They are deliberately omitted (not added
-- as `sorry`) to keep the file's axiom report clean. Resume after
-- user decides between options (a) / (b) / (c).

end libcrux_iot_ml_kem.BitMlKem.SpecPure
