/-
  Tier 1.5 — project-local `Std.Associative` / `Std.Commutative`
  instances for `Std.UScalar.xor` / `and` / `or`.

  Aeneas registers projection laws (`UScalar.bv_xor` etc.) at
  `Aeneas/Std/Scalar/Bitwise.lean:274–281` but does **not** declare AC
  instances on `UScalar` itself, so `grind` cannot rotate
  `(a ^^^ b ^^^ c : Std.U64)` past `bv_xor`'s reach. We add those
  instances locally; an Aeneas-upstream PR is gated on extended
  in-tree stability and is not done here.

  Scope note (Stage 2 Step 6.5, ninth session): the original Step 6.5
  design also called for a typed `Lifted n` wrapper + 25-rotation
  lemma family. We built and tested it — the wrapper-level close
  worked on synthetic L6 but did not carry through the real
  post-mvcgen context (200+ hypotheses bloated `grind`). The actual
  L6 close in `ThetaLift.lean` is a one-line
  `simp only [Std.UScalarTy.U64_numBits_eq, ← lift_xor, ← lift_td]`.
  Per the user's call, we trim the speculative wrapper layer and keep
  only the demonstrably-useful AC instances; Step 7 (`PrcLift`) can
  reintroduce the wrapper if χ-nonlinearity actually demands it.
-/
import Aeneas.Std.Scalar.Bitwise

open Aeneas Aeneas.Std

instance {ty : Std.UScalarTy} : Std.Associative (α := Std.UScalar ty) (· ^^^ ·) :=
  ⟨fun a b c => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_xor, BitVec.xor_assoc]⟩

instance {ty : Std.UScalarTy} : Std.Commutative (α := Std.UScalar ty) (· ^^^ ·) :=
  ⟨fun a b => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_xor, BitVec.xor_comm]⟩

instance {ty : Std.UScalarTy} : Std.Associative (α := Std.UScalar ty) (· &&& ·) :=
  ⟨fun a b c => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_and, BitVec.and_assoc]⟩

instance {ty : Std.UScalarTy} : Std.Commutative (α := Std.UScalar ty) (· &&& ·) :=
  ⟨fun a b => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_and, BitVec.and_comm]⟩

instance {ty : Std.UScalarTy} : Std.Associative (α := Std.UScalar ty) (· ||| ·) :=
  ⟨fun a b c => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_or, BitVec.or_assoc]⟩

instance {ty : Std.UScalarTy} : Std.Commutative (α := Std.UScalar ty) (· ||| ·) :=
  ⟨fun a b => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_or, BitVec.or_comm]⟩
