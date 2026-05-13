/-
  Minimal reproducer for the `0#uscalar` vs plain-`Nat 0` mismatch
  inside Triple posts that blocks `simp_all` / `grind` / `fcongr`.

  ## TL;DR root cause

  The reported phenomenon ("`0` displays as `0#uscalar`") is a
  pretty-printer artifact, NOT a UScalar-vs-Nat literal mismatch.

  The Aeneas notation
      notation:70 a:70 "#uscalar" => UScalar.mk (a)
  has a precedence bug: when pretty-printing
      UScalar.mk ((a.bv ^^^ d.bv).rotateLeft 0)
  it lacks parens around `(a.bv ^^^ d.bv).rotateLeft 0`, so the display
  collapses to
      (a.bv ^^^ d.bv).rotateLeft 0#uscalar
  which LOOKS LIKE `0` is a UScalar argument to BitVec.rotateLeft.
  In reality, the `#uscalar` is grabbing the outermost `UScalar.mk`
  wrapper around the ENTIRE `(...).rotateLeft 0` expression.

  ## What actually goes wrong with simp_all

  After `hax_mvcgen` and `simp_all [Equivalence.rot32]` on a chained-set
  FC cell-equation goal, simp:
    - DOES bridge `(0#u32).val ⇝ 0` (via `UScalar.ofNatCore_val_eq`)
    - DOES distribute `^^^`/`~~~`/`&&&` over `.bv` (via `UScalar.bv_xor` etc.)
    - DOES unfold `rot32`
  but does NOT decompose `v = ⟨BitVecExpr⟩` (a UScalar/U32 equality with
  `UScalar.mk` on the RHS) into `v.bv = BitVecExpr`. The chain hypothesis
  is at the `.bv` level; the goal is at the U32 level.

  The bridge lemma already exists in Aeneas:
      Std.UScalar.eq_equiv_bv_eq : x = y ↔ x.bv = y.bv
  but it is only tagged `@[bvify]`, NOT `@[simp]`. So `simp_all` skips it.

  ## Fix options (in order of preference)

  A. **Upstream:** add `@[simp]` to `Std.UScalar.eq_equiv_bv_eq`
     in `Aeneas/Std/Scalar/Core.lean:730`. This is the smallest
     diff and benefits all downstream proofs.

  B. **Local:** include `Std.UScalar.eq_equiv_bv_eq` in the simp set
     of the `prc_y_zeta_fc_proof` macro in `PrcLift.lean:191-203`.

  C. **Alternative:** add a new simp lemma
        UScalar.eq_mk_iff_bv_eq : v = ⟨e⟩ ↔ v.bv = e
     This is a strict specialisation of (A) and provides marginal
     benefit only (only fires when the RHS is literally `UScalar.mk e`).

  Related: HAX_AENEAS_PITFALLS.md L8 (different surface symptom,
  same underlying cause). Wishlist item L13#1.
-/
import LibcruxIotSha3.Equivalence.Lift
import LibcruxIotSha3.Equivalence.ThetaLift
import Hax

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3

namespace ScratchUScalarNat

-- ============================================================
-- Section 1: confirm `(0#u32).val ⇝ 0` works in isolation
-- (i.e., this is NOT the real bottleneck)
-- ============================================================

example (x : BitVec 32) : x.rotateLeft (0#u32 : Std.U32).val = x.rotateLeft 0 := by simp

example (x : BitVec 32) : x.rotateLeft (0#u32 : Std.U32).val = x.rotateLeft 0 := by
  simp only [Std.UScalar.ofNatCore_val_eq]

-- ============================================================
-- Section 2: the stuck-goal shape (no fix yet)
-- Reproduced via lean_run_code; commented out here.
-- ============================================================
/-
  example (a d v : Std.U32)
      (hchain : v.bv = (a ^^^ d).bv.rotateLeft (0#u32 : Std.U32).val) :
      v = Equivalence.rot32 (a ^^^ d) 0 := by
    simp_all [Equivalence.rot32]
  -- unsolved goals: v = (a.bv ^^^ d.bv).rotateLeft 0#uscalar
  -- (which is `v = UScalar.mk ((a.bv ^^^ d.bv).rotateLeft 0)` displayed
  -- with the broken-precedence #uscalar notation).
-/

-- ============================================================
-- Section 3: existing manual workaround
-- ============================================================

example (a d v : Std.U32)
    (hchain : v.bv = (a ^^^ d).bv.rotateLeft (0#u32 : Std.U32).val) :
    v = Equivalence.rot32 (a ^^^ d) 0 := by
  apply Std.U32.bv_eq_imp_eq
  simp_all

-- ============================================================
-- Section 4: PROPOSED FIX — just pass eq_equiv_bv_eq to simp_all
-- ============================================================

/-- Single-cell, plain rotation amount 0. -/
example (a d v : Std.U32)
    (hchain : v.bv = (a ^^^ d).bv.rotateLeft (0#u32 : Std.U32).val) :
    v = Equivalence.rot32 (a ^^^ d) 0 := by
  simp_all [Equivalence.rot32, Std.UScalar.eq_equiv_bv_eq]

/-- Single-cell, non-zero rotation amount. -/
example (a d v : Std.U32)
    (hchain : v.bv = (a ^^^ d).bv.rotateLeft (22#u32 : Std.U32).val) :
    v = Equivalence.rot32 (a ^^^ d) 22 := by
  simp_all [Equivalence.rot32, Std.UScalar.eq_equiv_bv_eq]

/-- The 5-cell chained-set goal (the actual PrcLift shape). -/
example (a0 a1 a2 a3 a4 d0 d1 d2 d3 d4 v0 v1 v2 v3 v4 : Std.U32)
    (hc0 : v0.bv = (a0 ^^^ d0).bv.rotateLeft (0#u32  : Std.U32).val)
    (hc1 : v1.bv = (a1 ^^^ d1).bv.rotateLeft (22#u32 : Std.U32).val)
    (hc2 : v2.bv = (a2 ^^^ d2).bv.rotateLeft (22#u32 : Std.U32).val)
    (hc3 : v3.bv = (a3 ^^^ d3).bv.rotateLeft (11#u32 : Std.U32).val)
    (hc4 : v4.bv = (a4 ^^^ d4).bv.rotateLeft (7#u32  : Std.U32).val) :
    v0 = Equivalence.rot32 (a0 ^^^ d0) 0 ∧
    v1 = Equivalence.rot32 (a1 ^^^ d1) 22 ∧
    v2 = Equivalence.rot32 (a2 ^^^ d2) 22 ∧
    v3 = Equivalence.rot32 (a3 ^^^ d3) 11 ∧
    v4 = Equivalence.rot32 (a4 ^^^ d4) 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [Equivalence.rot32, Std.UScalar.eq_equiv_bv_eq]

/-- A chi-formula cell equation (the actual PrcLift cell shape:
    `bx0 ^^^ ~~~bx1 &&& bx2`). -/
example (a0 a1 a2 d0 d1 d2 v : Std.U32)
    (hres : v.bv = (a0.bv ^^^ d0.bv).rotateLeft 0
              ^^^ (~~~ (a1.bv ^^^ d1.bv).rotateLeft 22)
                  &&& (a2.bv ^^^ d2.bv).rotateLeft 22) :
    v = Equivalence.rot32 (a0 ^^^ d0) 0 ^^^
        (~~~ Equivalence.rot32 (a1 ^^^ d1) 22) &&& Equivalence.rot32 (a2 ^^^ d2) 22 := by
  simp_all [Equivalence.rot32, Std.UScalar.eq_equiv_bv_eq,
            Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not]

-- ============================================================
-- Section 5: alternative fix — a new simp lemma
-- (works for the simple case but NOT for chi-formula cells)
-- ============================================================

@[simp]
theorem UScalar.eq_mk_iff_bv_eq {ty : UScalarTy}
    (v : UScalar ty) (e : BitVec ty.numBits) :
    v = ⟨e⟩ ↔ v.bv = e := by
  cases v; simp

/-- With UScalar.eq_mk_iff_bv_eq, the single-cell case closes without
    `eq_equiv_bv_eq`. -/
example (a d v : Std.U32)
    (hchain : v.bv = (a ^^^ d).bv.rotateLeft (0#u32 : Std.U32).val) :
    v = Equivalence.rot32 (a ^^^ d) 0 := by
  simp_all [Equivalence.rot32]

end ScratchUScalarNat
