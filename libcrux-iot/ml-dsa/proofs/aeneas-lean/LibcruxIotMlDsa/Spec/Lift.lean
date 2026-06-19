import LibcruxIotMlDsa.Spec.Pure

/-!
# The lift bridge (impl Montgomery i32 → clean `Z_q`)

Analogue of ML-KEM's `Spec/Lift.lean`. The impl stores coefficients as signed,
possibly non-canonical **Montgomery-domain** `i32` lanes (8 per `Coefficients`
SIMD unit, 32 units per `PolynomialRingElement`). The clean spec
(`Spec/Pure.lean`) uses a flat 256-array of canonical `Z_q`. The lift maps the
former to the latter.

The **impl-independent** core (`liftZ`) lives here now. The **impl-shaped**
lifts (`lift_coeffs`, `lift_poly`, `lift_vec`, `lift_matrix`) reference the
extracted types in `Extraction/Funs.lean` and are authored in **Phase 1**, once
the extraction has run — they are sketched in the trailing block comment.
-/

namespace libcrux_iot_ml_dsa.Spec.Lift
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Spec

/-- Strip Montgomery from a signed coefficient: interpret the integer mod `q`,
    then multiply by `R⁻¹`. A Montgomery-domain value `x = a·R (mod q)` lifts to
    the clean `a`. -/
def liftZ (x : Int) : Zq := (x : Zq) * (Montgomery.RINV : Zq)

/-- `liftZ` of a plain (already-clean) integer is just its residue — used when a
    seam is asserted to be in the standard (non-Montgomery) domain. Distinguish
    the two via explicit per-seam `scaleZ`-style factors (SKILL §13.13). -/
def liftZ_std (x : Int) : Zq := (x : Zq)

/-
Phase-1 impl-shaped lifts (need `Extraction/Funs.lean`). Sketch:

    open Aeneas.Std

    /-- 8 lanes of one SIMD unit → 8 clean field elements. -/
    def lift_coeffs (u : …vector_type.Coefficients) : Array Zq :=
      ((List.range 8).map (fun j => liftZ (u.values.val[j]!).val)).toArray

    /-- 32 units × 8 lanes → flat 256-array (`simd_units_to_array` analogue). -/
    def lift_poly (re : …polynomial.PolynomialRingElement …) : Pure.SpecPoly :=
      Pure.build (fun i => liftZ ((re.simd_units.val[i / 8]!).values.val[i % 8]!).val)

    def lift_vec    {K} (v : Array (…PolynomialRingElement …) K) : Array Pure.SpecPoly K := …
    def lift_matrix {K L} (m : …) : … := …

  Decide per seam whether to use `liftZ` (mont-strip) or `liftZ_std`, and pin the
  residual `R`-factor with an `#eval`/`#guard` proxy check before proving
  (the ML-KEM L7 `scaleZ` discipline).
-/

end libcrux_iot_ml_dsa.Spec.Lift
