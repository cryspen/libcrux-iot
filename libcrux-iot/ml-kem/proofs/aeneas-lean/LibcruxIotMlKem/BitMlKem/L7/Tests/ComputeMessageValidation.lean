/-
  # L7.4 `compute_message` — K=2/K=3 numerical validation harness.

  Validates the L7.4 grand equation
    `hacspec.matrix.compute_message (lift_poly v) (lift_vec secret) (lift_vec u)
       = .ok (lift_poly result3)`
  by RUNNING both the impl (`matrix.compute_message`, loop-based, #eval-reducible)
  and the hacspec spec on concrete inputs and comparing all 256 lanes in `ZMod 3329`.

  This validates that the full Montgomery R-factor chain nets correctly:
    accumulate (·169²)  →  ×2285 (lift_poly_mont→lift_poly bridge, 2285 = R = 169⁻¹)
       →  invert_ntt   →  ×512 (subtract_reduce: 1441·169)  →  canonical sub_polynomials.
  Confirmed constants (ZMod 3329): 169·2285 ≡ 1, 1441·169 ≡ 512, 2¹⁶ ≡ 2285.

  Both `#guard`s below must hold (build fails on regression). Run:
    lake build LibcruxIotMlKem.BitMlKem.L7.Tests.ComputeMessageValidation
  Not imported by the root library (manual/validation artifact).
-/
import LibcruxIotMlKem.BitMlKem.FCTargets

open CoreModels Aeneas Aeneas.Std
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.BitMlKem
open libcrux_iot_ml_kem.BitMlKem.FCTargets

namespace libcrux_iot_ml_kem.BitMlKem.L7.Tests

/-- Total i16 from an `Int` (wraps via `BitVec.ofInt`). -/
def mkI16 (n : Int) : Std.I16 := ⟨BitVec.ofInt 16 n⟩
def mkI32 (n : Int) : Std.I32 := ⟨BitVec.ofInt 32 n⟩
def len256 {α} (f : Nat → α) : ((List.range 256).map f).length = (256#usize).val := by
  simp only [List.length_map, List.length_range]; rfl
def len16 {α} (f : Nat → α) : ((List.range 16).map f).length = (16#usize).val := by
  simp only [List.length_map, List.length_range]; rfl

/-- Build a `PortableVector` (16 lanes) from a lane function. -/
def mkVec (f : Nat → Int) : vector.portable.vector_type.PortableVector :=
  { elements := Std.Array.make 16#usize ((List.range 16).map (fun i => mkI16 (f i))) (len16 _) }
/-- Build a `PolynomialRingElement` (256 lanes = 16 chunks × 16) from a lane function. -/
def mkPoly (f : Nat → Int) : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector :=
  { coefficients := Std.Array.make 16#usize ((List.range 16).map (fun c => mkVec (fun i => f (c*16+i)))) (len16 _) }
/-- Build the hacspec FE-array (256 lanes); equals `lift_poly`/`lift_vec` of `mkPoly`
    by definition since `lift_fe x = feOfZMod (x.val : ZMod 3329)`. -/
def mkFEArr (f : Nat → Int) : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize ((List.range 256).map (fun j => feOfZMod ((f j : ZMod 3329)))) (len256 _)
def accArr : Std.Array Std.I32 256#usize :=
  Std.Array.make 256#usize ((List.range 256).map (fun _ => mkI32 0)) (len256 _)

/-- Map a successful spec result to its 256 `ZMod 3329` lane values (`[]` on failure).
    Goes through `zmodOfFE` to avoid the noncomputable `Inhabited FieldElement`. -/
def specLanes (r : Result (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)) : List (ZMod 3329) :=
  match r with | .ok a => a.val.map zmodOfFE | _ => []
/-- Map a successful impl result's `result3` poly to its 256 `ZMod 3329` lane values. -/
def implLanes (r : Result (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector
      × vector.portable.vector_type.PortableVector × Std.Array Std.I32 256#usize)) : List (ZMod 3329) :=
  match r with
  | .ok (r3,_,_) => (List.range 256).map (fun j =>
      (((((r3.coefficients.val[j/16]!).elements.val[j%16]!).val) : Int) : ZMod 3329))
  | _ => []
def laneMismatches (spec impl : List (ZMod 3329)) : List Nat :=
  (List.range 256).filter (fun j => ! decide (spec.getD j 0 = impl.getD j 0))

/-! ## Confirmed R-constants (ZMod 3329). -/
#guard (169 * 2285 : ZMod 3329) = 1       -- 2285 = R = 169⁻¹ : the lift_poly_mont→lift_poly bridge
#guard (1441 * 169 : ZMod 3329) = 512     -- subtract_reduce's Montgomery constant
#guard ((2 : ZMod 3329) ^ 16) = 2285      -- R = 2¹⁶ mod q

/-! ## Case K=2 (small values). -/
def s2_0 (j:Nat):Int := (j%17)
def s2_1 (j:Nat):Int := (j%13)+1
def u2_0 (j:Nat):Int := (j%11)+1
def u2_1 (j:Nat):Int := (j%7)+2
def v2   (j:Nat):Int := (j%23)+1
def impl2 := matrix.compute_message (K := 2#usize) (vectortraitsOperationsInst := portable_ops_inst)
  (mkPoly v2)
  (Std.Array.make 2#usize [mkPoly s2_0, mkPoly s2_1] (by simp))
  (Std.Array.make 2#usize [mkPoly u2_0, mkPoly u2_1] (by simp))
  (mkPoly (fun _ => 0)) (mkVec (fun _ => 0)) accArr
def spec2 := hacspec_ml_kem.matrix.compute_message (RANK := 2#usize) (mkFEArr v2)
  (Std.Array.make 2#usize [mkFEArr s2_0, mkFEArr s2_1] (by simp))
  (Std.Array.make 2#usize [mkFEArr u2_0, mkFEArr u2_1] (by simp))

/-! ## Case K=3 (larger varied values, ≤ 3300). -/
def g (a b c : Nat) (j:Nat):Int := ((a*j + b*(j/16) + c) % 3301)
def v3 (j:Nat):Int := ((97*j + 13) % 3301)
def impl3 := matrix.compute_message (K := 3#usize) (vectortraitsOperationsInst := portable_ops_inst)
  (mkPoly v3)
  (Std.Array.make 3#usize [mkPoly (g 31 7 1), mkPoly (g 53 3 9), mkPoly (g 71 11 4)] (by simp))
  (Std.Array.make 3#usize [mkPoly (g 17 5 2), mkPoly (g 41 9 6), mkPoly (g 23 13 8)] (by simp))
  (mkPoly (fun _ => 0)) (mkVec (fun _ => 0)) accArr
def spec3 := hacspec_ml_kem.matrix.compute_message (RANK := 3#usize) (mkFEArr v3)
  (Std.Array.make 3#usize [mkFEArr (g 31 7 1), mkFEArr (g 53 3 9), mkFEArr (g 71 11 4)] (by simp))
  (Std.Array.make 3#usize [mkFEArr (g 17 5 2), mkFEArr (g 41 9 6), mkFEArr (g 23 13 8)] (by simp))

/-! ## The grand-equation checks (build fails if any lane mismatches). -/
#guard (laneMismatches (specLanes spec2) (implLanes impl2)).length = 0
#guard (laneMismatches (specLanes spec3) (implLanes impl3)).length = 0

-- Visibility (lane spot-checks):
#eval ((specLanes spec2).getD 0 0, (implLanes impl2).getD 0 0)   -- (1639, 1639)
#eval ((specLanes spec3).getD 100 0, (implLanes impl3).getD 100 0) -- (1130, 1130)

end libcrux_iot_ml_kem.BitMlKem.L7.Tests
