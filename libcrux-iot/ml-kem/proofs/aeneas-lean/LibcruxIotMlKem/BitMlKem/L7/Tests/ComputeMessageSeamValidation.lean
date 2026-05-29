/-
  # L7.4 `compute_message` — per-CONTRACT (per-seam) numerical validation.

  Where `ComputeMessageValidation.lean` validates the END-TO-END grand equation,
  this file validates each INTERNAL seam by running the impl and hacspec spec
  STEP-BY-STEP (all per-step functions are computable) and pinning the exact
  per-lane Montgomery R-factor at each boundary. This is the per-contract
  property testing that end-to-end testing is structurally blind to — it is how
  the L7.4 intermediate-contract R-errors were diagnosed and the corrected
  contracts derived.

  Validated factors (spec_lane = factor · impl_lane, ALL 256 lanes, K=2):
    SEAM 1  reducing_from_i32_array out (lift_poly result1)  vs  multiply_vectors
            → factor 2285 = R = 2¹⁶ mod q.
    SEAM 2  invert_ntt_montgomery out (lift_poly result2)    vs  ntt_inverse
            → factor 512 = 1441·169 mod q.
    SEAM 3  subtract_reduce out (lift_poly result3)          vs  sub_polynomials
            → factor 1 (equal — this is the FC theorem).

  Consequences for the proof contracts:
    • multiply_vectors = R · lift_poly result1 = R² · poly_reducing_pure(acc2).
    • compute_message_acc_pure (canonical fold) = R² · poly_reducing_pure(acc2)
      (S1-agent finding) = multiply_vectors  ⟹  S3 acc-bridge is TRUE as stated.
    • S1 conjunct 2 `poly_reducing_pure(acc2) = compute_message_acc_pure` is FALSE
      (off by R² = 1353); must be restated with the R² factor (or against
      multiply_vectors).

  All `#guard`s below must hold (build fails on regression). Run:
    lake build LibcruxIotMlKem.BitMlKem.L7.Tests.ComputeMessageSeamValidation
  Not imported by the root library. Author: orchestrator (per-contract Phase 0c, 2026-05-29).
-/
import LibcruxIotMlKem.BitMlKem.FCTargets

open Aeneas Aeneas.Std
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.BitMlKem
open libcrux_iot_ml_kem.BitMlKem.FCTargets

namespace libcrux_iot_ml_kem.BitMlKem.L7.Tests.Seam

def mkI16 (n : Int) : Std.I16 := ⟨BitVec.ofInt 16 n⟩
def mkI32 (n : Int) : Std.I32 := ⟨BitVec.ofInt 32 n⟩
def len256 {α} (f : Nat → α) : ((List.range 256).map f).length = (256#usize).val := by
  simp only [List.length_map, List.length_range]; rfl
def len16 {α} (f : Nat → α) : ((List.range 16).map f).length = (16#usize).val := by
  simp only [List.length_map, List.length_range]; rfl
def mkVec (f : Nat → Int) : vector.portable.vector_type.PortableVector :=
  { elements := Std.Array.make 16#usize ((List.range 16).map (fun i => mkI16 (f i))) (len16 _) }
def mkPoly (f : Nat → Int) : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector :=
  { coefficients := Std.Array.make 16#usize ((List.range 16).map (fun c => mkVec (fun i => f (c*16+i)))) (len16 _) }
def mkFEArr (f : Nat → Int) : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize ((List.range 256).map (fun j => feOfZMod ((f j : ZMod 3329)))) (len256 _)
def accArr : Std.Array Std.I32 256#usize :=
  Std.Array.make 256#usize ((List.range 256).map (fun _ => mkI32 0)) (len256 _)

def s0 (j:Nat):Int := (j%17)
def s1 (j:Nat):Int := (j%13)+1
def u0 (j:Nat):Int := (j%11)+1
def u1 (j:Nat):Int := (j%7)+2
def v  (j:Nat):Int := (j%23)+1
def secretArr := Std.Array.make 2#usize [mkPoly s0, mkPoly s1] (by simp)
def uArr := Std.Array.make 2#usize [mkPoly u0, mkPoly u1] (by simp)

/-- impl accumulator after the K=2 loop. -/
def acc2 : Std.Array Std.I32 256#usize :=
  match matrix.compute_message_loop (K:=2#usize) (vectortraitsOperationsInst:=portable_ops_inst)
    {start:=0#usize, «end»:=2#usize} secretArr uArr accArr with
  | .ok a => a | _ => accArr
/-- 256 ZMod lanes of an impl `result` poly (i16 .val cast to ZMod 3329 = lift_poly). -/
def implP (r : Result (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)) : List (ZMod 3329) :=
  match r with
  | .ok p => (List.range 256).map (fun j => let x : Int := ((p.coefficients.val[j/16]!).elements.val[j%16]!).val; (x : ZMod 3329))
  | _ => []
/-- 256 ZMod lanes of a hacspec FE-array result (via zmodOfFE). -/
def specZ (r : Result (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)) : List (ZMod 3329) :=
  match r with | .ok a => a.val.map zmodOfFE | _ => []

-- impl steps
def result1R := polynomial.PolynomialRingElement.reducing_from_i32_array (vectortraitsOperationsInst:=portable_ops_inst) (Aeneas.Std.Array.to_slice acc2) (mkPoly (fun _=>0))
def result1 := match result1R with | .ok p => p | _ => mkPoly (fun _=>0)
def result2R : Result (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) :=
  match invert_ntt.invert_ntt_montgomery (K:=2#usize) (vectortraitsOperationsInst:=portable_ops_inst) result1 (mkVec (fun _=>0)) with
  | .ok (p,_) => .ok p | .fail e => .fail e | .div => .div
def result2 := match result2R with | .ok p => p | _ => mkPoly (fun _=>0)
def result3R := polynomial.PolynomialRingElement.subtract_reduce (vectortraitsOperationsInst:=portable_ops_inst) (mkPoly v) result2
-- spec steps
def secFE := Std.Array.make 2#usize [mkFEArr s0, mkFEArr s1] (by simp)
def uFE := Std.Array.make 2#usize [mkFEArr u0, mkFEArr u1] (by simp)
def innerR := hacspec_ml_kem.matrix.multiply_vectors (RANK:=2#usize) secFE uFE
def innerInvR := hacspec_ml_kem.invert_ntt.ntt_inverse (match innerR with | .ok a => a | _ => mkFEArr (fun _=>0))
def outR := hacspec_ml_kem.matrix.sub_polynomials (mkFEArr v) (match innerInvR with | .ok a => a | _ => mkFEArr (fun _=>0))

/-- `spec = factor · impl` on every lane (multiplicative form, robust to zero lanes). -/
def seamHolds (spec impl : List (ZMod 3329)) (factor : ZMod 3329) : Bool :=
  (List.range 256).all (fun j => decide ((spec.getD j 0) = factor * (impl.getD j 0)))

#guard seamHolds (specZ innerR)    (implP result1R) 2285   -- SEAM 1: multiply_vectors = R · result1
#guard seamHolds (specZ innerInvR) (implP result2R) 512    -- SEAM 2: ntt_inverse     = 512 · result2
#guard seamHolds (specZ outR)      (implP result3R) 1      -- SEAM 3: sub_polynomials = result3 (theorem)

-- visibility
#eval ("SEAM1 lane1 (spec, impl):", (specZ innerR).getD 1 0, (implP result1R).getD 1 0)
#eval ("SEAM2 lane1 (spec, impl):", (specZ innerInvR).getD 1 0, (implP result2R).getD 1 0)

end libcrux_iot_ml_kem.BitMlKem.L7.Tests.Seam
