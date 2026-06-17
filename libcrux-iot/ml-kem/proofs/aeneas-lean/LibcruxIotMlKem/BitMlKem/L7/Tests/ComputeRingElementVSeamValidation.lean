/-
  # L7.3 `compute_ring_element_v` — per-seam numerical validation harness.

  Validates each INTERNAL seam of `matrix.compute_ring_element_v` by
  running impl and hacspec spec step-by-step and pinning the exact
  per-lane Montgomery R-factor at each boundary.

  Impl chain (matrix.compute_ring_element_v, K=2):
    accumulator → reducing_from_i32_array → invert_ntt_montgomery
                → add_message_error_reduce  (= result3, the returned poly)
  where `add_message_error_reduce(self:=error_2, message, result:=result2)`
  computes per lane: result3 = barrett( montgomery_mul_by_const(result2,1441)
                                          + (error_2 + message) ).

  Hacspec chain (matrix.compute_ring_element_v):
    inner = multiply_vectors t r;  inv = ntt_inverse inner;
    a = add_polynomials inv error_2;  result = add_polynomials a message.

  Validated factors (spec_lane = factor · impl_lane, ALL 256 lanes, K=2):
    SEAM 1  reducing_from_i32_array out (lift result1)  vs  multiply_vectors
            → factor 2285 = R = 2¹⁶ mod q.
    SEAM 2  invert_ntt_montgomery out (lift result2)    vs  ntt_inverse
            → factor 512 = 1441·169 mod q.
    TAIL    add_message_error_reduce out (lift result3) vs
            add_polynomials(add_polynomials(scaleZ 512 (lift result2), e2), msg)
            → factor 1 (the FC tail bridge D').

  Why TAIL factor = 1:  `montgomery_multiply_by_constant(x,1441) ≡ 512·x` in
  canonical ZMod (1441·169 ≡ 512). So impl result3 = 512·result2 + e2 + msg.
  Hacspec inv = ntt_inverse(t·r) = 512·result2 (SEAM 2), hence hacspec result
  = inv + e2 + msg = 512·result2 + e2 + msg.

  TAIL PRE-bounds: e2, msg, result2 lanes are all chosen in [0,3328] so that
  (error_2 + message).natAbs ≤ 29439 and result2.natAbs ≤ 32767 hold.

  All `#guard`s must hold (build fails on regression). Run:
    lake build LibcruxIotMlKem.BitMlKem.L7.Tests.ComputeRingElementVSeamValidation
  Not imported by the root library.
-/
import LibcruxIotMlKem.BitMlKem.FCTargets

open CoreModels Aeneas Aeneas.Std
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.BitMlKem
open libcrux_iot_ml_kem.BitMlKem.FCTargets

namespace libcrux_iot_ml_kem.BitMlKem.L7.Tests.SeamV

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

-- K=2 input data. t-vector (t0,t1), r-vector (r0,r1), error_2 (e2), message (msg).
def t0 (j:Nat):Int := (j%17)
def t1 (j:Nat):Int := (j%13)+1
def r0 (j:Nat):Int := (j%11)+1
def r1 (j:Nat):Int := (j%7)+2
-- TAIL inputs, all lanes in [0,3328] so add_message_error_reduce PRE holds.
def e2  (j:Nat):Int := (j%29)+1
def msg (j:Nat):Int := (j%19)+3
def result2fn (j:Nat):Int := (j%251)+5

def tArr := Std.Array.make 2#usize [mkPoly t0, mkPoly t1] (by simp)
def rArr := Std.Array.make 2#usize [mkPoly r0, mkPoly r1] (by simp)

/-- 256 ZMod lanes of an impl `result` poly (i16 .val cast to ZMod 3329 = lift_poly). -/
def implP (r : Result (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)) : List (ZMod 3329) :=
  match r with
  | .ok p => (List.range 256).map (fun j => let x : Int := ((p.coefficients.val[j/16]!).elements.val[j%16]!).val; (x : ZMod 3329))
  | _ => []
/-- 256 ZMod lanes of a hacspec FE-array result (via zmodOfFE). -/
def specZ (r : Result (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)) : List (ZMod 3329) :=
  match r with | .ok a => a.val.map zmodOfFE | _ => []

/-- `spec = factor · impl` on every lane (multiplicative form, robust to zero lanes). -/
def seamHolds (spec impl : List (ZMod 3329)) (factor : ZMod 3329) : Bool :=
  (List.range 256).all (fun j => decide ((spec.getD j 0) = factor * (impl.getD j 0)))

/-! ## SEAM 1 — inner product, factor 2285 (re-confirm). -/

/-- impl accumulator after the K=2 loop (L7.4 fallback path: compute_message_loop t r). -/
def acc2 : Std.Array Std.I32 256#usize :=
  match matrix.compute_message_loop (K:=2#usize) (vectortraitsOperationsInst:=portable_ops_inst)
    {start:=0#usize, «end»:=2#usize} tArr rArr accArr with
  | .ok a => a | _ => accArr
def result1R := polynomial.PolynomialRingElement.reducing_from_i32_array (vectortraitsOperationsInst:=portable_ops_inst) (Aeneas.Std.Array.to_slice acc2) (mkPoly (fun _=>0))
def result1 := match result1R with | .ok p => p | _ => mkPoly (fun _=>0)

def tFE := Std.Array.make 2#usize [mkFEArr t0, mkFEArr t1] (by simp)
def rFE := Std.Array.make 2#usize [mkFEArr r0, mkFEArr r1] (by simp)
def innerR := hacspec_ml_kem.matrix.multiply_vectors (RANK:=2#usize) tFE rFE

/-! ## SEAM 2 — ntt_inverse, factor 512 (from L7.4). -/

def result2R : Result (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) :=
  match invert_ntt.invert_ntt_montgomery (K:=2#usize) (vectortraitsOperationsInst:=portable_ops_inst) result1 (mkVec (fun _=>0)) with
  | .ok (p,_) => .ok p | .fail e => .fail e | .div => .div
def innerInvR := hacspec_ml_kem.invert_ntt.ntt_inverse (match innerR with | .ok a => a | _ => mkFEArr (fun _=>0))

/-! ## TAIL — add_message_error_reduce, factor 1 (THE new seam). -/

/-- A concrete canonical result2 (lanes ≤ 3328) — the SEAM-2 output is irrelevant
    here; we pin the tail factor at a fresh, in-range result2. -/
def result2c : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector := mkPoly result2fn

/-- impl tail: add_message_error_reduce(self:=error_2, message, result:=result2). -/
def result3R : Result (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) :=
  match polynomial.PolynomialRingElement.add_message_error_reduce (vectortraitsOperationsInst:=portable_ops_inst)
    (mkPoly e2) (mkPoly msg) result2c (mkVec (fun _=>0)) with
  | .ok (p,_) => .ok p | .fail er => .fail er | .div => .div

/-- hacspec tail at matching inputs: inv = 512·result2 (SEAM 2), then +e2, +msg. -/
def invFE : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  mkFEArr (fun j => ((512 * (result2fn j) : Int)))
def tailAR := hacspec_ml_kem.matrix.add_polynomials invFE (mkFEArr e2)
def tailOutR := hacspec_ml_kem.matrix.add_polynomials (match tailAR with | .ok a => a | _ => mkFEArr (fun _=>0)) (mkFEArr msg)

#guard seamHolds (specZ innerR)    (implP result1R) 2285   -- SEAM 1: multiply_vectors = R · result1
#guard seamHolds (specZ innerInvR) (implP result2R) 512    -- SEAM 2: ntt_inverse     = 512 · result2
#guard seamHolds (specZ tailOutR)  (implP result3R) 1      -- TAIL:  add_polys(add_polys(512·r2,e2),msg) = result3

-- visibility
#eval ("SEAM1 lane1 (spec, impl):", (specZ innerR).getD 1 0, (implP result1R).getD 1 0)
#eval ("SEAM2 lane1 (spec, impl):", (specZ innerInvR).getD 1 0, (implP result2R).getD 1 0)
#eval ("TAIL  lane1 (spec, impl):", (specZ tailOutR).getD 1 0, (implP result3R).getD 1 0)

end libcrux_iot_ml_kem.BitMlKem.L7.Tests.SeamV
