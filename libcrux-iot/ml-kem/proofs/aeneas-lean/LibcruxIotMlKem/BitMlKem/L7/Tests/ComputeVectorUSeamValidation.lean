/-
  # L7.2 `compute_vector_u` — per-seam numerical validation harness.

  Validates each INTERNAL seam of one per-row slice of
  `matrix.compute_vector_u` by running impl and hacspec spec step-by-step
  and pinning the exact per-lane Montgomery R-factor at each boundary.

  Per-output-row impl chain (matrix.compute_vector_u, output row i, K=2):
    accumulator (over j: aT[i][j]·r[j]) → reducing_from_i32_array
      → invert_ntt_montgomery → add_error_reduce  (= result_i, the row poly)
  where `add_error_reduce(self:=result2, error:=error_1[i])` computes per lane:
    result_i = barrett( montgomery_mul_by_const(result2, 1441) + error_1[i] ).

  Per-output-row hacspec chain (matrix.compute_vector_u, row i):
    result[i] = ntt_inverse( Σ_j aT[i][j]·r[j] ) + error_1[i]
              = add_polynomials (ntt_inverse (multiply_vectors aT_i r)) error_1[i].

  Validated factors (spec_lane = factor · impl_lane, ALL 256 lanes, K=2):
    SEAM 1  reducing_from_i32_array out (lift result1)  vs  multiply_vectors
            → factor 2285 = R = 2¹⁶ mod q.
    SEAM 2  invert_ntt_montgomery out (lift result2)    vs  ntt_inverse
            → factor 512 = 1441·169 mod q.
    TAIL    add_error_reduce out (lift result_i) vs
            add_polynomials(scaleZ 512 (lift result2), error_1[i])
            → factor 1 (the FC tail bridge D'', SINGLE-add).

  Why TAIL factor = 1:  `montgomery_multiply_by_constant(x,1441) ≡ 512·x` in
  canonical ZMod (1441·169 ≡ 512). So impl result_i = 512·result2 + error_1[i].
  Hacspec inv = ntt_inverse(aT_i·r) = 512·result2 (SEAM 2), hence hacspec
  result[i] = inv + error_1[i] = 512·result2 + error_1[i].

  TRANSPOSE / COLUMN-MAJOR RECONCILIATION (axiom-handled, excluded from PBT):
    Hacspec computes `transpose a` then `multiply_matrix_by_column`, so output
    row i uses `aT[i][j] = a[j][i]`. The impl samples `sample_matrix_entry
    matrix_entry seed 0 j` (the (i,j)-th sampled poly for row i). The bridge
    `lift_poly(sample(seed,i,j)) = (lift_matrix_from_seed seed K).val[j].val[i]`
    (column-major) is the `sample_matrix_entry_fc` axiom.
    `lift_matrix_from_seed` is noncomputable so the seed→matrix sampling /
    transpose convention CANNOT be tested numerically; it is excluded here
    and discharged by that axiom in the proof.

  TAIL PRE-bounds (`add_error_reduce_fc`):
    self (=result2) lanes .natAbs ≤ 32767, error_1[i] lanes .natAbs ≤ 29439.
    Both result2 and error_1[i] lanes here are chosen in [0,3328] so PRE holds.

  All `#guard`s must hold (build fails on regression). Run:
    lake build LibcruxIotMlKem.BitMlKem.L7.Tests.ComputeVectorUSeamValidation
  Not imported by the root library.
-/
import LibcruxIotMlKem.BitMlKem.FCTargets

open CoreModels Aeneas Aeneas.Std
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.BitMlKem
open libcrux_iot_ml_kem.BitMlKem.FCTargets

namespace libcrux_iot_ml_kem.BitMlKem.L7.Tests.SeamU

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

-- K=2 input data. Chosen matrix output-row aT_i = (m0,m1); r-vector (r0,r1);
-- per-row error error_1[i] (e1).
def m0 (j:Nat):Int := (j%17)
def m1 (j:Nat):Int := (j%13)+1
def r0 (j:Nat):Int := (j%11)+1
def r1 (j:Nat):Int := (j%7)+2
-- TAIL inputs, all lanes in [0,3328] so add_error_reduce PRE holds.
def e1       (j:Nat):Int := (j%29)+1
def result2fn (j:Nat):Int := (j%251)+5

def mArr := Std.Array.make 2#usize [mkPoly m0, mkPoly m1] (by simp)
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

/-! ## SEAM 1 — per-row inner product, factor 2285 (re-confirm). -/

/-- impl accumulator after the K=2 per-row loop (L7.4/L7.3 fallback path:
    compute_message_loop with secret:=matrix row (m0,m1), u:=r). -/
def acc2 : Std.Array Std.I32 256#usize :=
  match matrix.compute_message_loop (K:=2#usize) (vectortraitsOperationsInst:=portable_ops_inst)
    {start:=0#usize, «end»:=2#usize} mArr rArr accArr with
  | .ok a => a | _ => accArr
def result1R := polynomial.PolynomialRingElement.reducing_from_i32_array (vectortraitsOperationsInst:=portable_ops_inst) (Aeneas.Std.Array.to_slice acc2) (mkPoly (fun _=>0))
def result1 := match result1R with | .ok p => p | _ => mkPoly (fun _=>0)

def mFE := Std.Array.make 2#usize [mkFEArr m0, mkFEArr m1] (by simp)
def rFE := Std.Array.make 2#usize [mkFEArr r0, mkFEArr r1] (by simp)
def innerR := hacspec_ml_kem.matrix.multiply_vectors (RANK:=2#usize) mFE rFE

/-! ## SEAM 1b — fill-cache acc ≡ plain acc (loop0 specificity).

  `compute_vector_u_loop0` accumulates via `accumulating_ntt_multiply_fill_cache`
  (it ALSO populates the cache), whereas SEAM 1's proxy `compute_message_loop`
  uses the plain `accumulating_ntt_multiply`. Both carry the SAME
  `accumulating_ntt_multiply_poly_post` for the accumulator (FCTargets:27728 vs
  28537 — fill-cache merely ADDS a cache POST). This guard confirms numerically
  that, on identical (matrix-poly, r-poly) inputs, the fill-cache accumulator is
  byte-identical to the plain accumulator — so SEAM 1's factor-2285 pin transfers
  verbatim to the loop0 acc-bridge. The cache half is irrelevant to the acc seam. -/
def accFill : Std.Array Std.I32 256#usize :=
  match polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache
    (vectortraitsOperationsInst:=portable_ops_inst) (mkPoly m0) (mkPoly r0) accArr (mkPoly (fun _=>0)) with
  | .ok (a, _) => a | _ => accArr
def accPlain : Std.Array Std.I32 256#usize :=
  match polynomial.PolynomialRingElement.accumulating_ntt_multiply
    (vectortraitsOperationsInst:=portable_ops_inst) (mkPoly m0) (mkPoly r0) accArr with
  | .ok a => a | _ => accArr

#guard (List.range 256).all (fun j => decide (((accFill.val[j]!).val) = ((accPlain.val[j]!).val)))

/-! ## SEAM 2 — ntt_inverse, factor 512 (from L7.4/L7.3). -/

def result2R : Result (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) :=
  match invert_ntt.invert_ntt_montgomery (K:=2#usize) (vectortraitsOperationsInst:=portable_ops_inst) result1 (mkVec (fun _=>0)) with
  | .ok (p,_) => .ok p | .fail e => .fail e | .div => .div
def innerInvR := hacspec_ml_kem.invert_ntt.ntt_inverse (match innerR with | .ok a => a | _ => mkFEArr (fun _=>0))

/-! ## TAIL — add_error_reduce, factor 1 (THE new seam, single-add). -/

/-- A concrete canonical result2 (lanes ≤ 3328) — the SEAM-2 output is irrelevant
    here; we pin the tail factor at a fresh, in-range result2. -/
def result2c : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector := mkPoly result2fn

/-- impl tail: add_error_reduce(self:=result2, error:=error_1[i]). -/
def resultiR : Result (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) :=
  polynomial.PolynomialRingElement.add_error_reduce (vectortraitsOperationsInst:=portable_ops_inst)
    result2c (mkPoly e1)

/-- hacspec tail at matching inputs: inv = 512·result2 (SEAM 2), then + error_1[i]. -/
def invFE : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  mkFEArr (fun j => ((512 * (result2fn j) : Int)))
def tailOutR := hacspec_ml_kem.matrix.add_polynomials invFE (mkFEArr e1)

#guard seamHolds (specZ innerR)    (implP result1R) 2285   -- SEAM 1: multiply_vectors = R · result1
#guard seamHolds (specZ innerInvR) (implP result2R) 512    -- SEAM 2: ntt_inverse     = 512 · result2
#guard seamHolds (specZ tailOutR)  (implP resultiR) 1      -- TAIL:  add_polys(512·r2, e1) = result_i

-- visibility
#eval ("SEAM1 lane1 (spec, impl):", (specZ innerR).getD 1 0, (implP result1R).getD 1 0)
#eval ("SEAM2 lane1 (spec, impl):", (specZ innerInvR).getD 1 0, (implP result2R).getD 1 0)
#eval ("TAIL  lane1 (spec, impl):", (specZ tailOutR).getD 1 0, (implP resultiR).getD 1 0)

end libcrux_iot_ml_kem.BitMlKem.L7.Tests.SeamU
