import keccak_verification.spec.hacspec_sha3
import keccak_verification.spec.createi

/-! ## Spec decomposition for compositional round proofs

We decompose `spec_round` (theta ∘ rho ∘ pi ∘ chi ∘ iota) into two stages
that match the implementation structure:
  1. `spec_theta` = theta step
  2. `spec_prc`   = rho ∘ pi ∘ chi ∘ iota (everything after theta)

The unrolled versions avoid `createi`/`Vector.mapM` which can't be
reduced by simp in the WP monad.
-/

-- Checked arithmetic reduction lemmas for Keccak indices (Fin 5, Fin 25).
-- These let simp reduce *?, +?, /?, %? without matching on concrete index values.

-- For Fin 25: 5 *? i, i +? k (k ≤ 4), i /? 5, i %? 5
-- For Fin 5: i +? k (k ≤ 4), i %? 5

-- Checked arithmetic for USize64 values known to be < 25.
-- All Keccak index arithmetic stays within this bound.

-- a.toBitVec.toNat = a.toNat for USize64
private theorem bv_eq_nat (a : USize64) : a.toBitVec.toNat = a.toNat := rfl

theorem usize25_mul (a b : USize64) (ha : a.toNat < 25) (hb : b.toNat < 25) :
    a *? b = pure (a * b) := by
  simp only [rust_primitives.ops.arith.Mul.mul, BitVec.umulOverflow, bv_eq_nat]
  have : a.toNat * b.toNat < 625 := Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega)
  simp only [show ¬ (a.toNat * b.toNat ≥ 2 ^ 64) from by omega,
    ↓reduceIte, decide_false, Bool.false_eq_true]

theorem usize25_add (a b : USize64) (ha : a.toNat < 25) (hb : b.toNat < 25) :
    a +? b = pure (a + b) := by
  simp only [rust_primitives.ops.arith.Add.add, BitVec.uaddOverflow, bv_eq_nat]
  simp only [show ¬ (a.toNat + b.toNat ≥ 2 ^ 64) from by omega,
    ↓reduceIte, decide_false, Bool.false_eq_true]

theorem usize25_div (a : USize64) (b : USize64) (ha : a.toNat < 25) (hb : b ≠ 0) :
    a /? b = pure (a / b) := by
  simp [rust_primitives.ops.arith.Div.div, hb]

theorem usize25_rem (a : USize64) (b : USize64) (ha : a.toNat < 25) (hb : b ≠ 0) :
    a %? b = pure (a % b) := by
  simp [rust_primitives.ops.arith.Rem.rem, hb]

-- Pure spec-level functions for each Keccak sub-step.
-- Used in both the unrolled spec definitions and createi_ofFn proofs.

def theta_col (state : RustArray u64 25) (x : Fin (5 : usize).toNat) : u64 :=
  have : (25 : usize).toNat = 25 := rfl
  have : (5 : usize).toNat = 5 := rfl
  state.toVec[5 * x.val]'(by omega) ^^^ state.toVec[5 * x.val + 1]'(by omega) ^^^
  state.toVec[5 * x.val + 2]'(by omega) ^^^ state.toVec[5 * x.val + 3]'(by omega) ^^^
  state.toVec[5 * x.val + 4]'(by omega)

def theta_d_val (c : Fin (5 : usize).toNat → u64) (x : Fin (5 : usize).toNat) : u64 :=
  have : (5 : usize).toNat = 5 := rfl
  c ⟨(x.val + 4) % 5, by omega⟩ ^^^
  UInt64.ofBitVec ((c ⟨(x.val + 1) % 5, by omega⟩).toBitVec.rotateLeft 1)

def theta_result (state : RustArray u64 25) (d : Fin (5 : usize).toNat → u64)
    (i : Fin (25 : usize).toNat) : u64 :=
  have : (5 : usize).toNat = 5 := rfl
  have : (25 : usize).toNat = 25 := rfl
  state.toVec[i.val] ^^^ d ⟨i.val / 5, by omega⟩

def rho_lane (state : RustArray u64 25) (i : Fin (25 : usize).toNat) : u64 :=
  have : (25 : usize).toNat = 25 := rfl
  UInt64.ofBitVec (state.toVec[i.val].toBitVec.rotateLeft
    (hacspec_sha3.keccak_f.RHO_OFFSETS.toVec[i.val]).toNat)

def pi_lane (rho : Fin (25 : usize).toNat → u64) (i : Fin (25 : usize).toNat) : u64 :=
  have : (25 : usize).toNat = 25 := rfl
  let x := i.val / 5; let y := i.val % 5
  rho ⟨5 * ((x + 3 * y) % 5) + x, by omega⟩

def chi_lane (pi : Fin (25 : usize).toNat → u64) (i : Fin (25 : usize).toNat) : u64 :=
  have : (25 : usize).toNat = 25 := rfl
  let x := i.val / 5; let y := i.val % 5
  pi i ^^^ ((~~~(pi ⟨5 * ((x + 1) % 5) + y, by omega⟩)) &&&
                 pi ⟨5 * ((x + 2) % 5) + y, by omega⟩)

/-- Spec theta step: just hacspec theta. -/
def spec_theta (state : RustArray u64 25) : RustM (RustArray u64 25) :=
  hacspec_sha3.keccak_f.theta state

/-- Spec theta, unrolled using pure lane functions (no createi/Vector.mapM).
    Downstream consumers unfold theta_col/theta_d_val/theta_result to get concrete expressions. -/
def spec_theta_unrolled (state : RustArray u64 25) : RustM (RustArray u64 25) :=
  have h25 : (25 : usize).toNat = 25 := rfl
  let r := theta_result state (theta_d_val (theta_col state))
  pure (RustArray.ofVec #v[
    r ⟨0, by omega⟩, r ⟨1, by omega⟩, r ⟨2, by omega⟩, r ⟨3, by omega⟩, r ⟨4, by omega⟩,
    r ⟨5, by omega⟩, r ⟨6, by omega⟩, r ⟨7, by omega⟩, r ⟨8, by omega⟩, r ⟨9, by omega⟩,
    r ⟨10, by omega⟩, r ⟨11, by omega⟩, r ⟨12, by omega⟩, r ⟨13, by omega⟩, r ⟨14, by omega⟩,
    r ⟨15, by omega⟩, r ⟨16, by omega⟩, r ⟨17, by omega⟩, r ⟨18, by omega⟩, r ⟨19, by omega⟩,
    r ⟨20, by omega⟩, r ⟨21, by omega⟩, r ⟨22, by omega⟩, r ⟨23, by omega⟩, r ⟨24, by omega⟩])

set_option maxHeartbeats 64000000 in
open Std.Do in
theorem spec_theta_unrolled_eq (state : RustArray u64 25) :
    spec_theta state = spec_theta_unrolled state := by
  unfold spec_theta hacspec_sha3.keccak_f.theta spec_theta_unrolled
  have h5 : (5 : usize).toNat = 5 := rfl
  have h25 : (25 : usize).toNat = 25 := rfl
  -- columns: createi → Vector.ofFn (theta_col state)
  rw [hacspec_sha3.createi_ofFn _ (theta_col state) (fun ⟨n, hn⟩ => by
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
      simp (config := { decide := true }) [hacspec_sha3.keccak_f.get, bind, pure, RustM.bind,
        getElemResult, theta_col, rust_primitives.ops.arith.Mul.mul,
        rust_primitives.ops.arith.Add.add, BitVec.umulOverflow]
    | n + 5, h => exact absurd (show n + 5 < 5 from h) (by omega))]
  simp only [RustM.bind, bind]
  -- d-values: createi → Vector.ofFn (theta_d_val (theta_col state))
  rw [hacspec_sha3.createi_ofFn _ (theta_d_val (theta_col state)) (fun ⟨n, hn⟩ => by
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
      simp (config := { decide := true }) [hacspec_sha3.keccak_f.get, bind, pure, RustM.bind,
        getElemResult, theta_d_val,
        rust_primitives.ops.arith.Mul.mul, rust_primitives.ops.arith.Add.add,
        rust_primitives.ops.arith.Rem.rem, BitVec.umulOverflow, BitVec.uaddOverflow,
        core_models.num.Impl_9.rotate_left, Vector.getElem_ofFn, h5]
    | n + 5, h => exact absurd (show n + 5 < 5 from h) (by omega))]
  simp only [RustM.bind, bind]
  -- result: createi → Vector.ofFn (theta_result state (theta_d_val (theta_col state)))
  rw [hacspec_sha3.createi_ofFn _ (theta_result state (theta_d_val (theta_col state)))
    (fun ⟨n, hn⟩ => by
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
    | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _
    | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ =>
      simp (config := { decide := true }) [bind, pure, RustM.bind, getElemResult,
        theta_result,
        rust_primitives.ops.arith.Div.div, BitVec.umulOverflow, BitVec.uaddOverflow,
        Vector.getElem_ofFn, h5, h25]
      <;> rfl
    | n + 25, h => exact absurd (show n + 25 < 25 from h) (by omega))]
  simp only [pure, Vector.ofFn]
  rfl

/-- Spec post-theta step: rho + pi + chi + iota. -/
def spec_prc (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let s ← hacspec_sha3.keccak_f.rho state
  let s ← hacspec_sha3.keccak_f.pi s
  let s ← hacspec_sha3.keccak_f.chi s
  hacspec_sha3.keccak_f.iota s round

/-- Spec prc, fully unrolled (fused rho+pi+chi+iota, no createi/Vector.mapM). -/
def spec_prc_unrolled (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let p0 := state.toVec[0]
  let p1 := UInt64.ofBitVec (state.toVec[15].toBitVec.rotateLeft 28)
  let p2 := UInt64.ofBitVec (state.toVec[5].toBitVec.rotateLeft 1)
  let p3 := UInt64.ofBitVec (state.toVec[20].toBitVec.rotateLeft 27)
  let p4 := UInt64.ofBitVec (state.toVec[10].toBitVec.rotateLeft 62)
  let p5 := UInt64.ofBitVec (state.toVec[6].toBitVec.rotateLeft 44)
  let p6 := UInt64.ofBitVec (state.toVec[21].toBitVec.rotateLeft 20)
  let p7 := UInt64.ofBitVec (state.toVec[11].toBitVec.rotateLeft 6)
  let p8 := UInt64.ofBitVec (state.toVec[1].toBitVec.rotateLeft 36)
  let p9 := UInt64.ofBitVec (state.toVec[16].toBitVec.rotateLeft 55)
  let p10 := UInt64.ofBitVec (state.toVec[12].toBitVec.rotateLeft 43)
  let p11 := UInt64.ofBitVec (state.toVec[2].toBitVec.rotateLeft 3)
  let p12 := UInt64.ofBitVec (state.toVec[17].toBitVec.rotateLeft 25)
  let p13 := UInt64.ofBitVec (state.toVec[7].toBitVec.rotateLeft 10)
  let p14 := UInt64.ofBitVec (state.toVec[22].toBitVec.rotateLeft 39)
  let p15 := UInt64.ofBitVec (state.toVec[18].toBitVec.rotateLeft 21)
  let p16 := UInt64.ofBitVec (state.toVec[8].toBitVec.rotateLeft 45)
  let p17 := UInt64.ofBitVec (state.toVec[23].toBitVec.rotateLeft 8)
  let p18 := UInt64.ofBitVec (state.toVec[13].toBitVec.rotateLeft 15)
  let p19 := UInt64.ofBitVec (state.toVec[3].toBitVec.rotateLeft 41)
  let p20 := UInt64.ofBitVec (state.toVec[24].toBitVec.rotateLeft 14)
  let p21 := UInt64.ofBitVec (state.toVec[14].toBitVec.rotateLeft 61)
  let p22 := UInt64.ofBitVec (state.toVec[4].toBitVec.rotateLeft 18)
  let p23 := UInt64.ofBitVec (state.toVec[19].toBitVec.rotateLeft 56)
  let p24 := UInt64.ofBitVec (state.toVec[9].toBitVec.rotateLeft 2)
  let ch0 := p0 ^^^ ((~~~p5) &&& p10)
  let ch1 := p1 ^^^ ((~~~p6) &&& p11)
  let ch2 := p2 ^^^ ((~~~p7) &&& p12)
  let ch3 := p3 ^^^ ((~~~p8) &&& p13)
  let ch4 := p4 ^^^ ((~~~p9) &&& p14)
  let ch5 := p5 ^^^ ((~~~p10) &&& p15)
  let ch6 := p6 ^^^ ((~~~p11) &&& p16)
  let ch7 := p7 ^^^ ((~~~p12) &&& p17)
  let ch8 := p8 ^^^ ((~~~p13) &&& p18)
  let ch9 := p9 ^^^ ((~~~p14) &&& p19)
  let ch10 := p10 ^^^ ((~~~p15) &&& p20)
  let ch11 := p11 ^^^ ((~~~p16) &&& p21)
  let ch12 := p12 ^^^ ((~~~p17) &&& p22)
  let ch13 := p13 ^^^ ((~~~p18) &&& p23)
  let ch14 := p14 ^^^ ((~~~p19) &&& p24)
  let ch15 := p15 ^^^ ((~~~p20) &&& p0)
  let ch16 := p16 ^^^ ((~~~p21) &&& p1)
  let ch17 := p17 ^^^ ((~~~p22) &&& p2)
  let ch18 := p18 ^^^ ((~~~p23) &&& p3)
  let ch19 := p19 ^^^ ((~~~p24) &&& p4)
  let ch20 := p20 ^^^ ((~~~p0) &&& p5)
  let ch21 := p21 ^^^ ((~~~p1) &&& p6)
  let ch22 := p22 ^^^ ((~~~p2) &&& p7)
  let ch23 := p23 ^^^ ((~~~p3) &&& p8)
  let ch24 := p24 ^^^ ((~~~p4) &&& p9)
  let rc ← hacspec_sha3.keccak_f.ROUND_CONSTANTS[round]_?
  pure (RustArray.ofVec #v[ch0 ^^^ rc, ch1, ch2, ch3, ch4, ch5, ch6, ch7, ch8, ch9,
    ch10, ch11, ch12, ch13, ch14, ch15, ch16, ch17, ch18, ch19, ch20, ch21, ch22, ch23, ch24])

-- TODO: Proof passes standalone (lake env lean) but hits kernel deep recursion in lake build.
-- Fix: split into compositional rho_ofFn/pi_ofFn/chi_ofFn sub-lemmas to reduce proof term depth.
open Std.Do in
theorem spec_prc_unrolled_eq (state : RustArray u64 25) (round : usize)
    (hround : round.toNat < 24 := by omega) :
    spec_prc state round = spec_prc_unrolled state round := by
  sorry

/-- spec_round decomposes as spec_prc . spec_theta. -/
theorem spec_round_decomp (state : RustArray u64 25) (round : usize) :
    (do let s ← hacspec_sha3.keccak_f.theta state
        let s ← hacspec_sha3.keccak_f.rho s
        let s ← hacspec_sha3.keccak_f.pi s
        let s ← hacspec_sha3.keccak_f.chi s
        hacspec_sha3.keccak_f.iota s round) =
    (do let s ← spec_theta state
        spec_prc s round) := by
  unfold spec_theta spec_prc
  rfl
