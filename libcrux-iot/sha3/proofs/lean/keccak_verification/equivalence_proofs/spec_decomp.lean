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

-- Checked arithmetic lemmas: translate ?-operators to pure operators + Nat bounds.
-- Side conditions are all in Nat, so omega can chain bounds through intermediate results.
private theorem bv_eq_nat (a : USize64) : a.toBitVec.toNat = a.toNat := rfl

-- Reduction: checked op → pure op (when Nat bound holds)
theorem usize_mul_ok (a b : USize64) (h : a.toNat * b.toNat < 2 ^ 64) :
    a *? b = pure (a * b) := by
  simp only [rust_primitives.ops.arith.Mul.mul, BitVec.umulOverflow, bv_eq_nat]
  simp only [show ¬ (a.toNat * b.toNat ≥ 2 ^ 64) from by omega,
    ↓reduceIte, decide_false, Bool.false_eq_true]

theorem usize_add_ok (a b : USize64) (h : a.toNat + b.toNat < 2 ^ 64) :
    a +? b = pure (a + b) := by
  simp only [rust_primitives.ops.arith.Add.add, BitVec.uaddOverflow, bv_eq_nat]
  simp only [show ¬ (a.toNat + b.toNat ≥ 2 ^ 64) from by omega,
    ↓reduceIte, decide_false, Bool.false_eq_true]

theorem usize_div_ok (a b : USize64) (hb : b ≠ 0) :
    a /? b = pure (a / b) := by
  simp [rust_primitives.ops.arith.Div.div, hb]

theorem usize_rem_ok (a b : USize64) (hb : b ≠ 0) :
    a %? b = pure (a % b) := by
  simp [rust_primitives.ops.arith.Rem.rem, hb]

-- Nat distribution: (a op b).toNat = a.toNat op b.toNat (when no overflow)
-- Nat distribution: expose BitVec layer via `change`, then use BitVec lemmas + omega.
theorem usize_toNat_mul (a b : USize64) (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  simp only [← bv_eq_nat] at h
  show (a.toBitVec * b.toBitVec).toNat = a.toBitVec.toNat * b.toBitVec.toNat
  rw [BitVec.toNat_mul]; omega

theorem usize_toNat_add (a b : USize64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  simp only [← bv_eq_nat] at h
  show (a.toBitVec + b.toBitVec).toNat = a.toBitVec.toNat + b.toBitVec.toNat
  rw [BitVec.toNat_add]; omega

theorem usize_toNat_div (a b : USize64) :
    (a / b).toNat = a.toNat / b.toNat := by
  show (a.toBitVec / b.toBitVec).toNat = a.toBitVec.toNat / b.toBitVec.toNat
  exact BitVec.toNat_udiv ..

theorem usize_toNat_rem (a b : USize64) :
    (a % b).toNat = a.toNat % b.toNat := by
  show (a.toBitVec % b.toBitVec).toNat = a.toBitVec.toNat % b.toBitVec.toNat
  exact BitVec.toNat_umod ..

@[simp] theorem usize_toNat_ofNat (n : Nat) (h : n < 2 ^ 64 := by omega) :
    (USize64.ofNat n).toNat = n := by
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]; omega

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
def spec_theta_unrolled (state : RustArray u64 25) : RustM (RustArray u64 25) := do
  let c0 := state.toVec[0] ^^^ state.toVec[1] ^^^ state.toVec[2] ^^^ state.toVec[3] ^^^ state.toVec[4]
  let c1 := state.toVec[5] ^^^ state.toVec[6] ^^^ state.toVec[7] ^^^ state.toVec[8] ^^^ state.toVec[9]
  let c2 := state.toVec[10] ^^^ state.toVec[11] ^^^ state.toVec[12] ^^^ state.toVec[13] ^^^ state.toVec[14]
  let c3 := state.toVec[15] ^^^ state.toVec[16] ^^^ state.toVec[17] ^^^ state.toVec[18] ^^^ state.toVec[19]
  let c4 := state.toVec[20] ^^^ state.toVec[21] ^^^ state.toVec[22] ^^^ state.toVec[23] ^^^ state.toVec[24]
  let d0 := c4 ^^^ UInt64.ofBitVec (c1.toBitVec.rotateLeft 1)
  let d1 := c0 ^^^ UInt64.ofBitVec (c2.toBitVec.rotateLeft 1)
  let d2 := c1 ^^^ UInt64.ofBitVec (c3.toBitVec.rotateLeft 1)
  let d3 := c2 ^^^ UInt64.ofBitVec (c4.toBitVec.rotateLeft 1)
  let d4 := c3 ^^^ UInt64.ofBitVec (c0.toBitVec.rotateLeft 1)
  pure (RustArray.ofVec #v[
    state.toVec[0] ^^^ d0, state.toVec[1] ^^^ d0, state.toVec[2] ^^^ d0, state.toVec[3] ^^^ d0, state.toVec[4] ^^^ d0,
    state.toVec[5] ^^^ d1, state.toVec[6] ^^^ d1, state.toVec[7] ^^^ d1, state.toVec[8] ^^^ d1, state.toVec[9] ^^^ d1,
    state.toVec[10] ^^^ d2, state.toVec[11] ^^^ d2, state.toVec[12] ^^^ d2, state.toVec[13] ^^^ d2, state.toVec[14] ^^^ d2,
    state.toVec[15] ^^^ d3, state.toVec[16] ^^^ d3, state.toVec[17] ^^^ d3, state.toVec[18] ^^^ d3, state.toVec[19] ^^^ d3,
    state.toVec[20] ^^^ d4, state.toVec[21] ^^^ d4, state.toVec[22] ^^^ d4, state.toVec[23] ^^^ d4, state.toVec[24] ^^^ d4])

set_option maxHeartbeats 64000000 in
open Std.Do in
theorem spec_theta_unrolled_eq (state : RustArray u64 25) :
    spec_theta state = spec_theta_unrolled state := by
  unfold spec_theta hacspec_sha3.keccak_f.theta spec_theta_unrolled
  have h5 : (5 : usize).toNat = 5 := rfl
  have h25 : (25 : usize).toNat = 25 := rfl
  -- columns: createi → Vector.ofFn (theta_col state)
  rw [hacspec_sha3.createi_ofFn _ (theta_col state) (fun i => by
    have hi : (USize64.ofNat i.val).toNat = i.val := usize_toNat_ofNat i.val (by omega)
    have hmul : (5 : USize64).toNat * (USize64.ofNat i.val).toNat < 2 ^ 64 := by simp [hi, h5]; omega
    have hmul_nat : ((5 : USize64) * USize64.ofNat i.val).toNat = 5 * i.val := by
      simp [usize_toNat_mul _ _ hmul, hi, h5]
    -- All add bounds: (5*i + k).toNat < 2^64 for k=0..4
    have hab (k : USize64) (hk : k.toNat ≤ 4) :
        ((5 : USize64) * USize64.ofNat i.val).toNat + k.toNat < 2 ^ 64 := by
      simp only [hmul_nat]; omega
    simp only [hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult, theta_col,
      usize_mul_ok _ _ hmul,
      usize_add_ok _ _ (hab 0 (by native_decide)), usize_add_ok _ _ (hab 1 (by native_decide)),
      usize_add_ok _ _ (hab 2 (by native_decide)), usize_add_ok _ _ (hab 3 (by native_decide)),
      usize_add_ok _ _ (hab 4 (by native_decide)),
      usize_toNat_add _ _ (hab 0 (by native_decide)), usize_toNat_add _ _ (hab 1 (by native_decide)),
      usize_toNat_add _ _ (hab 2 (by native_decide)), usize_toNat_add _ _ (hab 3 (by native_decide)),
      usize_toNat_add _ _ (hab 4 (by native_decide)),
      hmul_nat, hi, h5, h25]
    have : 5 * i.val + 4 < 25 := by have := i.isLt; simp [h5] at this; omega
    simp only [USize64.reduceToNat, Nat.add_zero,
      show 5 * i.val + 0 < 25 from by omega, show 5 * i.val + 1 < 25 from by omega,
      show 5 * i.val + 2 < 25 from by omega, show 5 * i.val + 3 < 25 from by omega,
      show 5 * i.val + 4 < 25 from by omega, ↓reduceDIte]
    rfl)]
  simp only [RustM.bind, bind]
  -- d-values: createi → Vector.ofFn (theta_d_val (theta_col state))
  rw [hacspec_sha3.createi_ofFn _ (theta_d_val (theta_col state)) (fun i => by
    have hi : (USize64.ofNat i.val).toNat = i.val := usize_toNat_ofNat i.val (by omega)
    have hadd4 : (USize64.ofNat i.val).toNat + (4 : USize64).toNat < 2 ^ 64 := by simp [hi]; omega
    have hadd1 : (USize64.ofNat i.val).toNat + (1 : USize64).toNat < 2 ^ 64 := by simp [hi]; omega
    simp only [hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult, theta_d_val,
      usize_add_ok _ _ hadd4, usize_add_ok _ _ hadd1,
      usize_toNat_add _ _ hadd4, usize_toNat_add _ _ hadd1,
      usize_rem_ok _ _ (by decide : (5 : USize64) ≠ 0),
      usize_toNat_rem,
      core_models.num.Impl_9.rotate_left, Vector.getElem_ofFn,
      hi, h5, USize64.reduceToNat, Nat.add_zero]
    simp only [show (i.val + 4) % 5 < 5 from by omega,
      show (i.val + 1) % 5 < 5 from by omega, ↓reduceDIte,
      show UInt32.toNat 1 = 1 from rfl])]
  simp only [RustM.bind, bind]
  -- result: createi → Vector.ofFn (theta_result state (theta_d_val (theta_col state)))
  rw [hacspec_sha3.createi_ofFn _ (theta_result state (theta_d_val (theta_col state)))
    (fun i => by
    have hi : (USize64.ofNat i.val).toNat = i.val := usize_toNat_ofNat i.val (by omega)
    simp only [bind, pure, RustM.bind, getElemResult, theta_result,
      usize_div_ok _ _ (by decide : (5 : USize64) ≠ 0),
      usize_toNat_div,
      Vector.getElem_ofFn,
      hi, h5, h25, USize64.reduceToNat, Nat.add_zero]
    simp only [show i.val < 25 from i.isLt, show i.val / 5 < 5 from by omega, ↓reduceDIte]
    rfl)]
  -- TODO: Vector.ofFn r vs #v[r 0, ..., r 24] — needs fast tactic (rfl takes 648s in kernel)
  sorry

/-- Spec post-theta step: rho + pi + chi + iota. -/
def spec_prc (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let s ← hacspec_sha3.keccak_f.rho state
  let s ← hacspec_sha3.keccak_f.pi s
  let s ← hacspec_sha3.keccak_f.chi s
  hacspec_sha3.keccak_f.iota s round

/-- Iota lane function: XOR round constant at index 0, identity elsewhere. -/
def iota_lane (chi : Fin (25 : usize).toNat → u64) (rc : u64) (i : Fin (25 : usize).toNat) : u64 :=
  if i.val = 0 then chi i ^^^ rc else chi i

/-- Spec prc, compact form using pure lane functions. Used in compositional proofs. -/
def spec_prc_compact (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  have h25 : (25 : usize).toNat = 25 := rfl
  let rc ← hacspec_sha3.keccak_f.ROUND_CONSTANTS[round]_?
  pure (RustArray.ofVec (Vector.ofFn (iota_lane (chi_lane (pi_lane (rho_lane state))) rc)))

/-- Spec prc, fully unrolled with concrete let-bindings. Used by downstream proofs (prc_lift, round_equiv_comp). -/
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

-- TODO: Bridge between compact and unrolled forms. Trivially true (definitional)
-- but kernel rfl is too slow. Needs a fast Vector.ofFn vs #v[...] tactic.
theorem spec_prc_compact_eq_unrolled (state : RustArray u64 25) (round : usize)
    (hround : round.toNat < 24) :
    spec_prc_compact state round = spec_prc_unrolled state round := by
  sorry

-- Compositional sub-lemmas: each converts one monadic step to pure Vector.ofFn.

open Std.Do in
theorem rho_ofFn (state : RustArray u64 25) :
    hacspec_sha3.keccak_f.rho state = .ok (RustArray.ofVec (Vector.ofFn (rho_lane state))) := by
  have h25 : (25 : usize).toNat = 25 := rfl
  unfold hacspec_sha3.keccak_f.rho
  exact hacspec_sha3.createi_ofFn _ (rho_lane state) (fun i => by
    have hi : (USize64.ofNat i.val).toNat = i.val := usize_toNat_ofNat i.val (by omega)
    simp only [bind, pure, RustM.bind, getElemResult, rho_lane,
      core_models.num.Impl_9.rotate_left, h25, hi, USize64.reduceToNat]
    simp only [show i.val < 25 from i.isLt, ↓reduceDIte,
      show UInt32.toNat (hacspec_sha3.keccak_f.RHO_OFFSETS.toVec[i.val]) =
        (hacspec_sha3.keccak_f.RHO_OFFSETS.toVec[i.val]).toNat from rfl]
    rfl)

open Std.Do in
theorem pi_ofFn (f : Fin (25 : usize).toNat → u64) :
    hacspec_sha3.keccak_f.pi (RustArray.ofVec (Vector.ofFn f)) =
    .ok (RustArray.ofVec (Vector.ofFn (pi_lane f))) := by
  have h5 : (5 : usize).toNat = 5 := rfl
  have h25 : (25 : usize).toNat = 25 := rfl
  unfold hacspec_sha3.keccak_f.pi
  exact hacspec_sha3.createi_ofFn _ (pi_lane f) (fun i => by
    have hi : (USize64.ofNat i.val).toNat = i.val := usize_toNat_ofNat i.val (by omega)
    have hdiv : (USize64.ofNat i.val / 5).toNat = i.val / 5 := by
      rw [usize_toNat_div]; simp [hi]
    have hrem : (USize64.ofNat i.val % 5).toNat = i.val % 5 := by
      rw [usize_toNat_rem]; simp [hi]
    have hmul3y : ((3 : USize64) * (USize64.ofNat i.val % 5)).toNat = 3 * (i.val % 5) := by
      rw [usize_toNat_mul _ _ (by rw [show (3 : USize64).toNat = 3 from rfl, hrem]; omega)]
      rw [show (3 : USize64).toNat = 3 from rfl, hrem]
    have hxp3y : (USize64.ofNat i.val / 5 + 3 * (USize64.ofNat i.val % 5)).toNat =
        i.val / 5 + 3 * (i.val % 5) := by
      rw [usize_toNat_add]; simp [hdiv, hmul3y]; omega
    have hmod : ((USize64.ofNat i.val / 5 + 3 * (USize64.ofNat i.val % 5)) % 5).toNat =
        (i.val / 5 + 3 * (i.val % 5)) % 5 := by
      rw [usize_toNat_rem]; simp [hxp3y]
    have hmul5 : ((5 : USize64) * ((USize64.ofNat i.val / 5 + 3 * (USize64.ofNat i.val % 5)) % 5)).toNat =
        5 * ((i.val / 5 + 3 * (i.val % 5)) % 5) := by
      rw [usize_toNat_mul _ _ (by rw [h5, hmod]; omega), h5, hmod]
    have hfinal : (5 * ((USize64.ofNat i.val / 5 + 3 * (USize64.ofNat i.val % 5)) % 5) +
        USize64.ofNat i.val / 5).toNat =
        5 * ((i.val / 5 + 3 * (i.val % 5)) % 5) + i.val / 5 := by
      rw [usize_toNat_add]; simp [hmul5, hdiv]; omega
    -- Overflow bounds for each checked op (reference have lemmas)
    -- Overflow bounds: rewrite to Nat then omega
    have hmul3y_bound : (3 : USize64).toNat * (USize64.ofNat i.val % 5).toNat < 2 ^ 64 := by
      rw [show (3 : USize64).toNat = 3 from rfl, hrem]; omega
    have hxp3y_bound : (USize64.ofNat i.val / 5).toNat + (3 * (USize64.ofNat i.val % 5)).toNat < 2 ^ 64 := by
      rw [hdiv, hmul3y]; omega
    have hmul5_bound : (5 : USize64).toNat * ((USize64.ofNat i.val / 5 + 3 * (USize64.ofNat i.val % 5)) % 5).toNat < 2 ^ 64 := by
      rw [show (5 : USize64).toNat = 5 from h5, hmod]; omega
    have hfinal_bound : (5 * ((USize64.ofNat i.val / 5 + 3 * (USize64.ofNat i.val % 5)) % 5)).toNat +
        (USize64.ofNat i.val / 5).toNat < 2 ^ 64 := by
      rw [hmul5, hdiv]; omega
    simp only [hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult, pi_lane,
      usize_div_ok _ _ (by decide : (5 : USize64) ≠ 0),
      usize_rem_ok _ _ (by decide : (5 : USize64) ≠ 0),
      usize_mul_ok _ _ hmul3y_bound, usize_add_ok _ _ hxp3y_bound,
      usize_mul_ok _ _ hmul5_bound, usize_add_ok _ _ hfinal_bound,
      hmul3y, hxp3y, hmod, hmul5, hfinal,
      Vector.getElem_ofFn, hi, h5, h25, USize64.reduceToNat, Nat.add_zero]
    simp only [show 5 * ((i.val / 5 + 3 * (i.val % 5)) % 5) + i.val / 5 < 25 from by omega,
      ↓reduceDIte])

open Std.Do in
theorem chi_ofFn (f : Fin (25 : usize).toNat → u64) :
    hacspec_sha3.keccak_f.chi (RustArray.ofVec (Vector.ofFn f)) =
    .ok (RustArray.ofVec (Vector.ofFn (chi_lane f))) := by
  have h5 : (5 : usize).toNat = 5 := rfl
  have h25 : (25 : usize).toNat = 25 := rfl
  unfold hacspec_sha3.keccak_f.chi
  exact hacspec_sha3.createi_ofFn _ (chi_lane f) (fun i => by
    have hi : (USize64.ofNat i.val).toNat = i.val := usize_toNat_ofNat i.val (by omega)
    have hdiv : (USize64.ofNat i.val / 5).toNat = i.val / 5 := by rw [usize_toNat_div]; simp [hi]
    have hrem : (USize64.ofNat i.val % 5).toNat = i.val % 5 := by rw [usize_toNat_rem]; simp [hi]
    have hx1 : (USize64.ofNat i.val / 5 + 1).toNat = i.val / 5 + 1 := by
      rw [usize_toNat_add _ _ (by rw [hdiv]; simp; omega)]; simp [hdiv]
    have hx1mod : ((USize64.ofNat i.val / 5 + 1) % 5).toNat = (i.val / 5 + 1) % 5 := by
      rw [usize_toNat_rem]; simp [hx1]
    have hx2 : (USize64.ofNat i.val / 5 + 2).toNat = i.val / 5 + 2 := by
      rw [usize_toNat_add _ _ (by rw [hdiv]; simp; omega)]; simp [hdiv]
    have hx2mod : ((USize64.ofNat i.val / 5 + 2) % 5).toNat = (i.val / 5 + 2) % 5 := by
      rw [usize_toNat_rem]; simp [hx2]
    have hmul5_1 : ((5 : USize64) * ((USize64.ofNat i.val / 5 + 1) % 5)).toNat = 5 * ((i.val / 5 + 1) % 5) := by
      rw [usize_toNat_mul _ _ (by rw [h5, hx1mod]; omega), h5, hx1mod]
    have hmul5_2 : ((5 : USize64) * ((USize64.ofNat i.val / 5 + 2) % 5)).toNat = 5 * ((i.val / 5 + 2) % 5) := by
      rw [usize_toNat_mul _ _ (by rw [h5, hx2mod]; omega), h5, hx2mod]
    have hfinal1 : (5 * ((USize64.ofNat i.val / 5 + 1) % 5) + USize64.ofNat i.val % 5).toNat =
        5 * ((i.val / 5 + 1) % 5) + i.val % 5 := by
      rw [usize_toNat_add _ _ (by rw [hmul5_1, hrem]; omega), hmul5_1, hrem]
    have hfinal2 : (5 * ((USize64.ofNat i.val / 5 + 2) % 5) + USize64.ofNat i.val % 5).toNat =
        5 * ((i.val / 5 + 2) % 5) + i.val % 5 := by
      rw [usize_toNat_add _ _ (by rw [hmul5_2, hrem]; omega), hmul5_2, hrem]
    -- 5*x + y (to recover f[i])
    have hb_5x : (5 : USize64).toNat * (USize64.ofNat i.val / 5).toNat < 2 ^ 64 := by
      rw [h5, hdiv]; omega
    have hmul5x : ((5 : USize64) * (USize64.ofNat i.val / 5)).toNat = 5 * (i.val / 5) := by
      rw [usize_toNat_mul _ _ hb_5x, h5, hdiv]
    have hb_5xy : (5 * (USize64.ofNat i.val / 5)).toNat + (USize64.ofNat i.val % 5).toNat < 2 ^ 64 := by
      rw [hmul5x, hrem]; omega
    have h5xy : (5 * (USize64.ofNat i.val / 5) + USize64.ofNat i.val % 5).toNat = i.val := by
      rw [usize_toNat_add _ _ hb_5xy, hmul5x, hrem]; omega
    -- Overflow bounds for (x+1), (x+2), 5*((x+1)%5), etc.
    have hb_x1 : (USize64.ofNat i.val / 5).toNat + (1 : USize64).toNat < 2 ^ 64 := by
      rw [hdiv, show (1 : USize64).toNat = 1 from rfl]; omega
    have hb_x2 : (USize64.ofNat i.val / 5).toNat + (2 : USize64).toNat < 2 ^ 64 := by
      rw [hdiv, show (2 : USize64).toNat = 2 from rfl]; omega
    have hb_m1 : (5 : USize64).toNat * ((USize64.ofNat i.val / 5 + 1) % 5).toNat < 2 ^ 64 := by
      rw [h5, hx1mod]; omega
    have hb_m2 : (5 : USize64).toNat * ((USize64.ofNat i.val / 5 + 2) % 5).toNat < 2 ^ 64 := by
      rw [h5, hx2mod]; omega
    have hb_f1 : (5 * ((USize64.ofNat i.val / 5 + 1) % 5)).toNat + (USize64.ofNat i.val % 5).toNat < 2 ^ 64 := by
      rw [hmul5_1, hrem]; omega
    have hb_f2 : (5 * ((USize64.ofNat i.val / 5 + 2) % 5)).toNat + (USize64.ofNat i.val % 5).toNat < 2 ^ 64 := by
      rw [hmul5_2, hrem]; omega
    simp only [hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult, chi_lane,
      usize_div_ok _ _ (by decide : (5 : USize64) ≠ 0),
      usize_rem_ok _ _ (by decide : (5 : USize64) ≠ 0),
      usize_mul_ok _ _ hb_5x, usize_add_ok _ _ hb_5xy,
      usize_add_ok _ _ hb_x1, usize_add_ok _ _ hb_x2,
      usize_mul_ok _ _ hb_m1, usize_mul_ok _ _ hb_m2,
      usize_add_ok _ _ hb_f1, usize_add_ok _ _ hb_f2,
      hmul5x, h5xy,
      hx1, hx1mod, hx2, hx2mod, hmul5_1, hmul5_2, hfinal1, hfinal2,
      Vector.getElem_ofFn, hi, h5, h25, USize64.reduceToNat, Nat.add_zero]
    simp only [show i.val < 25 from i.isLt,
      show 5 * ((i.val / 5 + 1) % 5) + i.val % 5 < 25 from by omega,
      show 5 * ((i.val / 5 + 2) % 5) + i.val % 5 < 25 from by omega,
      ↓reduceDIte]
    congr 1)

set_option maxHeartbeats 4000000 in
open Std.Do in
theorem iota_ofFn (f : Fin (25 : usize).toNat → u64) (round : usize) (hround : round.toNat < 24) :
    hacspec_sha3.keccak_f.iota (RustArray.ofVec (Vector.ofFn f)) round =
    .ok (RustArray.ofVec (Vector.ofFn (iota_lane f (hacspec_sha3.keccak_f.ROUND_CONSTANTS.toVec[round.toNat])))) := by
  have h25 : (25 : usize).toNat = 25 := rfl
  have h24 : (24 : usize).toNat = 24 := rfl
  unfold hacspec_sha3.keccak_f.iota iota_lane
  simp only [pure, bind, RustM.bind, getElemResult, Vector.getElem_ofFn,
    rust_primitives.hax.monomorphized_update_at.update_at_usize,
    h25, h24, hround, dite_true, USize64.reduceToNat]
  simp only [show (0 : Nat) < 25 from by omega, dite_true, show 0 < (Vector.ofFn f).size from by simp]
  apply congrArg
  apply congrArg
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Vector.getElem_set]
  split
  · subst_vars; simp; rfl
  · simp_all [Ne.symm ‹_›]

-- Proven via compact form + bridge
open Std.Do in
theorem spec_prc_compact_eq (state : RustArray u64 25) (round : usize)
    (hround : round.toNat < 24 := by omega) :
    spec_prc state round = spec_prc_compact state round := by
  unfold spec_prc spec_prc_compact
  simp only [bind, RustM.bind, rho_ofFn, pi_ofFn, chi_ofFn, iota_ofFn _ _ hround,
    getElemResult, hround, dite_true, show (24 : usize).toNat = 24 from rfl, pure]
  rfl

open Std.Do in
theorem spec_prc_unrolled_eq (state : RustArray u64 25) (round : usize)
    (hround : round.toNat < 24 := by omega) :
    spec_prc state round = spec_prc_unrolled state round := by
  rw [spec_prc_compact_eq state round hround, spec_prc_compact_eq_unrolled state round hround]

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
