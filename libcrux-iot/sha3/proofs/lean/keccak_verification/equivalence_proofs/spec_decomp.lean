import keccak_verification.spec.hacspec_sha3
import keccak_verification.spec.createi
import keccak_verification.implementation.libcrux_iot_sha3

/-! ## Spec decomposition for compositional round proofs

We decompose `spec_round` (theta ∘ rho ∘ pi ∘ chi ∘ iota) into two stages
that match the implementation structure:
  1. `spec_theta` = theta step
  2. `spec_prc`   = rho ∘ pi ∘ chi ∘ iota (everything after theta)

The unrolled versions avoid `createi`/`Vector.mapM` which can't be
reduced by simp in the WP monad.
-/

/-- Spec theta step: just hacspec theta. -/
def spec_theta (state : RustArray u64 25) : RustM (RustArray u64 25) :=
  hacspec_sha3.keccak_f.theta state

/-- Spec theta, fully unrolled (no createi/Vector.mapM). -/
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

-- spec_theta_unrolled equals spec_theta.
set_option maxHeartbeats 32000000 in
open Std.Do in
theorem spec_theta_unrolled_eq (state : RustArray u64 25) :
    spec_theta state = spec_theta_unrolled state := by
  unfold spec_theta hacspec_sha3.keccak_f.theta spec_theta_unrolled
  -- First createi: column XOR (n=5). Each iteration accesses state[5x+y] for y=0..4.
  have hc := hacspec_sha3.createi_ofFn (n := 5) True
    (fun x => do
      let v0 ← hacspec_sha3.keccak_f.get state x 0
      let v1 ← hacspec_sha3.keccak_f.get state x 1
      let v01 ← pure (v0 ^^^ v1)
      let v2 ← hacspec_sha3.keccak_f.get state x 2
      let v012 ← pure (v01 ^^^ v2)
      let v3 ← hacspec_sha3.keccak_f.get state x 3
      let v0123 ← pure (v012 ^^^ v3)
      let v4 ← hacspec_sha3.keccak_f.get state x 4
      pure (v0123 ^^^ v4))
    (fun ⟨n, hn⟩ => by
      match n, hn with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
        simp [Triple, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
          ExceptT.run, Id.run, Except.pure, SPred.entails, SPred.down_pure,
          hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult,
          rust_primitives.ops.arith.Mul.mul, rust_primitives.ops.arith.Add.add]
        all_goals (first | trivial | simp_all)
      | n + 5, h => exact absurd (show n + 5 < 5 from h) (by omega))
    trivial
  rw [hc.2]; simp only [RustM.bind, bind]
  -- Second createi: d-values (n=5). Each iteration accesses c[(x+4)%5] and c[(x+1)%5].
  have hd := hacspec_sha3.createi_ofFn (n := 5) True
    (fun x => do
      let idx1 ← x +? 4
      let idx1 ← idx1 %? 5
      let cL ← (RustArray.ofVec (Vector.ofFn _))[idx1]_?
      let idx2 ← x +? 1
      let idx2 ← idx2 %? 5
      let cR ← (RustArray.ofVec (Vector.ofFn _))[idx2]_?
      let cR_rot ← core_models.num.Impl_9.rotate_left cR 1
      pure (cL ^^^ cR_rot))
    (fun ⟨n, hn⟩ => by
      match n, hn with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
        simp [Triple, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
          ExceptT.run, Id.run, Except.pure, SPred.entails, SPred.down_pure,
          hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult,
          rust_primitives.ops.arith.Mul.mul, rust_primitives.ops.arith.Add.add,
          rust_primitives.ops.arith.Rem.rem,
          core_models.num.Impl_9.rotate_left, RustM.ofTotal, Vector.getElem_ofFn,
          show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl]
        all_goals (first | trivial | simp_all)
      | n + 5, h => exact absurd (show n + 5 < 5 from h) (by omega))
    trivial
  rw [hd.2]; simp only [RustM.bind, bind]
  -- Third createi: result (n=25). Each iteration accesses state[idx] and d[idx/5].
  have hr := hacspec_sha3.createi_ofFn (n := 25) True
    (fun idx => do
      let v ← state[idx]_?
      let didx ← idx /? 5
      let dv ← (RustArray.ofVec (Vector.ofFn _))[didx]_?
      pure (v ^^^ dv))
    (fun ⟨n, hn⟩ => by
      match n, hn with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
        simp [Triple, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
          ExceptT.run, Id.run, Except.pure, SPred.entails, SPred.down_pure,
          hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult,
          rust_primitives.ops.arith.Mul.mul, rust_primitives.ops.arith.Add.add,
          rust_primitives.ops.arith.Rem.rem,
          core_models.num.Impl_9.rotate_left, RustM.ofTotal, Vector.getElem_ofFn,
          show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl]
        all_goals (first | trivial | simp_all)
      | n + 5, h => exact absurd (show n + 5 < 5 from h) (by omega))
    trivial
  rw [hr.2]
  -- Both sides are now .ok(concrete_array). Evaluate Vector.ofFn + RustM.ofTotal.
  simp only [pure, RustM.ofTotal, RustM.bind, bind,
    hacspec_sha3.keccak_f.get, getElemResult, core_models.ops.index.Index.index,
    core_models.num.Impl_9.rotate_left,
    show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl,
    Vector.getElem_ofFn]
  rfl

/-- Spec post-theta step: rho + pi + chi + iota. -/
def spec_prc (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let s ← hacspec_sha3.keccak_f.rho state
  let s ← hacspec_sha3.keccak_f.pi s
  let s ← hacspec_sha3.keccak_f.chi s
  hacspec_sha3.keccak_f.iota s round

/-- Spec prc, fully unrolled (fused rho+pi+chi+iota, no createi/Vector.mapM).
    Lane layout: p[i] = rotl(state[pi_src[i]], RHO_OFFSETS[pi_src[i]])
    then chi: ch[5x+y] = p[5x+y] ⊕ (¬p[5((x+1)%5)+y] ∧ p[5((x+2)%5)+y])
    then iota: ch[0] ⊕ RC[round] -/
def spec_prc_unrolled (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  -- rho + pi (fused): p[i] = rotl(state[pi_src[i]], rho_offset[pi_src[i]])
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
  -- chi: ch[5x+y] = p[5x+y] ⊕ (¬p[5((x+1)%5)+y] ∧ p[5((x+2)%5)+y])
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
  -- iota: XOR round constant into lane 0
  let rc ← hacspec_sha3.keccak_f.ROUND_CONSTANTS[round]_?
  pure (RustArray.ofVec #v[ch0 ^^^ rc, ch1, ch2, ch3, ch4, ch5, ch6, ch7, ch8, ch9,
    ch10, ch11, ch12, ch13, ch14, ch15, ch16, ch17, ch18, ch19, ch20, ch21, ch22, ch23, ch24])

-- spec_prc_unrolled equals spec_prc.
set_option maxHeartbeats 64000000 in
open Std.Do in
theorem spec_prc_unrolled_eq (state : RustArray u64 25) (round : usize)
    (hround : round.toNat < 24 := by omega) :
    spec_prc state round = spec_prc_unrolled state round := by
  unfold spec_prc spec_prc_unrolled
  -- rho: createi n=25, accesses state[idx] and RHO_OFFSETS[idx]
  unfold hacspec_sha3.keccak_f.rho
  have h_rho := hacspec_sha3.createi_ofFn (n := 25) True
    (fun idx => do
      let v ← state[idx]_?
      let off ← hacspec_sha3.keccak_f.RHO_OFFSETS[idx]_?
      core_models.num.Impl_9.rotate_left v off)
    (fun ⟨n, hn⟩ => by
      match n, hn with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
      | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _
      | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ =>
        simp [Triple, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
          ExceptT.run, Id.run, Except.pure, SPred.entails, SPred.down_pure,
          hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult,
          rust_primitives.ops.arith.Mul.mul, rust_primitives.ops.arith.Add.add,
          rust_primitives.ops.arith.Rem.rem, rust_primitives.ops.arith.Div.div,
          core_models.num.Impl_9.rotate_left, RustM.ofTotal, Vector.getElem_ofFn,
          show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl]
        all_goals (first | trivial | simp_all)
      | n + 25, h => exact absurd (show n + 25 < 25 from h) (by omega)) trivial
  rw [h_rho.2]; simp only [RustM.bind, bind]
  -- pi: createi n=25, accesses rho_result via get
  unfold hacspec_sha3.keccak_f.pi
  have h_pi := hacspec_sha3.createi_ofFn (n := 25) True
    (fun idx => do
      let x ← idx /? 5
      let y ← idx %? 5
      let src ← 3 *? y
      let src ← x +? src
      let src ← src %? 5
      hacspec_sha3.keccak_f.get (RustArray.ofVec (Vector.ofFn _)) src x)
    (fun ⟨n, hn⟩ => by
      match n, hn with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
      | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _
      | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ =>
        simp [Triple, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
          ExceptT.run, Id.run, Except.pure, SPred.entails, SPred.down_pure,
          hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult,
          rust_primitives.ops.arith.Mul.mul, rust_primitives.ops.arith.Add.add,
          rust_primitives.ops.arith.Rem.rem, rust_primitives.ops.arith.Div.div,
          core_models.num.Impl_9.rotate_left, RustM.ofTotal, Vector.getElem_ofFn,
          show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl]
        all_goals (first | trivial | simp_all)
      | n + 25, h => exact absurd (show n + 25 < 25 from h) (by omega)) trivial
  rw [h_pi.2]; simp only [RustM.bind, bind]
  -- chi: createi n=25, accesses pi_result via get
  unfold hacspec_sha3.keccak_f.chi
  have h_chi := hacspec_sha3.createi_ofFn (n := 25) True
    (fun idx => do
      let x ← idx /? 5
      let y ← idx %? 5
      let v ← hacspec_sha3.keccak_f.get (RustArray.ofVec (Vector.ofFn _)) x y
      let x1 ← x +? 1
      let x1 ← x1 %? 5
      let v1 ← hacspec_sha3.keccak_f.get (RustArray.ofVec (Vector.ofFn _)) x1 y
      let nv1 ← pure (~~~v1)
      let x2 ← x +? 2
      let x2 ← x2 %? 5
      let v2 ← hacspec_sha3.keccak_f.get (RustArray.ofVec (Vector.ofFn _)) x2 y
      let masked ← pure (nv1 &&& v2)
      pure (v ^^^ masked))
    (fun ⟨n, hn⟩ => by
      match n, hn with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
      | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _
      | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ =>
        simp [Triple, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
          ExceptT.run, Id.run, Except.pure, SPred.entails, SPred.down_pure,
          hacspec_sha3.keccak_f.get, bind, pure, RustM.bind, getElemResult,
          rust_primitives.ops.arith.Mul.mul, rust_primitives.ops.arith.Add.add,
          rust_primitives.ops.arith.Rem.rem, rust_primitives.ops.arith.Div.div,
          core_models.num.Impl_9.rotate_left, RustM.ofTotal, Vector.getElem_ofFn,
          show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl]
        all_goals (first | trivial | simp_all)
      | n + 25, h => exact absurd (show n + 25 < 25 from h) (by omega)) trivial
  rw [h_chi.2]; simp only [RustM.bind, bind]
  -- iota: no createi, just state[0] ^^^ ROUND_CONSTANTS[round]
  unfold hacspec_sha3.keccak_f.iota
  simp only [pure, bind, RustM.bind, RustM.ofTotal,
    getElemResult, core_models.ops.index.Index.index, Vector.getElem_ofFn,
    hacspec_sha3.keccak_f.get, core_models.num.Impl_9.rotate_left,
    rust_primitives.hax.monomorphized_update_at.update_at_usize,
    show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl,
    show (24 : usize).toNat = 24 from rfl]
  split <;> simp_all <;> omega

/-- spec_round decomposes as spec_prc ∘ spec_theta. -/
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
