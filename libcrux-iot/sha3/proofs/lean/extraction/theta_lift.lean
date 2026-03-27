import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import extraction.spec_decomp
import extraction.lift_defs
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## Theta lifting via pure algebraic bridge

1. theta_comp_spec_local (duplicated from step_equiv, 2M) gives d values
2. Pure algebraic bridge connects d values to spec_theta_unrolled(lift(s))
3. No hax_mvcgen on combined impl+spec — avoids term blowup
-/

-- Lifting lemmas (proven before irreducible)
private theorem lift_xor (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide
private theorem lift_td (cL0 cL1 cR0 cR1 : BitVec 32) :
    lift_lane_bv (cL0 ^^^ cR1.rotateLeft 1) (cL1 ^^^ cR0) =
    lift_lane_bv cL0 cL1 ^^^ (lift_lane_bv cR0 cR1).rotateLeft 1 := by
  unfold lift_lane_bv spread_to_even; bv_decide
-- Odd rotation by 1: z0/z1 swap
private theorem lift_rot1 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 1 = lift_lane_bv (z1.rotateLeft 1) z0 := by
  unfold lift_lane_bv spread_to_even; bv_decide
private theorem lift_xor5 (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0 ^^^ c0 ^^^ d0 ^^^ e0) (a1 ^^^ b1 ^^^ c1 ^^^ d1 ^^^ e1) =
    lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 ^^^ lift_lane_bv c0 c1 ^^^ lift_lane_bv d0 d1 ^^^ lift_lane_bv e0 e1 := by
  unfold lift_lane_bv spread_to_even; bv_decide
attribute [local irreducible] spread_to_even lift_lane_bv

-- Bridge: (lift s)[i] = UInt64.ofBitVec(lift_lane_bv(z0, z1)) without unfolding lift/lift_lane elsewhere
private theorem lift_getElem (s : KeccakState) (i : Nat) (hi : i < (25 : usize).toNat) :
    (lift s).toVec[i] =
    UInt64.ofBitVec (lift_lane_bv s.st.toVec[i]._0.toVec[0].toBitVec s.st.toVec[i]._0.toVec[1].toBitVec) := by
  unfold lift lift_lane
  show (RustArray.ofVec (Vector.ofFn _)).toVec[i] = _
  simp only [RustArray.toVec, Vector.getElem_ofFn]
  rfl

-- u32 toBitVec lemmas (needed for lift_xor matching after d-value substitution)
private theorem u32_xor_toBitVec (a b : UInt32) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl
private theorem u32_ofBitVec_toBitVec (x : BitVec 32) : (UInt32.ofBitVec x).toBitVec = x := rfl

-- u64 XOR distributes over ofBitVec
private theorem u64_ofBitVec_xor (a b : BitVec 64) : UInt64.ofBitVec (a ^^^ b) = UInt64.ofBitVec a ^^^ UInt64.ofBitVec b := rfl

-- u64 ofBitVec/toBitVec roundtrip
private theorem u64_toBitVec_ofBitVec (x : BitVec 64) : (UInt64.ofBitVec x).toBitVec = x := rfl

-- u64 toBitVec distributes over XOR (needed to reduce rotation arguments)
private theorem u64_xor_toBitVec (a b : UInt64) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

private abbrev lta (st_z0 st_z1 d_z0 d_z1 : u32) : u64 :=
  UInt64.ofBitVec (lift_lane_bv ((st_z0 ^^^ d_z0).toBitVec) ((st_z1 ^^^ d_z1).toBitVec))

def lift_theta_applied (s : KeccakState) : RustArray u64 25 :=
  let d := s.d; let st := s.st
  RustArray.ofVec #v[
    lta st.toVec[0]._0.toVec[0] st.toVec[0]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[1]._0.toVec[0] st.toVec[1]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[2]._0.toVec[0] st.toVec[2]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[3]._0.toVec[0] st.toVec[3]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[4]._0.toVec[0] st.toVec[4]._0.toVec[1] d.toVec[0]._0.toVec[0] d.toVec[0]._0.toVec[1],
    lta st.toVec[5]._0.toVec[0] st.toVec[5]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[6]._0.toVec[0] st.toVec[6]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[7]._0.toVec[0] st.toVec[7]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[8]._0.toVec[0] st.toVec[8]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[9]._0.toVec[0] st.toVec[9]._0.toVec[1] d.toVec[1]._0.toVec[0] d.toVec[1]._0.toVec[1],
    lta st.toVec[10]._0.toVec[0] st.toVec[10]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[11]._0.toVec[0] st.toVec[11]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[12]._0.toVec[0] st.toVec[12]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[13]._0.toVec[0] st.toVec[13]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[14]._0.toVec[0] st.toVec[14]._0.toVec[1] d.toVec[2]._0.toVec[0] d.toVec[2]._0.toVec[1],
    lta st.toVec[15]._0.toVec[0] st.toVec[15]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[16]._0.toVec[0] st.toVec[16]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[17]._0.toVec[0] st.toVec[17]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[18]._0.toVec[0] st.toVec[18]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[19]._0.toVec[0] st.toVec[19]._0.toVec[1] d.toVec[3]._0.toVec[0] d.toVec[3]._0.toVec[1],
    lta st.toVec[20]._0.toVec[0] st.toVec[20]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1],
    lta st.toVec[21]._0.toVec[0] st.toVec[21]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1],
    lta st.toVec[22]._0.toVec[0] st.toVec[22]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1],
    lta st.toVec[23]._0.toVec[0] st.toVec[23]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1],
    lta st.toVec[24]._0.toVec[0] st.toVec[24]._0.toVec[1] d.toVec[4]._0.toVec[0] d.toVec[4]._0.toVec[1]]

-- Duplicated theta_comp_proof macro (from step_equiv)
local macro "theta_comp_proof_local" : tactic =>
  `(tactic| (
    hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction]
    all_goals (first | intro h₁; subst h₁ | skip)
    all_goals simp (config := { decide := true }) only [getElemResult, core_models.ops.index.Index.index,
      ↓reduceDIte, USize64.reduceToNat, USize64.add_zero, USize64.toNat_zero, ↓reduceIte,
      USize64.toBitVec_ofNat, bind_pure_comp, pure_bind, USize64.reduceAdd, map_pure,
      Vector.size, Nat.zero_lt_succ, bind_pure, Std.Do.WP.pure, Vector.getElem_set,
      Std.Do.SPred.down_pure, rot32,
      show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl,
      show (2 : usize).toNat = 2 from rfl]
    all_goals (repeat' constructor)
    all_goals (first | subst_vars; rfl | rfl)))

set_option maxHeartbeats 2000000 in
open Std.Do in
private theorem theta_comp_spec_local (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜
      -- d[0].z0 = c[4].z0 ⊕ rot(c[1].z1, 1)
      r.d.toVec[0]._0.toVec[0] =
        (s.st.toVec[20]._0.toVec[0] ^^^ s.st.toVec[21]._0.toVec[0] ^^^
         s.st.toVec[22]._0.toVec[0] ^^^ s.st.toVec[23]._0.toVec[0] ^^^
         s.st.toVec[24]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[5]._0.toVec[1] ^^^ s.st.toVec[6]._0.toVec[1] ^^^
               s.st.toVec[7]._0.toVec[1] ^^^ s.st.toVec[8]._0.toVec[1] ^^^
               s.st.toVec[9]._0.toVec[1]) 1
      ∧
      -- d[0].z1 = c[4].z1 ⊕ c[1].z0
      r.d.toVec[0]._0.toVec[1] =
        (s.st.toVec[20]._0.toVec[1] ^^^ s.st.toVec[21]._0.toVec[1] ^^^
         s.st.toVec[22]._0.toVec[1] ^^^ s.st.toVec[23]._0.toVec[1] ^^^
         s.st.toVec[24]._0.toVec[1]) ^^^
        (s.st.toVec[5]._0.toVec[0] ^^^ s.st.toVec[6]._0.toVec[0] ^^^
         s.st.toVec[7]._0.toVec[0] ^^^ s.st.toVec[8]._0.toVec[0] ^^^
         s.st.toVec[9]._0.toVec[0])
      ∧
      -- d[1].z0 = c[0].z0 ⊕ rot(c[2].z1, 1)
      r.d.toVec[1]._0.toVec[0] =
        (s.st.toVec[0]._0.toVec[0] ^^^ s.st.toVec[1]._0.toVec[0] ^^^
         s.st.toVec[2]._0.toVec[0] ^^^ s.st.toVec[3]._0.toVec[0] ^^^
         s.st.toVec[4]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[10]._0.toVec[1] ^^^ s.st.toVec[11]._0.toVec[1] ^^^
               s.st.toVec[12]._0.toVec[1] ^^^ s.st.toVec[13]._0.toVec[1] ^^^
               s.st.toVec[14]._0.toVec[1]) 1
      ∧
      -- d[1].z1 = c[0].z1 ⊕ c[2].z0
      r.d.toVec[1]._0.toVec[1] =
        (s.st.toVec[0]._0.toVec[1] ^^^ s.st.toVec[1]._0.toVec[1] ^^^
         s.st.toVec[2]._0.toVec[1] ^^^ s.st.toVec[3]._0.toVec[1] ^^^
         s.st.toVec[4]._0.toVec[1]) ^^^
        (s.st.toVec[10]._0.toVec[0] ^^^ s.st.toVec[11]._0.toVec[0] ^^^
         s.st.toVec[12]._0.toVec[0] ^^^ s.st.toVec[13]._0.toVec[0] ^^^
         s.st.toVec[14]._0.toVec[0])
      ∧
      -- d[2].z0 = c[1].z0 ⊕ rot(c[3].z1, 1)
      r.d.toVec[2]._0.toVec[0] =
        (s.st.toVec[5]._0.toVec[0] ^^^ s.st.toVec[6]._0.toVec[0] ^^^
         s.st.toVec[7]._0.toVec[0] ^^^ s.st.toVec[8]._0.toVec[0] ^^^
         s.st.toVec[9]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[15]._0.toVec[1] ^^^ s.st.toVec[16]._0.toVec[1] ^^^
               s.st.toVec[17]._0.toVec[1] ^^^ s.st.toVec[18]._0.toVec[1] ^^^
               s.st.toVec[19]._0.toVec[1]) 1
      ∧
      -- d[2].z1 = c[1].z1 ⊕ c[3].z0
      r.d.toVec[2]._0.toVec[1] =
        (s.st.toVec[5]._0.toVec[1] ^^^ s.st.toVec[6]._0.toVec[1] ^^^
         s.st.toVec[7]._0.toVec[1] ^^^ s.st.toVec[8]._0.toVec[1] ^^^
         s.st.toVec[9]._0.toVec[1]) ^^^
        (s.st.toVec[15]._0.toVec[0] ^^^ s.st.toVec[16]._0.toVec[0] ^^^
         s.st.toVec[17]._0.toVec[0] ^^^ s.st.toVec[18]._0.toVec[0] ^^^
         s.st.toVec[19]._0.toVec[0])
      ∧
      -- d[3].z0 = c[2].z0 ⊕ rot(c[4].z1, 1)
      r.d.toVec[3]._0.toVec[0] =
        (s.st.toVec[10]._0.toVec[0] ^^^ s.st.toVec[11]._0.toVec[0] ^^^
         s.st.toVec[12]._0.toVec[0] ^^^ s.st.toVec[13]._0.toVec[0] ^^^
         s.st.toVec[14]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[20]._0.toVec[1] ^^^ s.st.toVec[21]._0.toVec[1] ^^^
               s.st.toVec[22]._0.toVec[1] ^^^ s.st.toVec[23]._0.toVec[1] ^^^
               s.st.toVec[24]._0.toVec[1]) 1
      ∧
      -- d[3].z1 = c[2].z1 ⊕ c[4].z0
      r.d.toVec[3]._0.toVec[1] =
        (s.st.toVec[10]._0.toVec[1] ^^^ s.st.toVec[11]._0.toVec[1] ^^^
         s.st.toVec[12]._0.toVec[1] ^^^ s.st.toVec[13]._0.toVec[1] ^^^
         s.st.toVec[14]._0.toVec[1]) ^^^
        (s.st.toVec[20]._0.toVec[0] ^^^ s.st.toVec[21]._0.toVec[0] ^^^
         s.st.toVec[22]._0.toVec[0] ^^^ s.st.toVec[23]._0.toVec[0] ^^^
         s.st.toVec[24]._0.toVec[0])
      ∧
      -- d[4].z0 = c[3].z0 ⊕ rot(c[0].z1, 1)
      r.d.toVec[4]._0.toVec[0] =
        (s.st.toVec[15]._0.toVec[0] ^^^ s.st.toVec[16]._0.toVec[0] ^^^
         s.st.toVec[17]._0.toVec[0] ^^^ s.st.toVec[18]._0.toVec[0] ^^^
         s.st.toVec[19]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[0]._0.toVec[1] ^^^ s.st.toVec[1]._0.toVec[1] ^^^
               s.st.toVec[2]._0.toVec[1] ^^^ s.st.toVec[3]._0.toVec[1] ^^^
               s.st.toVec[4]._0.toVec[1]) 1
      ∧
      -- d[4].z1 = c[3].z1 ⊕ c[0].z0
      r.d.toVec[4]._0.toVec[1] =
        (s.st.toVec[15]._0.toVec[1] ^^^ s.st.toVec[16]._0.toVec[1] ^^^
         s.st.toVec[17]._0.toVec[1] ^^^ s.st.toVec[18]._0.toVec[1] ^^^
         s.st.toVec[19]._0.toVec[1]) ^^^
        (s.st.toVec[0]._0.toVec[0] ^^^ s.st.toVec[1]._0.toVec[0] ^^^
         s.st.toVec[2]._0.toVec[0] ^^^ s.st.toVec[3]._0.toVec[0] ^^^
         s.st.toVec[4]._0.toVec[0])
      ∧
      -- st and i are preserved
      r.st = s.st ∧ r.i = s.i
    ⌝ ⦄ := by theta_comp_proof_local

-- After impl theta, lifted theta-applied state equals spec_theta_unrolled(lift(input))
set_option maxHeartbeats 16000000 in
open Std.Do in
theorem theta_lift_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
       let r_spec ← spec_theta_unrolled (lift s)
       pure (r_spec = lift_theta_applied r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  -- Step 1: Reduce spec_theta_unrolled (lift s) to pure (eliminating the spec bind)
  show ⦃⌜True⌝⦄
    (libcrux_iot_sha3.keccak.keccakf1600_round0_theta s >>= fun r_impl =>
      spec_theta_unrolled (lift s) >>= fun r_spec =>
      pure (r_spec = lift_theta_applied r_impl))
    ⦃PostCond.noThrow fun r => ⌜r⌝⦄
  conv in spec_theta_unrolled _ >>= _ => unfold spec_theta_unrolled; simp only [pure_bind]
  -- Step 2: Split bind — impl theta then pure algebraic check
  apply Triple.bind
  case hx => exact theta_comp_spec_local s
  case hf =>
    intro r
    apply Triple.pure
    rw [← SPred.entails_true_intro]
    exact SPred.pure_intro fun ⟨hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1, hd3z0, hd3z1, hd4z0, hd4z1, hst, _hi⟩ => by
      simp only [lift_theta_applied, lta, hst,
                  hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1, hd3z0, hd3z1, hd4z0, hd4z1,
                  lift_getElem, lift_xor, lift_td, lift_xor5, rot32,
                  u64_ofBitVec_xor, u64_toBitVec_ofBitVec, u64_xor_toBitVec,
                  u32_xor_toBitVec, u32_ofBitVec_toBitVec,
                  Std.Do.SPred.down_pure]
      change (⟨_⟩ : RustArray _ _) = ⟨_⟩
      all_goals (repeat' congr 1)
      all_goals simp only [← lift_xor5, lift_rot1]
