/-
  Round-3 θ lift spec.

  Round 3's theta operates on a state in round-2 layout, i.e.
  `lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)`.
-/
import LibcruxIotSha3.Equivalence.ThetaLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

attribute [local irreducible] spread_to_even lift_lane_bv

local macro "theta_c3_proof" subfun:ident : tactic =>
  `(tactic|
    (unfold $subfun
     hax_mvcgen
     all_goals first
       | scalar_tac
       | (intros
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals first | assumption | (
            apply Eq.trans ‹_›
            congr 2
            apply Std.U32.bv_eq_imp_eq
            simp_all [Std.UScalar.bv_xor]))))

/-! ## Round-3 per-c-cell sub-function specs

XOR chain order matches the impl: `ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4`
in canonical position order 5*x, 5*x+1, ..., 5*x+4. Zetas follow
`impl_swap_k 3` (true iff position ∈ {1,4,6,7,10,11,13,15,17,19,23,24})
for c[x][0] reads. -/

@[spec]
private theorem theta_c_x0_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 0#usize
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x0_z0

@[spec]
private theorem theta_c_x0_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 1#usize
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x0_z1

@[spec]
private theorem theta_c_x1_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 0#usize
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x1_z0

@[spec]
private theorem theta_c_x1_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 1#usize
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[1]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x1_z1

@[spec]
private theorem theta_c_x2_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 0#usize
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[0]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x2_z0

@[spec]
private theorem theta_c_x2_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 1#usize
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[1]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x2_z1

@[spec]
private theorem theta_c_x3_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 0#usize
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x3_z0

@[spec]
private theorem theta_c_x3_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 1#usize
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x3_z1

@[spec]
private theorem theta_c_x4_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 0#usize
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x4_z0

@[spec]
private theorem theta_c_x4_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 1#usize
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!)) ⌝ ⦄ := by
  theta_c3_proof keccak.keccakf1600_round3_theta_c_x4_z1

set_option maxHeartbeats 1600000 in
@[spec]
private theorem theta_d_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ∧
        r.d.val[0]!.val[0]! =
          s.c.val[4]!.val[0]! ^^^ rot32 s.c.val[1]!.val[1]! 1 ∧
        r.d.val[0]!.val[1]! =
          s.c.val[4]!.val[1]! ^^^ s.c.val[1]!.val[0]! ∧
        r.d.val[1]!.val[0]! =
          s.c.val[0]!.val[0]! ^^^ rot32 s.c.val[2]!.val[1]! 1 ∧
        r.d.val[1]!.val[1]! =
          s.c.val[0]!.val[1]! ^^^ s.c.val[2]!.val[0]! ∧
        r.d.val[2]!.val[0]! =
          s.c.val[1]!.val[0]! ^^^ rot32 s.c.val[3]!.val[1]! 1 ∧
        r.d.val[2]!.val[1]! =
          s.c.val[1]!.val[1]! ^^^ s.c.val[3]!.val[0]! ∧
        r.d.val[3]!.val[0]! =
          s.c.val[2]!.val[0]! ^^^ rot32 s.c.val[4]!.val[1]! 1 ∧
        r.d.val[3]!.val[1]! =
          s.c.val[2]!.val[1]! ^^^ s.c.val[4]!.val[0]! ∧
        r.d.val[4]!.val[0]! =
          s.c.val[3]!.val[0]! ^^^ rot32 s.c.val[0]!.val[1]! 1 ∧
        r.d.val[4]!.val[1]! =
          s.c.val[3]!.val[1]! ^^^ s.c.val[0]!.val[0]! ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_theta_d
  hax_mvcgen
  all_goals first
    | scalar_tac
    | trivial
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       all_goals first | trivial | assumption | (
         simp only [Std.WP.predn] at *
         try apply Std.U32.bv_eq_imp_eq
         simp_all [Std.UScalar.bv_xor, rot32]))

set_option maxHeartbeats 4000000 in
theorem theta_comp_spec_local_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧
        r.d.val[0]!.val[0]! =
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ^^^
          rot32 (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
                 s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
                 s.st.val[9]!.val[1]!) 1 ∧
        r.d.val[0]!.val[1]! =
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ^^^
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!) ∧
        r.d.val[1]!.val[0]! =
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!) ^^^
          rot32 (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
                 s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[0]! ^^^
                 s.st.val[14]!.val[1]!) 1 ∧
        r.d.val[1]!.val[1]! =
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!) ^^^
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[0]!) ∧
        r.d.val[2]!.val[0]! =
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!) ^^^
          rot32 (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
                 s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[1]! ^^^
                 s.st.val[19]!.val[0]!) 1 ∧
        r.d.val[2]!.val[1]! =
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[1]!) ^^^
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!) ∧
        r.d.val[3]!.val[0]! =
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[0]!) ^^^
          rot32 (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
                 s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
                 s.st.val[24]!.val[0]!) 1 ∧
        r.d.val[3]!.val[1]! =
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[1]!) ^^^
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ∧
        r.d.val[4]!.val[0]! =
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!) ^^^
          rot32 (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[0]! ^^^
                 s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
                 s.st.val[4]!.val[0]!) 1 ∧
        r.d.val[4]!.val[1]! =
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!) ^^^
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_theta
  hax_mvcgen
  all_goals first
    | trivial
    | grind
    | simp_all

-- @[spec] (added when proof is filled in)
set_option maxHeartbeats 16000000 in
theorem theta_lift_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta s
    ⦃ ⇓ r_impl => ⌜
      r_impl.i = s.i ∧
      (do
        let r_spec ← keccak_f.theta_unrolled
          (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))
        pure (r_spec = lift_theta_applied_perm r_impl
          (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))).holds ⌝ ⦄ := by
  sorry

end libcrux_iot_sha3.Equivalence
