/-
  Round-2 ρ∘π∘χ∘ι lift spec.

  Same shape as `prc_lift_spec_1` (round 1) but on the round-2 impl chain.
  The input state is in round-1 layout (`(impl_perm ∘ impl_perm, impl_swap_k 2)`)
  and the output is in round-2 layout (`(impl_perm ∘ impl_perm ∘ impl_perm,
  impl_swap_k 3)`).

  Structure:
  - 10 per-FC `@[spec]` lemmas `pi_rho_chi_y{0..4}_zeta{0,1}_spec_fc_2`.
  - 25 input access lemmas `lift_theta_applied_perm_bv_K_2`.
  - Main composition `prc_lift_spec_2`.
-/
import LibcruxIotSha3.Equivalence.PrcLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

/-! ### FC proof macro (round-2 version)

Mirrors `prc_y_zeta_no_rc_proof_1`: the round-2 FC bodies have the
same shape (5 reads, 5 rotates, 5 chi steps, 5 writes), so the same
`hax_mvcgen` hyp-name layout applies. -/

set_option hygiene false in
local macro "prc_y_zeta_no_rc_proof_2" subfun:ident : tactic => `(tactic|
  (unfold $subfun
   hax_mvcgen
   all_goals try scalar_tac
   expose_names
   refine ⟨?_, ?_, ?_, ?_⟩
   · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
   · exact h_57.trans (h_50.trans (h_43.trans (h_36.trans h_29)))
   · exact h_56.trans (h_49.trans (h_42.trans (h_35.trans h_28)))
   · rw [h_59, h_52, h_45, h_38, h_31]
     norm_num [apply_5_writes]
     congr 6
     all_goals apply Std.U32.bv_eq_imp_eq
     all_goals (
       simp only [
         h_27.2, h_26.2, h_25,
         h_34.2, h_33.2, h_32,
         h_41.2, h_40.2, h_39,
         h_48.2, h_47.2, h_46,
         h_55.2, h_54.2, h_53,
         h_7, h_9, h_20, h_22, h_24,
         h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
         h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
         Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32]
       norm_num)))

set_option maxHeartbeats 16000000

/-! ## Per-FC spec lemmas for round-2 -/

/-! writes lanes 0/7/14/16/23 at halves 0/1/0/0/1;
    RC_INTERLEAVED_0[s.i] XORed into lane 0 half 0; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y0_zeta0_spec_fc_2
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[0]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 0
      let bx1 := rot32 (s.st.val[7]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx2 := rot32 (s.st.val[14]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 22
      let bx3 := rot32 (s.st.val[16]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 11
      let bx4 := rot32 (s.st.val[23]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        0 7 14 16 23
        0#usize 1#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · exact h_59.trans (h_52.trans (h_45.trans (h_38.trans h_31)))
  · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
  · rw [h_61, h_54, h_47, h_40, h_33]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        h_29.2, h_27.2, h_26.2, h_25,
        h_36.2, h_35.2, h_34,
        h_43.2, h_42.2, h_41,
        h_50.2, h_49.2, h_48,
        h_57.2, h_56.2, h_55,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32]
      norm_num)

/-! writes lanes 0/7/14/16/23 at halves 1/0/1/1/0;
    RC_INTERLEAVED_1[s.i] XORed into lane 0 half 1; INCREMENTS `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y0_zeta1_spec_fc_2
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[0]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 0
      let bx1 := rot32 (s.st.val[7]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 22
      let bx2 := rot32 (s.st.val[14]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 21
      let bx3 := rot32 (s.st.val[16]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 10
      let bx4 := rot32 (s.st.val[23]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ∧
      r.st.val = apply_5_writes s.st.val
        0 7 14 16 23
        1#usize 0#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_1.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_61.trans (h_54.trans (h_47.trans (h_40.trans h_33)))
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · rw [h_59, h_52, h_45, h_38, h_31, h_30]
    rfl
  · rw [h_62, h_55, h_48, h_41, h_34]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        h_29.2, h_27.2, h_26.2, h_25,
        h_37.2, h_36.2, h_35,
        h_44.2, h_43.2, h_42,
        h_51.2, h_50.2, h_49,
        h_58.2, h_57.2, h_56,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32]
      norm_num)

/-! writes lanes 3/5/12/19/21 at halves 0/0/0/1/0; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y1_zeta0_spec_fc_2
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[19]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 14
      let bx1 := rot32 (s.st.val[21]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 10
      let bx2 := rot32 (s.st.val[3]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 2
      let bx3 := rot32 (s.st.val[5]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 23
      let bx4 := rot32 (s.st.val[12]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 5 12 19 21
        0#usize 0#usize 0#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof_2 keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0

/-! writes lanes 3/5/12/19/21 at halves 1/1/1/0/1; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y1_zeta1_spec_fc_2
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[19]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 14
      let bx1 := rot32 (s.st.val[21]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 10
      let bx2 := rot32 (s.st.val[3]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 1
      let bx3 := rot32 (s.st.val[5]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx4 := rot32 (s.st.val[12]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 30
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 5 12 19 21
        1#usize 1#usize 1#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof_2 keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1

/-! writes lanes 1/8/10/17/24 at halves 1/0/1/1/1; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y2_zeta0_spec_fc_2
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[8]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 1
      let bx1 := rot32 (s.st.val[10]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 3
      let bx2 := rot32 (s.st.val[17]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 13
      let bx3 := rot32 (s.st.val[24]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 4
      let bx4 := rot32 (s.st.val[1]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 8 10 17 24
        1#usize 0#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof_2 keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0

/-! writes lanes 1/8/10/17/24 at halves 0/1/0/0/0; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y2_zeta1_spec_fc_2
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[8]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 0
      let bx1 := rot32 (s.st.val[10]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 3
      let bx2 := rot32 (s.st.val[17]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 12
      let bx3 := rot32 (s.st.val[24]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 4
      let bx4 := rot32 (s.st.val[1]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 8 10 17 24
        0#usize 1#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof_2 keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1

/-! writes lanes 4/6/13/15/22 at halves 1/1/1/1/0; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y3_zeta0_spec_fc_2
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[22]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 14
      let bx1 := rot32 (s.st.val[4]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 18
      let bx2 := rot32 (s.st.val[6]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 5
      let bx3 := rot32 (s.st.val[13]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 8
      let bx4 := rot32 (s.st.val[15]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 6 13 15 22
        1#usize 1#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof_2 keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0

/-! writes lanes 4/6/13/15/22 at halves 0/0/0/0/1; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y3_zeta1_spec_fc_2
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[22]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 13
      let bx1 := rot32 (s.st.val[4]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 18
      let bx2 := rot32 (s.st.val[6]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 5
      let bx3 := rot32 (s.st.val[13]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 7
      let bx4 := rot32 (s.st.val[15]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 6 13 15 22
        0#usize 0#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof_2 keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1

/-! writes lanes 2/9/11/18/20 at halves 0/0/1/0/0; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y4_zeta0_spec_fc_2
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[11]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 31
      let bx1 := rot32 (s.st.val[18]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      let bx2 := rot32 (s.st.val[20]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 20
      let bx3 := rot32 (s.st.val[2]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 21
      let bx4 := rot32 (s.st.val[9]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 9 11 18 20
        0#usize 0#usize 1#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof_2 keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0

/-! writes lanes 2/9/11/18/20 at halves 1/1/0/1/1; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y4_zeta1_spec_fc_2
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[11]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      let bx1 := rot32 (s.st.val[18]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 27
      let bx2 := rot32 (s.st.val[20]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 19
      let bx3 := rot32 (s.st.val[2]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 20
      let bx4 := rot32 (s.st.val[9]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 9 11 18 20
        1#usize 1#usize 0#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof_2 keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1


/-! ## Input cell access lemmas (round 2)

For each `K = 0..24`, `(lift_theta_applied_perm s (impl_perm ∘ impl_perm)
(impl_swap_k 2)).val[K]!.bv` is `lift_lane_bv` over swap-aware halves of
`s.st[(impl_perm (impl_perm K))]` XOR'd with `s.d[K/5]`. -/

private theorem lta_perm_getElem_2 (s : state.KeccakState)
    (p : Fin 25 → Fin 25) (sw : Fin 25 → Bool) (k : Fin 25) :
    (lift_theta_applied_perm s p sw).val[k.val]! =
      lift_lane_maybe_swap (s.st.val[(p k).val]!) (sw (p k)) ^^^
        lift_lane (s.d.val[k.val / 5]!) := by
  unfold lift_theta_applied_perm
  change (List.ofFn _)[k.val]! = _
  rw [getElem!_pos _ k.val (by simpa using k.isLt), List.getElem_ofFn]

theorem lift_theta_applied_perm_bv_0_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[0]!).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[0]!).val[1]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨0, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨0, by decide⟩).val = 0 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨0, by decide⟩) = false := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_1_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[1]!).bv =
      lift_lane_bv ((s.st.val[4]!).val[1]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[4]!).val[0]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨1, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨1, by decide⟩).val = 4 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨1, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_2_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[2]!).bv =
      lift_lane_bv ((s.st.val[3]!).val[1]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[3]!).val[0]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨2, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨2, by decide⟩).val = 3 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨2, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_3_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[3]!).bv =
      lift_lane_bv ((s.st.val[2]!).val[1]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[2]!).val[0]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨3, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨3, by decide⟩).val = 2 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨3, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_4_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[4]!).bv =
      lift_lane_bv ((s.st.val[1]!).val[1]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[1]!).val[0]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨4, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨4, by decide⟩).val = 1 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨4, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_5_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[5]!).bv =
      lift_lane_bv ((s.st.val[8]!).val[1]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[8]!).val[0]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨5, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨5, by decide⟩).val = 8 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨5, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_6_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[6]!).bv =
      lift_lane_bv ((s.st.val[7]!).val[1]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[7]!).val[0]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨6, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨6, by decide⟩).val = 7 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨6, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_7_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[7]!).bv =
      lift_lane_bv ((s.st.val[6]!).val[1]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[6]!).val[0]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨7, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨7, by decide⟩).val = 6 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨7, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_8_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[8]!).bv =
      lift_lane_bv ((s.st.val[5]!).val[1]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[5]!).val[0]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨8, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨8, by decide⟩).val = 5 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨8, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_9_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[9]!).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[9]!).val[1]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨9, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨9, by decide⟩).val = 9 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨9, by decide⟩) = false := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_10_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[10]!).bv =
      lift_lane_bv ((s.st.val[11]!).val[1]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[11]!).val[0]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨10, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨10, by decide⟩).val = 11 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨10, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_11_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[11]!).bv =
      lift_lane_bv ((s.st.val[10]!).val[1]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[10]!).val[0]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨11, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨11, by decide⟩).val = 10 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨11, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_12_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[12]!).bv =
      lift_lane_bv ((s.st.val[14]!).val[1]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[14]!).val[0]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨12, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨12, by decide⟩).val = 14 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨12, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_13_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[13]!).bv =
      lift_lane_bv ((s.st.val[13]!).val[0]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[13]!).val[1]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨13, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨13, by decide⟩).val = 13 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨13, by decide⟩) = false := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_14_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[14]!).bv =
      lift_lane_bv ((s.st.val[12]!).val[1]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[12]!).val[0]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨14, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨14, by decide⟩).val = 12 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨14, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_15_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[15]!).bv =
      lift_lane_bv ((s.st.val[19]!).val[1]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[19]!).val[0]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨15, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨15, by decide⟩).val = 19 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨15, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_16_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[16]!).bv =
      lift_lane_bv ((s.st.val[18]!).val[1]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[18]!).val[0]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨16, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨16, by decide⟩).val = 18 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨16, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_17_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[17]!).bv =
      lift_lane_bv ((s.st.val[17]!).val[0]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[17]!).val[1]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨17, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨17, by decide⟩).val = 17 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨17, by decide⟩) = false := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_18_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[18]!).bv =
      lift_lane_bv ((s.st.val[16]!).val[1]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[16]!).val[0]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨18, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨18, by decide⟩).val = 16 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨18, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_19_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[19]!).bv =
      lift_lane_bv ((s.st.val[15]!).val[1]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[15]!).val[0]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨19, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨19, by decide⟩).val = 15 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨19, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_20_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[20]!).bv =
      lift_lane_bv ((s.st.val[22]!).val[1]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[22]!).val[0]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨20, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨20, by decide⟩).val = 22 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨20, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_21_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[21]!).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[21]!).val[1]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨21, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨21, by decide⟩).val = 21 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨21, by decide⟩) = false := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_22_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[22]!).bv =
      lift_lane_bv ((s.st.val[20]!).val[1]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[20]!).val[0]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨22, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨22, by decide⟩).val = 20 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨22, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_23_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[23]!).bv =
      lift_lane_bv ((s.st.val[24]!).val[1]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[24]!).val[0]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨23, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨23, by decide⟩).val = 24 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨23, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_24_2 (s : state.KeccakState) :
    ((lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)).val[24]!).bv =
      lift_lane_bv ((s.st.val[23]!).val[1]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[23]!).val[0]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem_2 s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨24, by decide⟩]
  have hp : ((impl_perm ∘ impl_perm) ⟨24, by decide⟩).val = 23 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨24, by decide⟩) = true := by
    rw [impl_swap_k_two]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

/-! ## Main composition: `prc_lift_spec_2`

Couples the round-2 `keccakf1600_round2_pi_rho_chi_{1,2}` chain to the spec
`iota ∘ chi_unrolled ∘ pi_unrolled ∘ rho_unrolled` applied to the round-1
layout state. Output is in round-2 layout (`(impl_perm ∘ impl_perm ∘
impl_perm, impl_swap_k 3)`). Mirrors `prc_lift_spec_1` but with the round-2
parameters on both sides. -/

set_option maxHeartbeats 256000000 in
theorem prc_lift_spec_2 (s : state.KeccakState) (hi_lt : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let r1 ← keccak.keccakf1600_round2_pi_rho_chi_1 0#usize s
        keccak.keccakf1600_round2_pi_rho_chi_2 r1)
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled
            (lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2))
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl
                  (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))).holds ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_1
  unfold keccak.keccakf1600_round2_pi_rho_chi_2
  hax_mvcgen
  all_goals try scalar_tac
  subst_vars
  rw [prc_spec_eq_composed]
  casesm* _ ∧ _
  rename_i r9 r8 r7 r6 r5 r4 r3 r2 r1 r' hd hc hi h_chain
    l26 l25 l24 l23 l22 l21 l20 l19 l18 l17 l16 l15 l14 l13 l12 l11 l10 l9 l8
    h_FC9 l7 h_FC8 l6 h_FC7 l5 h_FC6 l4 h_FC5 l3 h_FC4 l2 h_FC3 l1 h_FC2 l_last h_FC1
  simp only [l_last, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17,
    l18, l19, l20, l21, l22, l23, l24, l25, l26]
    at h_chain h_FC1 h_FC2 h_FC3 h_FC4 h_FC5 h_FC6 h_FC7 h_FC8 h_FC9
  have hr'  : (↑r'.st : List lane.Lane2U32).length = 25  := by exact r'.st.2
  have hr1  : (↑r1.st : List lane.Lane2U32).length = 25  := by exact r1.st.2
  have hr2  : (↑r2.st : List lane.Lane2U32).length = 25  := by exact r2.st.2
  have hr3  : (↑r3.st : List lane.Lane2U32).length = 25  := by exact r3.st.2
  have hr4  : (↑r4.st : List lane.Lane2U32).length = 25  := by exact r4.st.2
  have hr5  : (↑r5.st : List lane.Lane2U32).length = 25  := by exact r5.st.2
  have hr6  : (↑r6.st : List lane.Lane2U32).length = 25  := by exact r6.st.2
  have hr7  : (↑r7.st : List lane.Lane2U32).length = 25  := by exact r7.st.2
  have hr8  : (↑r8.st : List lane.Lane2U32).length = 25  := by exact r8.st.2
  have hr9  : (↑r9.st : List lane.Lane2U32).length = 25  := by exact r9.st.2
  have hss  : (↑s.st  : List lane.Lane2U32).length = 25  := by exact s.st.2
  have hlane : ∀ (L : lane.Lane2U32), L.val.length = 2 := fun L => L.2
  apply Subtype.ext
  unfold prc_spec lift_perm
  conv_rhs =>
    rw [show (impl_swap_k 3) = (fun L : Fin 25 =>
      decide (L.val ∈ ([1, 4, 6, 7, 10, 11, 13, 15, 17, 19, 23, 24] : List Nat))) from by
      funext L; rw [impl_swap_k]]
    unfold impl_perm lift_lane_maybe_swap
  simp (config := { decide := true }) only [Std.Array.make, List.ofFn_succ, List.ofFn_zero,
    Function.comp_apply,
    Fin.val_succ, Fin.val_zero, Nat.succ_eq_add_one, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceDiv, Nat.reduceMod, reduceIte]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (
    apply Std.U64.bv_eq_imp_eq
    simp (config := { decide := true }) only
      [h_chain, h_FC1, h_FC2, h_FC3, h_FC4, h_FC5, h_FC6, h_FC7, h_FC8, h_FC9, apply_5_writes,
       lift_lane,
       List.getElem!_set_ne, List.getElem!_set, List.length_set,
       Std.Array.set_val_eq, hlane,
       hr', hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hss,
       show ((0#usize : Std.Usize) : Nat) = 0 from rfl,
       show ((1#usize : Std.Usize) : Nat) = 1 from rfl]
    simp only [lift_theta_applied_perm_bv_0_2, lift_theta_applied_perm_bv_1_2,
      lift_theta_applied_perm_bv_2_2, lift_theta_applied_perm_bv_3_2,
      lift_theta_applied_perm_bv_4_2, lift_theta_applied_perm_bv_5_2,
      lift_theta_applied_perm_bv_6_2, lift_theta_applied_perm_bv_7_2,
      lift_theta_applied_perm_bv_8_2, lift_theta_applied_perm_bv_9_2,
      lift_theta_applied_perm_bv_10_2, lift_theta_applied_perm_bv_11_2,
      lift_theta_applied_perm_bv_12_2, lift_theta_applied_perm_bv_13_2,
      lift_theta_applied_perm_bv_14_2, lift_theta_applied_perm_bv_15_2,
      lift_theta_applied_perm_bv_16_2, lift_theta_applied_perm_bv_17_2,
      lift_theta_applied_perm_bv_18_2, lift_theta_applied_perm_bv_19_2,
      lift_theta_applied_perm_bv_20_2, lift_theta_applied_perm_bv_21_2,
      lift_theta_applied_perm_bv_22_2, lift_theta_applied_perm_bv_23_2,
      lift_theta_applied_perm_bv_24_2,
      Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32, rot64]
    simp only [Std.UScalarTy.U64_numBits_eq,
      rot_0, rot_1, rot_2, rot_3, rot_6, rot_8, rot_10,
      rot_14, rot_15, rot_18, rot_20, rot_21, rot_25, rot_27,
      rot_28, rot_36, rot_39, rot_41, rot_43, rot_44, rot_45,
      rot_55, rot_56, rot_61, rot_62,
      ← lift_xor, ← lift_and, ← lift_not, ← lift_chi,
      ← rc_equiv _ hi_lt])

end libcrux_iot_sha3.Equivalence
