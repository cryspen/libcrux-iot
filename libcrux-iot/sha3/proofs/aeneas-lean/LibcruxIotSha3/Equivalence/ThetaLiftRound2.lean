/-
  Round-2 θ lift spec.

  Round 2's theta operates on a state in round-1 layout, i.e.
  `lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)`. The c-cell
  reads follow `impl_swap_k 2` at the column-x impl positions.
-/
import LibcruxIotSha3.Equivalence.ThetaLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

attribute [local irreducible] spread_to_even lift_lane_bv

local macro "theta_c2_proof" subfun:ident : tactic =>
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

/-! ## Round-2 per-c-cell sub-function specs

The XOR order mirrors the impl read order (`ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4`
in canonical position order 5*x, 5*x+1, ..., 5*x+4). Zetas follow
`impl_swap_k 2` (true iff position ∉ {0,9,13,17,21}) for c[x][0] reads. -/

@[spec]
private theorem theta_c_x0_z0_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 0#usize
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[1]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x0_z0

@[spec]
private theorem theta_c_x0_z1_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 1#usize
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[0]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x0_z1

@[spec]
private theorem theta_c_x1_z0_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 0#usize
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[0]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x1_z0

@[spec]
private theorem theta_c_x1_z1_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 1#usize
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[1]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x1_z1

@[spec]
private theorem theta_c_x2_z0_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 0#usize
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[1]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x2_z0

@[spec]
private theorem theta_c_x2_z1_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 1#usize
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[0]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x2_z1

@[spec]
private theorem theta_c_x3_z0_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 0#usize
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[1]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x3_z0

@[spec]
private theorem theta_c_x3_z1_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 1#usize
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[0]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x3_z1

@[spec]
private theorem theta_c_x4_z0_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 0#usize
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x4_z0

@[spec]
private theorem theta_c_x4_z1_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 1#usize
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!)) ⌝ ⦄ := by
  theta_c2_proof keccak.keccakf1600_round2_theta_c_x4_z1

set_option maxHeartbeats 1600000 in
@[spec]
private theorem theta_d_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_d s
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
  unfold keccak.keccakf1600_round2_theta_d
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
theorem theta_comp_spec_local_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧
        r.d.val[0]!.val[0]! =
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ^^^
          rot32 (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[0]! ^^^
                 s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[0]! ^^^
                 s.st.val[9]!.val[1]!) 1 ∧
        r.d.val[0]!.val[1]! =
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ^^^
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[0]!) ∧
        r.d.val[1]!.val[0]! =
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[1]!) ^^^
          rot32 (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
                 s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[1]! ^^^
                 s.st.val[14]!.val[0]!) 1 ∧
        r.d.val[1]!.val[1]! =
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[0]!) ^^^
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[1]!) ∧
        r.d.val[2]!.val[0]! =
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[0]!) ^^^
          rot32 (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[0]! ^^^
                 s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[0]! ^^^
                 s.st.val[19]!.val[0]!) 1 ∧
        r.d.val[2]!.val[1]! =
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[1]!) ^^^
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[1]!) ∧
        r.d.val[3]!.val[0]! =
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[1]!) ^^^
          rot32 (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[1]! ^^^
                 s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[0]! ^^^
                 s.st.val[24]!.val[0]!) 1 ∧
        r.d.val[3]!.val[1]! =
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[0]!) ^^^
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ∧
        r.d.val[4]!.val[0]! =
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[1]!) ^^^
          rot32 (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[0]! ^^^
                 s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
                 s.st.val[4]!.val[0]!) 1 ∧
        r.d.val[4]!.val[1]! =
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[0]!) ^^^
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[1]!) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_theta
  hax_mvcgen
  all_goals first
    | trivial
    | grind
    | simp_all

/-! ## Round-2 spec-input lane peel lemmas

These mirror the round-1 infrastructure but with the round-2 layout
parameters `(impl_perm ∘ impl_perm, impl_swap_k 2)`. -/

/-- `impl_swap_k 2 L = decide (L.val ∉ [0, 9, 13, 17, 21])`. -/
private theorem impl_swap_k_two (L : Fin 25) :
    impl_swap_k 2 L =
      decide (L.val ∉ ([0, 9, 13, 17, 21] : List Nat)) := by
  unfold impl_swap_k; rfl

private theorem lift_perm_getElem (s : state.KeccakState)
    (p : Fin 25 → Fin 25) (sw : Fin 25 → Bool) (k : Fin 25) :
    (lift_perm s p sw).val[k.val]! =
      lift_lane_maybe_swap (s.st.val[(p k).val]!) (sw (p k)) := by
  unfold lift_perm
  change (List.ofFn _)[k.val]! = _
  rw [getElem!_pos _ k.val (by simpa using k.isLt), List.getElem_ofFn]

private theorem lift_perm_getElem_bv_aux (s : state.KeccakState)
    (p : Fin 25 → Fin 25) (sw : Fin 25 → Bool) (k : Fin 25) :
    ((↑(lift_perm s p sw) : List Std.U64)[(k.val : Nat)]!).bv =
      (lift_lane_maybe_swap (s.st.val[(p k).val]!) (sw (p k))).bv := by
  show ((lift_perm s p sw).val[k.val]!).bv = _
  rw [lift_perm_getElem]

/-- `lift_lane_maybe_swap` on the `true` branch. -/
private theorem lift_lane_maybe_swap_true_bv (l : libcrux_iot_sha3.lane.Lane2U32) :
    (lift_lane_maybe_swap l true).bv =
      lift_lane_bv (l.val[1]!).bv (l.val[0]!).bv := by
  unfold lift_lane_maybe_swap; rfl

/-- `lift_lane_maybe_swap` on the `false` branch. -/
private theorem lift_lane_maybe_swap_false_bv (l : libcrux_iot_sha3.lane.Lane2U32) :
    (lift_lane_maybe_swap l false).bv =
      lift_lane_bv (l.val[0]!).bv (l.val[1]!).bv := by
  unfold lift_lane_maybe_swap lift_lane; rfl

/-! ## RHS-side rewriting: `lift_theta_applied_perm`'s `lift_lane_maybe_swap`
    cells at concrete `Fin 25` indices for round 2 (`(impl_perm ∘ impl_perm)`,
    `impl_swap_k 2`). -/

private theorem lta_perm_bv_0_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 0)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 0)))).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm 0)).val = 0 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 0)) = false := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_1_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 1)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 1)))).bv =
      lift_lane_bv ((s.st.val[4]!).val[1]!.bv) ((s.st.val[4]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 1)).val = 4 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 1)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_2_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 2)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 2)))).bv =
      lift_lane_bv ((s.st.val[3]!).val[1]!.bv) ((s.st.val[3]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 2)).val = 3 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 2)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_3_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 3)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 3)))).bv =
      lift_lane_bv ((s.st.val[2]!).val[1]!.bv) ((s.st.val[2]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 3)).val = 2 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 3)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_4_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 4)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 4)))).bv =
      lift_lane_bv ((s.st.val[1]!).val[1]!.bv) ((s.st.val[1]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 4)).val = 1 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 4)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_5_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 5)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 5)))).bv =
      lift_lane_bv ((s.st.val[8]!).val[1]!.bv) ((s.st.val[8]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 5)).val = 8 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 5)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_6_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 6)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 6)))).bv =
      lift_lane_bv ((s.st.val[7]!).val[1]!.bv) ((s.st.val[7]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 6)).val = 7 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 6)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_7_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 7)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 7)))).bv =
      lift_lane_bv ((s.st.val[6]!).val[1]!.bv) ((s.st.val[6]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 7)).val = 6 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 7)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_8_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 8)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 8)))).bv =
      lift_lane_bv ((s.st.val[5]!).val[1]!.bv) ((s.st.val[5]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 8)).val = 5 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 8)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_9_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 9)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 9)))).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm 9)).val = 9 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 9)) = false := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_10_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 10)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 10)))).bv =
      lift_lane_bv ((s.st.val[11]!).val[1]!.bv) ((s.st.val[11]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 10)).val = 11 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 10)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_11_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 11)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 11)))).bv =
      lift_lane_bv ((s.st.val[10]!).val[1]!.bv) ((s.st.val[10]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 11)).val = 10 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 11)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_12_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 12)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 12)))).bv =
      lift_lane_bv ((s.st.val[14]!).val[1]!.bv) ((s.st.val[14]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 12)).val = 14 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 12)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_13_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 13)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 13)))).bv =
      lift_lane_bv ((s.st.val[13]!).val[0]!.bv) ((s.st.val[13]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm 13)).val = 13 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 13)) = false := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_14_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 14)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 14)))).bv =
      lift_lane_bv ((s.st.val[12]!).val[1]!.bv) ((s.st.val[12]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 14)).val = 12 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 14)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_15_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 15)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 15)))).bv =
      lift_lane_bv ((s.st.val[19]!).val[1]!.bv) ((s.st.val[19]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 15)).val = 19 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 15)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_16_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 16)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 16)))).bv =
      lift_lane_bv ((s.st.val[18]!).val[1]!.bv) ((s.st.val[18]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 16)).val = 18 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 16)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_17_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 17)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 17)))).bv =
      lift_lane_bv ((s.st.val[17]!).val[0]!.bv) ((s.st.val[17]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm 17)).val = 17 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 17)) = false := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_18_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 18)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 18)))).bv =
      lift_lane_bv ((s.st.val[16]!).val[1]!.bv) ((s.st.val[16]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 18)).val = 16 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 18)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_19_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 19)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 19)))).bv =
      lift_lane_bv ((s.st.val[15]!).val[1]!.bv) ((s.st.val[15]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 19)).val = 15 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 19)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_20_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 20)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 20)))).bv =
      lift_lane_bv ((s.st.val[22]!).val[1]!.bv) ((s.st.val[22]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 20)).val = 22 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 20)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_21_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 21)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 21)))).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm 21)).val = 21 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 21)) = false := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_22_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 22)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 22)))).bv =
      lift_lane_bv ((s.st.val[20]!).val[1]!.bv) ((s.st.val[20]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 22)).val = 20 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 22)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_23_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 23)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 23)))).bv =
      lift_lane_bv ((s.st.val[24]!).val[1]!.bv) ((s.st.val[24]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 23)).val = 24 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 23)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_24_2 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm (impl_perm 24)).val]!)
        (impl_swap_k 2 (impl_perm (impl_perm 24)))).bv =
      lift_lane_bv ((s.st.val[23]!).val[1]!.bv) ((s.st.val[23]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm 24)).val = 23 := by decide
  have hsw : impl_swap_k 2 (impl_perm (impl_perm 24)) = true := by
    unfold impl_swap_k; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]

/-! Round-2 per-K peel lemmas: same pattern as round 1 but with the
    `(impl_perm ∘ impl_perm, impl_swap_k 2)` shape. -/

private theorem lift_perm_getElem_bv_0_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(0 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨0, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨0, by decide⟩).val = 0 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨0, by decide⟩) = false := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_1_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(1 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[4]!).val[1]!.bv) ((s.st.val[4]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨1, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨1, by decide⟩).val = 4 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨1, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_2_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(2 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[3]!).val[1]!.bv) ((s.st.val[3]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨2, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨2, by decide⟩).val = 3 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨2, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_3_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(3 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[2]!).val[1]!.bv) ((s.st.val[2]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨3, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨3, by decide⟩).val = 2 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨3, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_4_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(4 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[1]!).val[1]!.bv) ((s.st.val[1]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨4, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨4, by decide⟩).val = 1 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨4, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_5_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(5 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[8]!).val[1]!.bv) ((s.st.val[8]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨5, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨5, by decide⟩).val = 8 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨5, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_6_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(6 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[7]!).val[1]!.bv) ((s.st.val[7]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨6, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨6, by decide⟩).val = 7 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨6, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_7_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(7 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[6]!).val[1]!.bv) ((s.st.val[6]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨7, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨7, by decide⟩).val = 6 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨7, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_8_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(8 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[5]!).val[1]!.bv) ((s.st.val[5]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨8, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨8, by decide⟩).val = 5 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨8, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_9_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(9 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨9, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨9, by decide⟩).val = 9 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨9, by decide⟩) = false := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_10_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(10 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[11]!).val[1]!.bv) ((s.st.val[11]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨10, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨10, by decide⟩).val = 11 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨10, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_11_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(11 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[10]!).val[1]!.bv) ((s.st.val[10]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨11, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨11, by decide⟩).val = 10 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨11, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_12_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(12 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[14]!).val[1]!.bv) ((s.st.val[14]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨12, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨12, by decide⟩).val = 14 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨12, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_13_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(13 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[13]!).val[0]!.bv) ((s.st.val[13]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨13, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨13, by decide⟩).val = 13 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨13, by decide⟩) = false := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_14_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(14 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[12]!).val[1]!.bv) ((s.st.val[12]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨14, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨14, by decide⟩).val = 12 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨14, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_15_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(15 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[19]!).val[1]!.bv) ((s.st.val[19]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨15, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨15, by decide⟩).val = 19 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨15, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_16_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(16 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[18]!).val[1]!.bv) ((s.st.val[18]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨16, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨16, by decide⟩).val = 18 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨16, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_17_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(17 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[17]!).val[0]!.bv) ((s.st.val[17]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨17, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨17, by decide⟩).val = 17 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨17, by decide⟩) = false := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_18_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(18 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[16]!).val[1]!.bv) ((s.st.val[16]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨18, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨18, by decide⟩).val = 16 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨18, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_19_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(19 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[15]!).val[1]!.bv) ((s.st.val[15]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨19, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨19, by decide⟩).val = 15 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨19, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_20_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(20 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[22]!).val[1]!.bv) ((s.st.val[22]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨20, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨20, by decide⟩).val = 22 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨20, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_21_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(21 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨21, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨21, by decide⟩).val = 21 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨21, by decide⟩) = false := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_22_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(22 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[20]!).val[1]!.bv) ((s.st.val[20]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨22, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨22, by decide⟩).val = 20 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨22, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_23_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(23 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[24]!).val[1]!.bv) ((s.st.val[24]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨23, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨23, by decide⟩).val = 24 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨23, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_24_2 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) : List Std.U64)[(24 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[23]!).val[1]!.bv) ((s.st.val[23]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm) (impl_swap_k 2) ⟨24, by decide⟩
  have hp : ((impl_perm ∘ impl_perm) ⟨24, by decide⟩).val = 23 := by decide
  have hsw : impl_swap_k 2 ((impl_perm ∘ impl_perm) ⟨24, by decide⟩) = true := by
    unfold impl_swap_k; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

/-- `BitVec.rotateLeft 1` distributes over XOR (BV-32 version). -/
private theorem rotateLeft1_xor_bv32 (a b : BitVec 32) :
    (a ^^^ b).rotateLeft 1 = a.rotateLeft 1 ^^^ b.rotateLeft 1 := by
  bv_decide

set_option maxHeartbeats 64000000 in
@[spec]
theorem theta_lift_spec_2 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta s
    ⦃ ⇓ r_impl => ⌜
      r_impl.i = s.i ∧
      (do
        let r_spec ← keccak_f.theta_unrolled
          (lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2))
        pure (r_spec = lift_theta_applied_perm r_impl
          (impl_perm ∘ impl_perm) (impl_swap_k 2))).holds ⌝ ⦄ := by
  apply Triple.of_entails_right _ (theta_comp_spec_local_2 s)
  rw [PostCond.entails_noThrow]
  intro r_impl hpost
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
  refine ⟨hpost.2.1, ?_⟩
  unfold Aeneas.Std.Result.holds
  unfold keccak_f.theta_unrolled
  hax_mvcgen
  all_goals try scalar_tac
  obtain ⟨hst, _, hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1,
          hd3z0, hd3z1, hd4z0, hd4z1⟩ := hpost
  apply Subtype.ext
  unfold lift_theta_applied_perm
  show _ = List.ofFn _
  simp only [Std.Array.make, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
             Nat.zero_add, Nat.reduceAdd, hst]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
  -- Rewrite `impl_swap_k 2` to a decidable membership form so reduceIte can fire.
  all_goals simp only [impl_swap_k_two]
  -- Unfold `lift_lane_maybe_swap` and `lift_lane` to expose `s.st[((impl_perm ∘ impl_perm) K).val]!`.
  -- The if-then-else branches reduce at concrete Fin K via `decide := true`.
  all_goals
    simp (config := { decide := true }) only [
      lift_lane_maybe_swap, lift_lane,
      Std.UScalar.bv_xor,
      reduceIte,
      Function.comp_apply,
      show (↑(impl_perm (impl_perm 0)) : Nat) = 0 from rfl]
  all_goals
    simp_all only [Std.UScalar.bv_xor, rot32,
      show ((0#usize : Std.Usize).val) = 0 from rfl,
      show ((1#usize : Std.Usize).val) = 1 from rfl,
      show ((2#usize : Std.Usize).val) = 2 from rfl,
      show ((3#usize : Std.Usize).val) = 3 from rfl,
      show ((4#usize : Std.Usize).val) = 4 from rfl,
      show ((5#usize : Std.Usize).val) = 5 from rfl,
      show ((6#usize : Std.Usize).val) = 6 from rfl,
      show ((7#usize : Std.Usize).val) = 7 from rfl,
      show ((8#usize : Std.Usize).val) = 8 from rfl,
      show ((9#usize : Std.Usize).val) = 9 from rfl,
      show ((10#usize : Std.Usize).val) = 10 from rfl,
      show ((11#usize : Std.Usize).val) = 11 from rfl,
      show ((12#usize : Std.Usize).val) = 12 from rfl,
      show ((13#usize : Std.Usize).val) = 13 from rfl,
      show ((14#usize : Std.Usize).val) = 14 from rfl,
      show ((15#usize : Std.Usize).val) = 15 from rfl,
      show ((16#usize : Std.Usize).val) = 16 from rfl,
      show ((17#usize : Std.Usize).val) = 17 from rfl,
      show ((18#usize : Std.Usize).val) = 18 from rfl,
      show ((19#usize : Std.Usize).val) = 19 from rfl,
      show ((20#usize : Std.Usize).val) = 20 from rfl,
      show ((21#usize : Std.Usize).val) = 21 from rfl,
      show ((22#usize : Std.Usize).val) = 22 from rfl,
      show ((23#usize : Std.Usize).val) = 23 from rfl,
      show ((24#usize : Std.Usize).val) = 24 from rfl,
      show ((1#u32 : Std.U32).val) = 1 from rfl]
  all_goals
    simp only [lift_perm_getElem_bv_0_2, lift_perm_getElem_bv_1_2, lift_perm_getElem_bv_2_2,
      lift_perm_getElem_bv_3_2, lift_perm_getElem_bv_4_2, lift_perm_getElem_bv_5_2,
      lift_perm_getElem_bv_6_2, lift_perm_getElem_bv_7_2, lift_perm_getElem_bv_8_2,
      lift_perm_getElem_bv_9_2, lift_perm_getElem_bv_10_2, lift_perm_getElem_bv_11_2,
      lift_perm_getElem_bv_12_2, lift_perm_getElem_bv_13_2, lift_perm_getElem_bv_14_2,
      lift_perm_getElem_bv_15_2, lift_perm_getElem_bv_16_2, lift_perm_getElem_bv_17_2,
      lift_perm_getElem_bv_18_2, lift_perm_getElem_bv_19_2, lift_perm_getElem_bv_20_2,
      lift_perm_getElem_bv_21_2, lift_perm_getElem_bv_22_2, lift_perm_getElem_bv_23_2,
      lift_perm_getElem_bv_24_2]
  all_goals simp only [Std.UScalarTy.U64_numBits_eq, ← lift_xor, ← lift_td]
  all_goals try
    simp only [
      show (↑(impl_perm (impl_perm (Fin.succ 0))) : Nat) = 4 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ)) : Nat) = 3 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ)) : Nat) = 2 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ)) : Nat) = 1 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ)) : Nat) = 8 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ)) : Nat) = 7 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ)) : Nat) = 6 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ)) : Nat) = 5 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 9 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 11 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 10 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 14 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 13 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 12 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 19 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 18 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 17 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 16 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 15 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 22 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 21 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 20 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 24 from rfl,
      show (↑(impl_perm (impl_perm (Fin.succ 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) : Nat) = 23 from rfl]
  all_goals first
    | rfl
    | apply congrArg₂ lift_lane_bv
  all_goals try simp only [rotateLeft1_xor_bv32]
  all_goals
    first | ac_rfl
          | (apply congrArg (HXor.hXor (α := BitVec 32) _); ac_rfl)
          | (apply congrArg (HXor.hXor (α := BitVec 32) _);
             try simp only [← rotateLeft1_xor_bv32]; ac_rfl)

end libcrux_iot_sha3.Equivalence
