/-
  Round-1 θ lift spec.

  Round k's theta operates on a state in round-(k-1) layout. The spec
  side feeds in `lift_perm s (impl_perm^k) (impl_swap_k k)`. For k=1
  that's `lift_perm s impl_perm impl_swap` (since `impl_swap_k 1 = impl_swap`).
  Theta does not pi-permute, so the output is in the same
  `(impl_perm^k, impl_swap_k k)` layout as the input — encoded as
  `lift_theta_applied_perm` on the post-theta impl state, with the same
  `(p, sw)` arguments.

  ## Architecture (transcribed from `ThetaLiftDefs.lean` + `ThetaLift.lean`)

  - 10 per-c-cell sub-fn specs `theta_c_x{0..4}_z{0,1}_spec_1`: each
    reads 5 swap-aware `s.st` halves matching `impl_swap` at the
    `impl_perm`-image of the spec column's 5 indices.
  - `theta_d_spec_1` matches round 0 (theta_d reads s.c canonically).
  - `theta_comp_spec_local_1` chains all 11 sub-fn specs.
  - 25 `lift_perm_getElem_bv_*` peel lemmas exposing the swap-aware
    spec-input lane reads.
  - `theta_lift_spec_1` then closes with the same `Subtype.ext` +
    25-cell `congr` strategy as round 0, but on the `_perm`-shaped RHS.
-/
import LibcruxIotSha3.Equivalence.ThetaLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

attribute [local irreducible] spread_to_even lift_lane_bv

/-- Tactic for round-1 c-cell specs: same shape as the round-0
    `theta_c_proof` macro in `ThetaLiftDefs.lean` (re-declared here
    locally because that macro is `local`). -/
local macro "theta_c1_proof" subfun:ident : tactic =>
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

/-! ## Round-1 per-c-cell sub-function specs

Each round-1 `theta_c_x{X}_z{Z}` reads 5 `s.st` halves with a
swap-aware pattern: for spec column index X, the impl reads at
positions `impl_perm(5*X + i)` for `i ∈ [0..5]`, with the `Z`-th
half polarity adjusted by `impl_swap` at each position.

The XOR order below mirrors the impl read order so that mvcgen's
literal XOR chain matches structurally. -/

@[spec]
private theorem theta_c_x0_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 0#usize
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x0_z0

@[spec]
private theorem theta_c_x0_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 1#usize
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x0_z1

@[spec]
private theorem theta_c_x1_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 0#usize
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[0]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x1_z0

@[spec]
private theorem theta_c_x1_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 1#usize
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[1]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x1_z1

@[spec]
private theorem theta_c_x2_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 0#usize
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x2_z0

@[spec]
private theorem theta_c_x2_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 1#usize
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x2_z1

@[spec]
private theorem theta_c_x3_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 0#usize
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x3_z0

@[spec]
private theorem theta_c_x3_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 1#usize
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x3_z1

@[spec]
private theorem theta_c_x4_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 0#usize
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x4_z0

@[spec]
private theorem theta_c_x4_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 1#usize
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!)) ⌝ ⦄ := by
  theta_c1_proof keccak.keccakf1600_round1_theta_c_x4_z1

/-! Round-1 `theta_d` overwrites `s.d` from the existing `s.c` cells.
    Same control shape as round 0 (theta_d uses c-cells canonically). -/

set_option maxHeartbeats 1600000 in
@[spec]
private theorem theta_d_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_d s
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
  unfold keccak.keccakf1600_round1_theta_d
  hax_mvcgen
  all_goals first
    | scalar_tac
    | trivial
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       all_goals first | trivial | assumption | (
         simp only [Std.WP.predn] at *
         try apply Std.U32.bv_eq_imp_eq
         simp_all [Std.UScalar.bv_xor, rot32]))

/-! ## Composed round-1 θ spec (impl side)

Chains the 11 sub-function specs to express each `r.d[x][z]` in terms
of the original `s.st` BitVec halves (with the round-1 swap-aware read
pattern). -/

set_option maxHeartbeats 4000000 in
theorem theta_comp_spec_local_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧
        -- d[0].z0 = c[4].z0 ⊕ rot(c[1].z1, 1)
        r.d.val[0]!.val[0]! =
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ^^^
          rot32 (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
                 s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
                 s.st.val[9]!.val[1]!) 1 ∧
        -- d[0].z1 = c[4].z1 ⊕ c[1].z0
        r.d.val[0]!.val[1]! =
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ^^^
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[0]!) ∧
        -- d[1].z0 = c[0].z0 ⊕ rot(c[2].z1, 1)
        r.d.val[1]!.val[0]! =
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!) ^^^
          rot32 (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
                 s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
                 s.st.val[14]!.val[0]!) 1 ∧
        -- d[1].z1 = c[0].z1 ⊕ c[2].z0
        r.d.val[1]!.val[1]! =
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!) ^^^
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!) ∧
        -- d[2].z0 = c[1].z0 ⊕ rot(c[3].z1, 1)
        r.d.val[2]!.val[0]! =
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[0]!) ^^^
          rot32 (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
                 s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
                 s.st.val[19]!.val[1]!) 1 ∧
        -- d[2].z1 = c[1].z1 ⊕ c[3].z0
        r.d.val[2]!.val[1]! =
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[1]!) ^^^
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!) ∧
        -- d[3].z0 = c[2].z0 ⊕ rot(c[4].z1, 1)
        r.d.val[3]!.val[0]! =
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!) ^^^
          rot32 (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[1]! ^^^
                 s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
                 s.st.val[24]!.val[1]!) 1 ∧
        -- d[3].z1 = c[2].z1 ⊕ c[4].z0
        r.d.val[3]!.val[1]! =
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!) ^^^
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ∧
        -- d[4].z0 = c[3].z0 ⊕ rot(c[0].z1, 1)
        r.d.val[4]!.val[0]! =
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!) ^^^
          rot32 (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
                 s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
                 s.st.val[4]!.val[1]!) 1 ∧
        -- d[4].z1 = c[3].z1 ⊕ c[0].z0
        r.d.val[4]!.val[1]! =
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!) ^^^
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_theta
  hax_mvcgen
  all_goals first
    | trivial
    | grind
    | simp_all

/-! ## Round-1 spec-input lane peel lemmas

Each `lift_perm_getElem_bv_k_1` exposes the spec-side input lane `k` as a
`lift_lane_bv` over the appropriate halves of `s.st[impl_perm k]`, with
half polarity selected by `impl_swap (impl_perm k)`. -/

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
    cells at concrete `Fin 25` indices, mapped to the corresponding
    `lift_lane_bv` over halves of `s.st[impl_perm K]`. -/

private theorem lta_perm_bv_0_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 0).val]!) (impl_swap (impl_perm 0))).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  have hp : (impl_perm 0).val = 0 := by decide
  have hsw : impl_swap (impl_perm 0) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_1_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 1).val]!) (impl_swap (impl_perm 1))).bv =
      lift_lane_bv ((s.st.val[2]!).val[1]!.bv) ((s.st.val[2]!).val[0]!.bv) := by
  have hp : (impl_perm 1).val = 2 := by decide
  have hsw : impl_swap (impl_perm 1) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_2_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 2).val]!) (impl_swap (impl_perm 2))).bv =
      lift_lane_bv ((s.st.val[4]!).val[0]!.bv) ((s.st.val[4]!).val[1]!.bv) := by
  have hp : (impl_perm 2).val = 4 := by decide
  have hsw : impl_swap (impl_perm 2) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_3_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 3).val]!) (impl_swap (impl_perm 3))).bv =
      lift_lane_bv ((s.st.val[1]!).val[0]!.bv) ((s.st.val[1]!).val[1]!.bv) := by
  have hp : (impl_perm 3).val = 1 := by decide
  have hsw : impl_swap (impl_perm 3) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_4_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 4).val]!) (impl_swap (impl_perm 4))).bv =
      lift_lane_bv ((s.st.val[3]!).val[1]!.bv) ((s.st.val[3]!).val[0]!.bv) := by
  have hp : (impl_perm 4).val = 3 := by decide
  have hsw : impl_swap (impl_perm 4) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_5_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 5).val]!) (impl_swap (impl_perm 5))).bv =
      lift_lane_bv ((s.st.val[6]!).val[0]!.bv) ((s.st.val[6]!).val[1]!.bv) := by
  have hp : (impl_perm 5).val = 6 := by decide
  have hsw : impl_swap (impl_perm 5) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_6_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 6).val]!) (impl_swap (impl_perm 6))).bv =
      lift_lane_bv ((s.st.val[8]!).val[1]!.bv) ((s.st.val[8]!).val[0]!.bv) := by
  have hp : (impl_perm 6).val = 8 := by decide
  have hsw : impl_swap (impl_perm 6) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_7_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 7).val]!) (impl_swap (impl_perm 7))).bv =
      lift_lane_bv ((s.st.val[5]!).val[1]!.bv) ((s.st.val[5]!).val[0]!.bv) := by
  have hp : (impl_perm 7).val = 5 := by decide
  have hsw : impl_swap (impl_perm 7) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_8_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 8).val]!) (impl_swap (impl_perm 8))).bv =
      lift_lane_bv ((s.st.val[7]!).val[0]!.bv) ((s.st.val[7]!).val[1]!.bv) := by
  have hp : (impl_perm 8).val = 7 := by decide
  have hsw : impl_swap (impl_perm 8) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_9_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 9).val]!) (impl_swap (impl_perm 9))).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  have hp : (impl_perm 9).val = 9 := by decide
  have hsw : impl_swap (impl_perm 9) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_10_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 10).val]!) (impl_swap (impl_perm 10))).bv =
      lift_lane_bv ((s.st.val[12]!).val[1]!.bv) ((s.st.val[12]!).val[0]!.bv) := by
  have hp : (impl_perm 10).val = 12 := by decide
  have hsw : impl_swap (impl_perm 10) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_11_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 11).val]!) (impl_swap (impl_perm 11))).bv =
      lift_lane_bv ((s.st.val[14]!).val[1]!.bv) ((s.st.val[14]!).val[0]!.bv) := by
  have hp : (impl_perm 11).val = 14 := by decide
  have hsw : impl_swap (impl_perm 11) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_12_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 12).val]!) (impl_swap (impl_perm 12))).bv =
      lift_lane_bv ((s.st.val[11]!).val[0]!.bv) ((s.st.val[11]!).val[1]!.bv) := by
  have hp : (impl_perm 12).val = 11 := by decide
  have hsw : impl_swap (impl_perm 12) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_13_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 13).val]!) (impl_swap (impl_perm 13))).bv =
      lift_lane_bv ((s.st.val[13]!).val[1]!.bv) ((s.st.val[13]!).val[0]!.bv) := by
  have hp : (impl_perm 13).val = 13 := by decide
  have hsw : impl_swap (impl_perm 13) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_14_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 14).val]!) (impl_swap (impl_perm 14))).bv =
      lift_lane_bv ((s.st.val[10]!).val[0]!.bv) ((s.st.val[10]!).val[1]!.bv) := by
  have hp : (impl_perm 14).val = 10 := by decide
  have hsw : impl_swap (impl_perm 14) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_15_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 15).val]!) (impl_swap (impl_perm 15))).bv =
      lift_lane_bv ((s.st.val[18]!).val[1]!.bv) ((s.st.val[18]!).val[0]!.bv) := by
  have hp : (impl_perm 15).val = 18 := by decide
  have hsw : impl_swap (impl_perm 15) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_16_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 16).val]!) (impl_swap (impl_perm 16))).bv =
      lift_lane_bv ((s.st.val[15]!).val[0]!.bv) ((s.st.val[15]!).val[1]!.bv) := by
  have hp : (impl_perm 16).val = 15 := by decide
  have hsw : impl_swap (impl_perm 16) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_17_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 17).val]!) (impl_swap (impl_perm 17))).bv =
      lift_lane_bv ((s.st.val[17]!).val[1]!.bv) ((s.st.val[17]!).val[0]!.bv) := by
  have hp : (impl_perm 17).val = 17 := by decide
  have hsw : impl_swap (impl_perm 17) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_18_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 18).val]!) (impl_swap (impl_perm 18))).bv =
      lift_lane_bv ((s.st.val[19]!).val[0]!.bv) ((s.st.val[19]!).val[1]!.bv) := by
  have hp : (impl_perm 18).val = 19 := by decide
  have hsw : impl_swap (impl_perm 18) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_19_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 19).val]!) (impl_swap (impl_perm 19))).bv =
      lift_lane_bv ((s.st.val[16]!).val[1]!.bv) ((s.st.val[16]!).val[0]!.bv) := by
  have hp : (impl_perm 19).val = 16 := by decide
  have hsw : impl_swap (impl_perm 19) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_20_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 20).val]!) (impl_swap (impl_perm 20))).bv =
      lift_lane_bv ((s.st.val[24]!).val[0]!.bv) ((s.st.val[24]!).val[1]!.bv) := by
  have hp : (impl_perm 20).val = 24 := by decide
  have hsw : impl_swap (impl_perm 20) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_21_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 21).val]!) (impl_swap (impl_perm 21))).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  have hp : (impl_perm 21).val = 21 := by decide
  have hsw : impl_swap (impl_perm 21) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_22_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 22).val]!) (impl_swap (impl_perm 22))).bv =
      lift_lane_bv ((s.st.val[23]!).val[0]!.bv) ((s.st.val[23]!).val[1]!.bv) := by
  have hp : (impl_perm 22).val = 23 := by decide
  have hsw : impl_swap (impl_perm 22) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_23_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 23).val]!) (impl_swap (impl_perm 23))).bv =
      lift_lane_bv ((s.st.val[20]!).val[1]!.bv) ((s.st.val[20]!).val[0]!.bv) := by
  have hp : (impl_perm 23).val = 20 := by decide
  have hsw : impl_swap (impl_perm 23) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_24_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 24).val]!) (impl_swap (impl_perm 24))).bv =
      lift_lane_bv ((s.st.val[22]!).val[1]!.bv) ((s.st.val[22]!).val[0]!.bv) := by
  have hp : (impl_perm 24).val = 22 := by decide
  have hsw : impl_swap (impl_perm 24) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]

/-- Build a peel lemma for a specific k=0..24 with `impl_perm`+`impl_swap_k 1`.
    Each instance is closed by `lift_perm_getElem_bv_aux` followed by `decide`
    on the concrete `impl_perm`/`impl_swap`/`impl_swap_k` values. -/
private theorem lift_perm_getElem_bv_0_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(0 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨0, by decide⟩
  have hp : (impl_perm ⟨0, by decide⟩).val = 0 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨0, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_1_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(1 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[2]!).val[1]!.bv) ((s.st.val[2]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨1, by decide⟩
  have hp : (impl_perm ⟨1, by decide⟩).val = 2 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨1, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_2_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(2 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[4]!).val[0]!.bv) ((s.st.val[4]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨2, by decide⟩
  have hp : (impl_perm ⟨2, by decide⟩).val = 4 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨2, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_3_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(3 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[1]!).val[0]!.bv) ((s.st.val[1]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨3, by decide⟩
  have hp : (impl_perm ⟨3, by decide⟩).val = 1 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨3, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_4_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(4 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[3]!).val[1]!.bv) ((s.st.val[3]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨4, by decide⟩
  have hp : (impl_perm ⟨4, by decide⟩).val = 3 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨4, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_5_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(5 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[6]!).val[0]!.bv) ((s.st.val[6]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨5, by decide⟩
  have hp : (impl_perm ⟨5, by decide⟩).val = 6 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨5, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_6_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(6 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[8]!).val[1]!.bv) ((s.st.val[8]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨6, by decide⟩
  have hp : (impl_perm ⟨6, by decide⟩).val = 8 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨6, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_7_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(7 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[5]!).val[1]!.bv) ((s.st.val[5]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨7, by decide⟩
  have hp : (impl_perm ⟨7, by decide⟩).val = 5 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨7, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_8_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(8 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[7]!).val[0]!.bv) ((s.st.val[7]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨8, by decide⟩
  have hp : (impl_perm ⟨8, by decide⟩).val = 7 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨8, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_9_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(9 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨9, by decide⟩
  have hp : (impl_perm ⟨9, by decide⟩).val = 9 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨9, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_10_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(10 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[12]!).val[1]!.bv) ((s.st.val[12]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨10, by decide⟩
  have hp : (impl_perm ⟨10, by decide⟩).val = 12 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨10, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_11_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(11 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[14]!).val[1]!.bv) ((s.st.val[14]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨11, by decide⟩
  have hp : (impl_perm ⟨11, by decide⟩).val = 14 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨11, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_12_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(12 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[11]!).val[0]!.bv) ((s.st.val[11]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨12, by decide⟩
  have hp : (impl_perm ⟨12, by decide⟩).val = 11 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨12, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_13_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(13 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[13]!).val[1]!.bv) ((s.st.val[13]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨13, by decide⟩
  have hp : (impl_perm ⟨13, by decide⟩).val = 13 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨13, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_14_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(14 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[10]!).val[0]!.bv) ((s.st.val[10]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨14, by decide⟩
  have hp : (impl_perm ⟨14, by decide⟩).val = 10 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨14, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_15_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(15 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[18]!).val[1]!.bv) ((s.st.val[18]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨15, by decide⟩
  have hp : (impl_perm ⟨15, by decide⟩).val = 18 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨15, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_16_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(16 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[15]!).val[0]!.bv) ((s.st.val[15]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨16, by decide⟩
  have hp : (impl_perm ⟨16, by decide⟩).val = 15 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨16, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_17_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(17 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[17]!).val[1]!.bv) ((s.st.val[17]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨17, by decide⟩
  have hp : (impl_perm ⟨17, by decide⟩).val = 17 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨17, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_18_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(18 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[19]!).val[0]!.bv) ((s.st.val[19]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨18, by decide⟩
  have hp : (impl_perm ⟨18, by decide⟩).val = 19 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨18, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_19_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(19 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[16]!).val[1]!.bv) ((s.st.val[16]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨19, by decide⟩
  have hp : (impl_perm ⟨19, by decide⟩).val = 16 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨19, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_20_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(20 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[24]!).val[0]!.bv) ((s.st.val[24]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨20, by decide⟩
  have hp : (impl_perm ⟨20, by decide⟩).val = 24 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨20, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_21_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(21 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨21, by decide⟩
  have hp : (impl_perm ⟨21, by decide⟩).val = 21 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨21, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_22_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(22 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[23]!).val[0]!.bv) ((s.st.val[23]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨22, by decide⟩
  have hp : (impl_perm ⟨22, by decide⟩).val = 23 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨22, by decide⟩) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_23_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(23 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[20]!).val[1]!.bv) ((s.st.val[20]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨23, by decide⟩
  have hp : (impl_perm ⟨23, by decide⟩).val = 20 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨23, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_24_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(24 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[22]!).val[1]!.bv) ((s.st.val[22]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨24, by decide⟩
  have hp : (impl_perm ⟨24, by decide⟩).val = 22 := by decide
  have hsw : impl_swap_k 1 (impl_perm ⟨24, by decide⟩) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

/-! Round-1 θ lift spec. The infrastructure above (`lta_perm_bv_*_1`,
    `lift_perm_getElem_bv_*_1`, `lift_lane_maybe_swap_{true,false}_bv`)
    is in place. Remaining gap: the 25-lane closure
    `simp only [..., ← lift_xor, ← lift_td]` doesn't fully discharge
    lanes with swap=true — those need a `← lift_swap` step (or
    equivalent BV reasoning) to fold the half-reversed `lift_lane_bv`
    expressions back into `lift_lane_maybe_swap true _` form. -/

-- @[spec] (added when proof is filled in)
set_option maxHeartbeats 64000000 in
theorem theta_lift_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta s
    ⦃ ⇓ r_impl => ⌜
      r_impl.i = s.i ∧
      (do
        let r_spec ← keccak_f.theta_unrolled (lift_perm s impl_perm (impl_swap_k 1))
        pure (r_spec = lift_theta_applied_perm r_impl impl_perm (impl_swap_k 1))).holds ⌝ ⦄ := by
  sorry

end libcrux_iot_sha3.Equivalence
