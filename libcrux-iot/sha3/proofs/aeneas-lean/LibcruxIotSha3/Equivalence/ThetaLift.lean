/-
  θ-step impl/spec lifting — validation spike file.

  This file currently contains a single goal: `theta_comp_spec_local`,
  the impl-side post-condition of `keccakf1600_round0_theta`. Once that
  goal closes cleanly with `hax_mvcgen` + `grind`, the rest of the file
  plan (full `theta_lift_spec` triple + `Triple.bind` composition) can
  be filled in.
-/
import LibcruxIotSha3.Equivalence.Lift
import LibcruxIotSha3.Equivalence.LiftLemmas
import Hax

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

attribute [local irreducible] spread_to_even lift_lane_bv

/-! ## Theta composition (impl side)

Expresses each component of `r.d` after `keccakf1600_round0_theta` in
terms of the original `s.st` BitVec halves, and asserts that `s.st` and
`s.i` are preserved (the impl's θ step only writes `c` / `d`).

  d[x].z0 = c[(x+4)%5].z0 ⊕ rot(c[(x+1)%5].z1, 1)
  d[x].z1 = c[(x+4)%5].z1 ⊕         c[(x+1)%5].z0
  c[x].z  = ⊕_{y=0..4} st[5*x + y].z
-/

/-! ### Per-sub-function state-preservation specs

The θ step only writes the auxiliary `c` / `d` columns; `st` and `i` are
preserved. Each sub-function's spec is proved once with `mvcgen` and
registered `@[spec]` so the composed `keccakf1600_round0_theta` spec
chains them automatically. -/

@[spec]
private theorem set_lane_value_preserves_st_i
    (s : state.KeccakState) (i j : Std.Usize) {Q}
    (hpost : ∀ r : state.KeccakState, r.st = s.st → r.i = s.i → (Q.1 r).down)
    (v : Std.U32) (hi : i.val < 5) (hj : j.val < 2) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.set_lane_value s i j v
    ⦃ Q ⦄ := by
  unfold state.KeccakState.set_lane_value
  mvcgen
  all_goals first | simpa | (apply hpost <;> rfl)

@[spec]
private theorem get_with_zeta_spec
    (s : state.KeccakState) (i j zeta : Std.Usize) {Q}
    (hi : i.val < 5) (hj : j.val < 5) (hzeta : zeta.val < 2)
    (hpost : ∀ v : Std.U32, (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄ state.KeccakState.get_with_zeta s i j zeta ⦃ Q ⦄ := by
  unfold state.KeccakState.get_with_zeta
    lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index
  mvcgen
  all_goals first | (intros; apply hpost) | apply hpost | scalar_tac

/-- `Lane2U32` array-index returns the indexed element when in bounds. Used by
    `theta_d` to read `s.c`. -/
@[spec]
private theorem lane_index_spec
    (l : lane.Lane2U32) (i : Std.Usize) {Q}
    (hi : i.val < 2)
    (hpost : ∀ v : Std.U32, (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄
    lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index l i
    ⦃ Q ⦄ := by
  unfold lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index
  mvcgen
  all_goals first | (intros; apply hpost) | apply hpost | scalar_tac

/-- `core_models.num.U32.rotate_left` is total. (Local re-statement of the
    spec in `CoreModels/Specs.lean` for downstream consumers that haven't
    yet picked up the updated rust-core-models pin.) -/
@[spec]
private theorem rotate_left_u32_spec
    (x : Std.U32) (n : Std.U32) {Q}
    (hpost : ∀ v : Std.U32, (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.U32.rotate_left x n
    ⦃ Q ⦄ := by
  unfold core_models.num.U32.rotate_left
    rust_primitives.arithmetic.rotate_left_u32
  mvcgen
  apply hpost

/-- Tactic used for every per-sub-function state-preservation spec:
    unfold once, then chain the registered primitive specs. -/
local macro "theta_sub_preserves_st_i_proof" subfun:ident : tactic =>
  `(tactic|
    (unfold $subfun
     hax_mvcgen <;>
       first | grind | scalar_tac))

/-! Theta_c sub-function specs. Each ends in `set_lane_value` (only
    touches `c`), so the registered `set_lane_value_preserves_st_i`
    `@[spec]` lemma carries `st`/`i` through. -/

@[spec]
private theorem theta_c_x0_z0_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x0_z0

@[spec]
private theorem theta_c_x0_z1_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x0_z1

@[spec]
private theorem theta_c_x1_z0_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x1_z0

@[spec]
private theorem theta_c_x1_z1_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x1_z1

@[spec]
private theorem theta_c_x2_z0_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x2_z0

@[spec]
private theorem theta_c_x2_z1_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x2_z1

@[spec]
private theorem theta_c_x3_z0_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x3_z0

@[spec]
private theorem theta_c_x3_z1_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x3_z1

@[spec]
private theorem theta_c_x4_z0_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x4_z0

@[spec]
private theorem theta_c_x4_z1_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_c_x4_z1

/-! `theta_d` overwrites only `s.d`. -/
@[spec]
private theorem theta_d_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  theta_sub_preserves_st_i_proof keccak.keccakf1600_round0_theta_d

/-! ### Composed θ-round spec

With the 11 sub-function specs registered `@[spec]`, `hax_mvcgen`
threads `r.st = s.st ∧ r.i = s.i` through the entire 11-step do-block. -/

set_option maxHeartbeats 4000000 in
theorem theta_comp_spec_local (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_theta
  hax_mvcgen
  all_goals grind

end libcrux_iot_sha3.Equivalence
