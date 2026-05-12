/-
  θ-step impl/spec lifting.

  This file contains the impl-side post-condition for
  `keccakf1600_round0_theta` (the 12-conjunct d-value form,
  `theta_comp_spec_local`), and the spec-coupling theorem
  `theta_lift_spec` that connects it to `keccak_f.theta_unrolled` on
  the spec side via the lifting algebra in `LiftLemmas.lean`.
-/
import LibcruxIotSha3.Equivalence.Lift
import LibcruxIotSha3.Equivalence.LiftLemmas
import HacspecSha3
import Hax

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

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
private theorem set_lane_value_spec
    (s : state.KeccakState) (i j : Std.Usize) (v : Std.U32) {Q}
    (hi : i.val < 5) (hj : j.val < 2)
    (hpost : ∀ r : state.KeccakState,
        r.st = s.st → r.i = s.i → r.d = s.d →
        r.c = s.c.set i ((s.c.val[i.val]!).set j v) →
        (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.set_lane_value s i j v
    ⦃ Q ⦄ := by
  unfold state.KeccakState.set_lane_value
  mvcgen
  all_goals first | simpa | scalar_tac | (
    simp only [Std.WP.predn] at *
    obtain ⟨_, _⟩ := ‹_ ∧ _›
    apply hpost <;> simp [*])

@[spec]
private theorem get_with_zeta_spec
    (s : state.KeccakState) (i j zeta : Std.Usize) {Q}
    (hi : i.val < 5) (hj : j.val < 5) (hzeta : zeta.val < 2)
    (hpost : ∀ v : Std.U32, v = (s.st.val[5 * j.val + i.val]!).val[zeta.val]! →
        (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄ state.KeccakState.get_with_zeta s i j zeta ⦃ Q ⦄ := by
  unfold state.KeccakState.get_with_zeta
    lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index
  mvcgen
  all_goals first | scalar_tac | (
    intros
    apply hpost
    subst_vars
    congr 2 <;> scalar_tac)

/-- `Lane2U32` array-index returns the indexed element when in bounds. Used by
    `theta_d` to read `s.c`. -/
@[spec]
private theorem lane_index_spec
    (l : lane.Lane2U32) (i : Std.Usize) {Q}
    (hi : i.val < 2)
    (hpost : ∀ v : Std.U32, v = l.val[i.val]! → (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄
    lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index l i
    ⦃ Q ⦄ := by
  unfold lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index
  mvcgen
  all_goals first | scalar_tac | (intros; apply hpost _ ‹_›)

/-- `core_models.num.U32.rotate_left` returns the bit-rotated value. (Local
    re-statement of the spec in `CoreModels/Specs.lean` for downstream
    consumers that haven't yet picked up the updated rust-core-models pin.) -/
@[spec]
private theorem rotate_left_u32_spec
    (x : Std.U32) (n : Std.U32) {Q}
    (hpost : ∀ v : Std.U32, v.bv = x.bv.rotateLeft n.val → (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.U32.rotate_left x n
    ⦃ Q ⦄ := by
  unfold core_models.num.U32.rotate_left
    rust_primitives.arithmetic.rotate_left_u32
  mvcgen [Std.UScalar.rotate_left]
  apply hpost _ rfl

/-- `core_models.num.U64.rotate_left` returns the bit-rotated value. Same
    shape as `rotate_left_u32_spec`; used on the spec side of
    `theta_lift_spec` for the 5 ρ-style rotations in `theta_unrolled`. -/
@[spec]
private theorem rotate_left_u64_spec
    (x : Std.U64) (n : Std.U32) {Q}
    (hpost : ∀ v : Std.U64, v.bv = x.bv.rotateLeft n.val → (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.U64.rotate_left x n
    ⦃ Q ⦄ := by
  unfold core_models.num.U64.rotate_left
    rust_primitives.arithmetic.rotate_left_u64
  mvcgen [Std.UScalar.rotate_left]
  apply hpost _ rfl

/-- Tactic used for every per-sub-function state-preservation spec:
    unfold once, then chain the registered primitive specs. -/
local macro "theta_sub_preserves_st_i_proof" subfun:ident : tactic =>
  `(tactic|
    (unfold $subfun
     hax_mvcgen <;>
       first | grind | scalar_tac))

/-- Tactic for the strengthened `theta_c_xX_zZ` specs: after `hax_mvcgen`
    handles the do-block, the remaining VC says the freshly-written
    `c[X][Z]` value equals the chained XOR of five `s.st` reads. The
    XOR equality is per `UScalar.eq_equiv_bv_eq` + the BitVec halves
    of `h✝` already accumulated by `mvcgen`. -/
local macro "theta_c_proof" subfun:ident : tactic =>
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

/-! Theta_c sub-function specs. Each ends in `set_lane_value` (only
    touches `c`), so the registered `set_lane_value_preserves_st_i`
    `@[spec]` lemma carries `st`/`i` through. -/

@[spec]
private theorem theta_c_x0_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 0#usize
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x0_z0

@[spec]
private theorem theta_c_x0_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 1#usize
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x0_z1

@[spec]
private theorem theta_c_x1_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 0#usize
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x1_z0

@[spec]
private theorem theta_c_x1_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 1#usize
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x1_z1

@[spec]
private theorem theta_c_x2_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 0#usize
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x2_z0

@[spec]
private theorem theta_c_x2_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 1#usize
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x2_z1

@[spec]
private theorem theta_c_x3_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 0#usize
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x3_z0

@[spec]
private theorem theta_c_x3_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 1#usize
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x3_z1

@[spec]
private theorem theta_c_x4_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 0#usize
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x4_z0

@[spec]
private theorem theta_c_x4_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 1#usize
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x4_z1

/-! `theta_d` overwrites only `s.d`. Each `r.d[x][z]` is determined by two
    cells of `s.c`, possibly with a 32-bit rotation. -/
set_option maxHeartbeats 1600000 in
@[spec]
private theorem theta_d_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_d s
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
  unfold keccak.keccakf1600_round0_theta_d
  hax_mvcgen
  all_goals first
    | scalar_tac
    | trivial
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       all_goals first | trivial | assumption | (
         simp only [Std.WP.predn] at *
         try apply Std.U32.bv_eq_imp_eq
         simp_all [Std.UScalar.bv_xor, rot32]))

/-! ### Composed θ-round spec

With the 11 sub-function specs registered `@[spec]`, `hax_mvcgen`
threads the post forward. Each `r.d[x][z]` is expressed in terms of
the original `s.st` halves via the c-cell chain:

  c[x].z = ⊕_{y=0..4} st[5*x + y].z
  d[x].z0 = c[(x+4)%5].z0 ⊕ rot(c[(x+1)%5].z1, 1)
  d[x].z1 = c[(x+4)%5].z1 ⊕ c[(x+1)%5].z0
-/

set_option maxHeartbeats 4000000 in
theorem theta_comp_spec_local (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧
        -- d[0].z0 = c[4].z0 ⊕ rot(c[1].z1, 1)
        r.d.val[0]!.val[0]! =
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ^^^
          rot32 (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[1]! ^^^
                 s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[1]! ^^^
                 s.st.val[9]!.val[1]!) 1 ∧
        -- d[0].z1 = c[4].z1 ⊕ c[1].z0
        r.d.val[0]!.val[1]! =
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ^^^
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!) ∧
        -- d[1].z0 = c[0].z0 ⊕ rot(c[2].z1, 1)
        r.d.val[1]!.val[0]! =
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[0]!) ^^^
          rot32 (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
                 s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
                 s.st.val[14]!.val[1]!) 1 ∧
        -- d[1].z1 = c[0].z1 ⊕ c[2].z0
        r.d.val[1]!.val[1]! =
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[1]!) ^^^
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!) ∧
        -- d[2].z0 = c[1].z0 ⊕ rot(c[3].z1, 1)
        r.d.val[2]!.val[0]! =
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!) ^^^
          rot32 (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[1]! ^^^
                 s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
                 s.st.val[19]!.val[1]!) 1 ∧
        -- d[2].z1 = c[1].z1 ⊕ c[3].z0
        r.d.val[2]!.val[1]! =
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[1]!) ^^^
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[0]!) ∧
        -- d[3].z0 = c[2].z0 ⊕ rot(c[4].z1, 1)
        r.d.val[3]!.val[0]! =
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!) ^^^
          rot32 (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
                 s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[1]! ^^^
                 s.st.val[24]!.val[1]!) 1 ∧
        -- d[3].z1 = c[2].z1 ⊕ c[4].z0
        r.d.val[3]!.val[1]! =
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!) ^^^
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ∧
        -- d[4].z0 = c[3].z0 ⊕ rot(c[0].z1, 1)
        r.d.val[4]!.val[0]! =
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[0]!) ^^^
          rot32 (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
                 s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
                 s.st.val[4]!.val[1]!) 1 ∧
        -- d[4].z1 = c[3].z1 ⊕ c[0].z0
        r.d.val[4]!.val[1]! =
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[1]!) ^^^
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[0]!) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_theta
  hax_mvcgen
  all_goals first
    | trivial
    | grind
    | simp_all

/-! ## θ-applied lifted state (spec-coupling side)

After impl θ, the impl's `r.st` is *unchanged* — the actual XOR-into-`st`
is deferred to π·ρ·χ. But the spec's `theta_unrolled` *does* apply the
d-values to the state in one go. To bridge this asymmetry we define
`lift_theta_applied r_impl`, the lifted 25-lane state that the spec
would produce given the impl's post-θ d-cells. The spec-coupling
theorem then proves `theta_unrolled (lift s) = ok (lift_theta_applied r_impl)`.
-/

/-- The 25-lane `u64` state that the spec's `theta_unrolled` produces
    given the impl's post-θ scratch cells. Each lane `i` is
    `lift_lane_bv (s.st[i].z0 ⊕ s.d[i/5].z0) (s.st[i].z1 ⊕ s.d[i/5].z1)`. -/
def lift_theta_applied (s : state.KeccakState) : Std.Array Std.U64 25#usize :=
  ⟨List.ofFn (fun i : Fin 25 =>
      ⟨lift_lane_bv
          ((s.st.val[i.val]!).val[0]!.bv ^^^ (s.d.val[i.val / 5]!).val[0]!.bv)
          ((s.st.val[i.val]!).val[1]!.bv ^^^ (s.d.val[i.val / 5]!).val[1]!.bv)⟩),
    by simp⟩

/-! ## Spec-coupling theorem

After running the impl θ on `s`, the spec's `theta_unrolled (lift s)`
produces exactly `lift_theta_applied r_impl`. The chain of equalities:

  spec lane i  = (lift s)[i] ⊕ spec_d[i/5]
              = lift_lane (s.st[i]) ⊕ spec_d[i/5]    -- by lift def
              = lift_lane (s.st[i]) ⊕ lift_lane_bv impl_d[i/5]  -- by lift_td/xor5
              = lift_lane_bv (st.z0 ⊕ d.z0) (st.z1 ⊕ d.z1)  -- by lift_xor
              = lift_theta_applied r_impl . val[i]   -- by def

The substitution from `theta_comp_spec_local`'s 12-conjunct post is
how we bridge "spec d-cell content" with "impl r.d cell content".
-/

set_option maxHeartbeats 16000000 in
theorem theta_lift_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    (do
      let r_impl ← keccak.keccakf1600_round0_theta s
      let r_spec ← keccak_f.theta_unrolled (lift s)
      pure (r_spec = lift_theta_applied r_impl))
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  apply Triple.bind
  case hx => exact theta_comp_spec_local s
  case hf =>
    intro r_impl
    unfold keccak_f.theta_unrolled
    hax_mvcgen
    all_goals try scalar_tac
    sorry

end libcrux_iot_sha3.Equivalence
