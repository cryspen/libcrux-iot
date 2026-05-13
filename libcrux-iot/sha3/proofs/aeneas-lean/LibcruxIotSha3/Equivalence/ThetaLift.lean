/-
  θ-step impl/spec lifting.

  This file contains the impl-side post-condition for
  `keccakf1600_round0_theta` (the 12-conjunct d-value form,
  `theta_comp_spec_local`), and the spec-coupling theorem
  `theta_lift_spec` that connects it to `keccak_f.theta_unrolled` on
  the spec side via the lifting algebra in `LiftLemmas.lean`.
-/
import LibcruxIotSha3.Equivalence.Lift
import LibcruxIotSha3.Equivalence.UScalarAC
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
       scalar_tac))

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

/-- Helper for `lift_theta_applied`: lift a single lane given the four
    interleaved halves (state z0/z1 and column d z0/z1). XOR is applied
    on the U32 halves before lifting; equivalently, the U32 XORs land
    inside the BitVec arguments of `lift_lane_bv`. -/
private abbrev lta (st_z0 st_z1 d_z0 d_z1 : Std.U32) : Std.U64 :=
  ⟨lift_lane_bv ((st_z0 ^^^ d_z0).bv) ((st_z1 ^^^ d_z1).bv)⟩

/-- The 25-lane `u64` state that the spec's `theta_unrolled` produces
    given the impl's post-θ scratch cells. Each lane `i` is
    `lift_lane_bv (s.st[i].z0 ⊕ s.d[i/5].z0) (s.st[i].z1 ⊕ s.d[i/5].z1)`.

    Written as a literal 25-element list (rather than `List.ofFn`) so
    that `unfold lift_theta_applied` exposes a concrete cons list — this
    aligns the RHS structurally with the LHS literal list produced by
    `hax_mvcgen` on `theta_unrolled` and lets a 25-way `congr` peel the
    lanes pointwise. -/
def lift_theta_applied (s : state.KeccakState) : Std.Array Std.U64 25#usize :=
  let d := s.d; let st := s.st
  Std.Array.make 25#usize [
    lta (st.val[0]!).val[0]! (st.val[0]!).val[1]! (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    lta (st.val[1]!).val[0]! (st.val[1]!).val[1]! (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    lta (st.val[2]!).val[0]! (st.val[2]!).val[1]! (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    lta (st.val[3]!).val[0]! (st.val[3]!).val[1]! (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    lta (st.val[4]!).val[0]! (st.val[4]!).val[1]! (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    lta (st.val[5]!).val[0]! (st.val[5]!).val[1]! (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    lta (st.val[6]!).val[0]! (st.val[6]!).val[1]! (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    lta (st.val[7]!).val[0]! (st.val[7]!).val[1]! (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    lta (st.val[8]!).val[0]! (st.val[8]!).val[1]! (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    lta (st.val[9]!).val[0]! (st.val[9]!).val[1]! (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    lta (st.val[10]!).val[0]! (st.val[10]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    lta (st.val[11]!).val[0]! (st.val[11]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    lta (st.val[12]!).val[0]! (st.val[12]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    lta (st.val[13]!).val[0]! (st.val[13]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    lta (st.val[14]!).val[0]! (st.val[14]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    lta (st.val[15]!).val[0]! (st.val[15]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    lta (st.val[16]!).val[0]! (st.val[16]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    lta (st.val[17]!).val[0]! (st.val[17]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    lta (st.val[18]!).val[0]! (st.val[18]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    lta (st.val[19]!).val[0]! (st.val[19]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    lta (st.val[20]!).val[0]! (st.val[20]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!,
    lta (st.val[21]!).val[0]! (st.val[21]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!,
    lta (st.val[22]!).val[0]! (st.val[22]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!,
    lta (st.val[23]!).val[0]! (st.val[23]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!,
    lta (st.val[24]!).val[0]! (st.val[24]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!]

/-- Bridge from the lift definition: indexing `lift s` at a `Fin 25` returns
    the lifted interleaved halves of `s.st[k]`. Used to rewrite the spec-side
    chain hypotheses `r✝ = (lift s)[k]!` into BitVec form. Stated over `Fin 25`
    so the `lift`-side `List.ofFn` reduces by `Fin.getElem` rather than a
    generic Nat index. -/
private theorem lift_getElem (s : state.KeccakState) (k : Fin 25) :
    (lift s).val[k.val]! =
      (⟨lift_lane_bv ((s.st.val[k.val]!).val[0]!.bv) ((s.st.val[k.val]!).val[1]!.bv)⟩ : Std.U64) := by
  unfold lift lift_lane
  change (List.ofFn _)[k.val]! = _
  rw [getElem!_pos _ k.val (by simpa using k.isLt), List.getElem_ofFn]

private theorem lift_getElem_bv (s : state.KeccakState) (k : Fin 25) :
    ((↑(lift s) : List Std.U64)[(k.val : Nat)]!).bv =
      lift_lane_bv ((s.st.val[k.val]!).val[0]!.bv) ((s.st.val[k.val]!).val[1]!.bv) := by
  rw [lift_getElem]

/-- 25 concrete-index specialisations of `lift_getElem_bv`, stated in the
    "coerced-list" form `(↑(lift s))[↑N#usize : Std.Usize)]!.bv` to match
    exactly the syntactic shape `hax_mvcgen` produces in `theta_unrolled`'s
    spec-side chain. Each fires as a simp rewrite to expose the underlying
    `lift_lane_bv` for the algebraic close. -/
private theorem lift_getElem_bv_0 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(0 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  show ((lift s).val[0]!).bv = _; exact lift_getElem_bv s ⟨0, by decide⟩
private theorem lift_getElem_bv_1 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(1 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[1]!).val[0]!.bv) ((s.st.val[1]!).val[1]!.bv) := by
  show ((lift s).val[1]!).bv = _; exact lift_getElem_bv s ⟨1, by decide⟩
private theorem lift_getElem_bv_2 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(2 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[2]!).val[0]!.bv) ((s.st.val[2]!).val[1]!.bv) := by
  show ((lift s).val[2]!).bv = _; exact lift_getElem_bv s ⟨2, by decide⟩
private theorem lift_getElem_bv_3 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(3 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[3]!).val[0]!.bv) ((s.st.val[3]!).val[1]!.bv) := by
  show ((lift s).val[3]!).bv = _; exact lift_getElem_bv s ⟨3, by decide⟩
private theorem lift_getElem_bv_4 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(4 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[4]!).val[0]!.bv) ((s.st.val[4]!).val[1]!.bv) := by
  show ((lift s).val[4]!).bv = _; exact lift_getElem_bv s ⟨4, by decide⟩
private theorem lift_getElem_bv_5 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(5 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[5]!).val[0]!.bv) ((s.st.val[5]!).val[1]!.bv) := by
  show ((lift s).val[5]!).bv = _; exact lift_getElem_bv s ⟨5, by decide⟩
private theorem lift_getElem_bv_6 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(6 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[6]!).val[0]!.bv) ((s.st.val[6]!).val[1]!.bv) := by
  show ((lift s).val[6]!).bv = _; exact lift_getElem_bv s ⟨6, by decide⟩
private theorem lift_getElem_bv_7 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(7 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[7]!).val[0]!.bv) ((s.st.val[7]!).val[1]!.bv) := by
  show ((lift s).val[7]!).bv = _; exact lift_getElem_bv s ⟨7, by decide⟩
private theorem lift_getElem_bv_8 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(8 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[8]!).val[0]!.bv) ((s.st.val[8]!).val[1]!.bv) := by
  show ((lift s).val[8]!).bv = _; exact lift_getElem_bv s ⟨8, by decide⟩
private theorem lift_getElem_bv_9 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(9 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  show ((lift s).val[9]!).bv = _; exact lift_getElem_bv s ⟨9, by decide⟩
private theorem lift_getElem_bv_10 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(10 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[10]!).val[0]!.bv) ((s.st.val[10]!).val[1]!.bv) := by
  show ((lift s).val[10]!).bv = _; exact lift_getElem_bv s ⟨10, by decide⟩
private theorem lift_getElem_bv_11 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(11 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[11]!).val[0]!.bv) ((s.st.val[11]!).val[1]!.bv) := by
  show ((lift s).val[11]!).bv = _; exact lift_getElem_bv s ⟨11, by decide⟩
private theorem lift_getElem_bv_12 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(12 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[12]!).val[0]!.bv) ((s.st.val[12]!).val[1]!.bv) := by
  show ((lift s).val[12]!).bv = _; exact lift_getElem_bv s ⟨12, by decide⟩
private theorem lift_getElem_bv_13 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(13 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[13]!).val[0]!.bv) ((s.st.val[13]!).val[1]!.bv) := by
  show ((lift s).val[13]!).bv = _; exact lift_getElem_bv s ⟨13, by decide⟩
private theorem lift_getElem_bv_14 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(14 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[14]!).val[0]!.bv) ((s.st.val[14]!).val[1]!.bv) := by
  show ((lift s).val[14]!).bv = _; exact lift_getElem_bv s ⟨14, by decide⟩
private theorem lift_getElem_bv_15 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(15 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[15]!).val[0]!.bv) ((s.st.val[15]!).val[1]!.bv) := by
  show ((lift s).val[15]!).bv = _; exact lift_getElem_bv s ⟨15, by decide⟩
private theorem lift_getElem_bv_16 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(16 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[16]!).val[0]!.bv) ((s.st.val[16]!).val[1]!.bv) := by
  show ((lift s).val[16]!).bv = _; exact lift_getElem_bv s ⟨16, by decide⟩
private theorem lift_getElem_bv_17 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(17 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[17]!).val[0]!.bv) ((s.st.val[17]!).val[1]!.bv) := by
  show ((lift s).val[17]!).bv = _; exact lift_getElem_bv s ⟨17, by decide⟩
private theorem lift_getElem_bv_18 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(18 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[18]!).val[0]!.bv) ((s.st.val[18]!).val[1]!.bv) := by
  show ((lift s).val[18]!).bv = _; exact lift_getElem_bv s ⟨18, by decide⟩
private theorem lift_getElem_bv_19 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(19 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[19]!).val[0]!.bv) ((s.st.val[19]!).val[1]!.bv) := by
  show ((lift s).val[19]!).bv = _; exact lift_getElem_bv s ⟨19, by decide⟩
private theorem lift_getElem_bv_20 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(20 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[20]!).val[0]!.bv) ((s.st.val[20]!).val[1]!.bv) := by
  show ((lift s).val[20]!).bv = _; exact lift_getElem_bv s ⟨20, by decide⟩
private theorem lift_getElem_bv_21 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(21 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  show ((lift s).val[21]!).bv = _; exact lift_getElem_bv s ⟨21, by decide⟩
private theorem lift_getElem_bv_22 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(22 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[22]!).val[0]!.bv) ((s.st.val[22]!).val[1]!.bv) := by
  show ((lift s).val[22]!).bv = _; exact lift_getElem_bv s ⟨22, by decide⟩
private theorem lift_getElem_bv_23 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(23 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[23]!).val[0]!.bv) ((s.st.val[23]!).val[1]!.bv) := by
  show ((lift s).val[23]!).bv = _; exact lift_getElem_bv s ⟨23, by decide⟩
private theorem lift_getElem_bv_24 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(24 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[24]!).val[0]!.bv) ((s.st.val[24]!).val[1]!.bv) := by
  show ((lift s).val[24]!).bv = _; exact lift_getElem_bv s ⟨24, by decide⟩

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

/-! Spec-coupling Triple for round-0 θ, in `.holds`-in-post form so it can
    be tagged `@[spec]` and used by `hax_mvcgen` whenever a downstream
    function calls `keccakf1600_round0_theta`. The post says: for the
    `r_impl` produced by impl-θ, the spec computation
    `theta_unrolled (lift s)` succeeds with result equal to
    `lift_theta_applied r_impl`. -/
set_option maxHeartbeats 16000000 in
@[spec]
theorem theta_lift_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r_impl => ⌜
      (do
        let r_spec ← keccak_f.theta_unrolled (lift s)
        pure (r_spec = lift_theta_applied r_impl)).holds ⌝ ⦄ := by
  apply Triple.of_entails_right _ (theta_comp_spec_local s)
  rw [PostCond.entails_noThrow]
  intro r_impl
  intro hpost
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
  unfold Aeneas.Std.Result.holds
  unfold keccak_f.theta_unrolled
  hax_mvcgen
  all_goals try scalar_tac
  -- Main residual: Array.make 25 [r✝²⁴..r✝] = lift_theta_applied r_impl.
  -- Destructure the 12-conjunct theta_comp_spec_local post and the
  -- spec-side chain, then close 25 lanes pointwise via the lifting
  -- algebra (lift_getElem_bv + lift_xor5 + lift_td + lift_rot1).
  obtain ⟨hst, _, hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1,
          hd3z0, hd3z1, hd4z0, hd4z1⟩ := hpost
  apply Subtype.ext
  unfold lift_theta_applied
  simp only [Std.Array.make, hst,
             hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1,
             hd3z0, hd3z1, hd4z0, hd4z1]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
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
    simp only [lift_getElem_bv_0, lift_getElem_bv_1, lift_getElem_bv_2,
      lift_getElem_bv_3, lift_getElem_bv_4, lift_getElem_bv_5,
      lift_getElem_bv_6, lift_getElem_bv_7, lift_getElem_bv_8,
      lift_getElem_bv_9, lift_getElem_bv_10, lift_getElem_bv_11,
      lift_getElem_bv_12, lift_getElem_bv_13, lift_getElem_bv_14,
      lift_getElem_bv_15, lift_getElem_bv_16, lift_getElem_bv_17,
      lift_getElem_bv_18, lift_getElem_bv_19, lift_getElem_bv_20,
      lift_getElem_bv_21, lift_getElem_bv_22, lift_getElem_bv_23,
      lift_getElem_bv_24]
  all_goals simp only [Std.UScalarTy.U64_numBits_eq, ← lift_xor, ← lift_td]

end libcrux_iot_sha3.Equivalence
