/-
  # `Equivalence/L3_NTTDrivers.lean` — Layer 3 NTT driver-loop Triples.

  L3.x Triples for the `ntt_at_layer_N` driver loops in `ntt.rs`:

  - **L3.1 `ntt_at_layer_1_spec`** — innermost layer: a 16-iter loop over
    a `PolynomialRingElement`'s 16 PortableVectors, each call dispatched
    via the trait's `ntt_layer_1_step` (which forwards to L2.2's
    `vector.portable.ntt.ntt_layer_1_step`). Per-coefficient bound goes
    `7·3328 → 8·3328`; `zeta_i.val : 63 → 127`.
  - **L3.2 `ntt_at_layer_2_spec`** — 2 ζ lookups/iter, dispatches
    `ntt_layer_2_step`. Bound `6·3328 → 7·3328`; `zeta_i : 31 → 63`.
  - **L3.3 `ntt_at_layer_3_spec`** — 1 ζ lookup/iter, dispatches
    `ntt_layer_3_step`. Bound `5·3328 → 6·3328`; `zeta_i : 15 → 31`.

  Specialised to `Vector := PortableVector` with the concrete
  `Libcrux_iot_ml_kemVectorTraitsOperations` instance. The instance's
  `ntt_layer_N_step` field reduces (via `@[reducible]`) to
  `…Operations.ntt_layer_N_step`, which is itself a thin wrapper for
  `vector.portable.ntt.ntt_layer_N_step` — L2.2 / L2.3 / L2.4 fire directly.

  See `Plan.lean § L3.1` (lines 1458-1514) and `§ L3.2 / L3.3` (lines
  1516-1525) for F*-port references.
-/
import LibcruxIotMlKem.Equivalence.L1_VectorElementOps
import LibcruxIotMlKem.Equivalence.L2_NTTSteps

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Equivalence

open Aeneas Aeneas.Std Result ControlFlow Std.Do
open libcrux_iot_ml_kem.Util

/-! ## Inhabited instances — needed for `.val[j]!` projections.

`Std.Array α n` uses `List.get!` under the hood, which requires
`Inhabited α`. The L2/L1 layers don't trigger this because they only
project into `Array I16 16`. The L3 layer projects into `Array
PortableVector 16` and `Array (PolynomialRingElement PortableVector) K`,
so we register the canonical zero-witness instances locally. -/

instance : Inhabited libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  ⟨{ elements := Std.Array.make 16#usize (List.replicate 16 (0#i16 : Std.I16))
        (by simp) }⟩

instance {Vector : Type} [Inhabited Vector] {K : Std.Usize} :
    Inhabited (libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) :=
  ⟨{ coefficients := Std.Array.make 16#usize (List.replicate 16 default) (by simp) }⟩

/-! ## Local helpers — Triple ↔ Result.ok bridges, pure-prop holds. -/

private theorem triple_of_ok_l3 {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

private theorem triple_exists_ok_l3 {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp])

private theorem pure_prop_holds_l3 {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_l3 {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h; exact h trivial

/-! ## Small `Usize.add` helper — produces `.val`-form equations. -/

private theorem usize_add_ok_eq (x y : Std.Usize)
    (h_max : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  have hT := Std.Usize.add_spec h_max
  -- hT : x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ — this is `WP.spec`, not Triple.
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  refine ⟨z, h_eq, ?_⟩
  show z.val = x.val + y.val
  exact h_v

/-! ## `polynomial.zeta_spec` helper

The `ZETAS_TIMES_MONTGOMERY_R` table has 128 `Std.I16` entries. Each is
in absolute value at most 1664 (in fact, all entries here are < 1700;
each fits in a Montgomery-reduced field element). `polynomial.zeta i`
performs a single bounded `Array.index_usize` on that table.

We expose this through a single decidable bound: the table's underlying
`.val` (a 128-element `List Std.I16`) has every element ≤ 1664 in
absolute value. After unsealing the `@[irreducible]` table this is a
finite check that `decide` discharges.
-/

unseal libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R in
private theorem ZETAS_TIMES_MONTGOMERY_R_bound :
    ∀ i : Nat, i < 128 →
      ((libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).val[i]!).val.natAbs ≤ 1664 := by
  intro i hi
  interval_cases i <;> decide

@[spec]
theorem polynomial.zeta_spec (i : Std.Usize) (hi : i.val < 128) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.zeta i
    ⦃ ⇓ r => ⌜ r.val.natAbs ≤ 1664 ⌝ ⦄ := by
  -- `polynomial.zeta i = Array.index_usize ZETAS_TIMES_MONTGOMERY_R i`.
  have h_len :
      (libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).length = 128 :=
    Std.Array.length_eq _
  have h_idx :
      Aeneas.Std.Array.index_usize
        libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R i
      = .ok ((libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).val[i.val]!) :=
    array_index_usize_ok_eq _ i (by rw [h_len]; exact hi)
  have h_ok :
      libcrux_iot_ml_kem.polynomial.zeta i
        = .ok ((libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).val[i.val]!) := by
    unfold libcrux_iot_ml_kem.polynomial.zeta
    rw [h_idx]
  exact triple_of_ok_l3 h_ok (ZETAS_TIMES_MONTGOMERY_R_bound i.val hi)

/-! ## L3.1 — `ntt_at_layer_1_spec`

Driver loop: 16 iterations over `re.coefficients`. Each iteration reads
`re.coefficients[k]` (a `PortableVector`), looks up four ζ-values via
`polynomial.zeta` (indices `zeta_i.val + 1 .. zeta_i.val + 4`),
dispatches `OpsInst.ntt_layer_1_step`, and writes back. `zeta_i.val`
advances by 4; the bound per coefficient goes `7·3328 → 8·3328`.

We specialise to `Vector := PortableVector` and the concrete trait
instance. The `@[reducible]` instance field reduces
`OpsInst.ntt_layer_1_step a z0 z1 z2 z3` to
`vector.portable.ntt.ntt_layer_1_step a z0 z1 z2 z3` (mod a trivial
`Result.ok` wrap), which is L2.2's target.

Loop invariant after `k` iterations (`k.val ∈ [0, 16]`), state
`(cur_zeta_i, cur_re)`:
  - `cur_zeta_i.val = 63 + 4 * k.val`
  - For `j < k.val`, all 16 elements of
    `cur_re.coefficients[j]` are bounded by `8 * 3328`.
  - For `j ≥ k.val`, `cur_re.coefficients[j] = re.coefficients[j]`
    (so per `h_pre`, all 16 elements are bounded by `7 * 3328`). -/

namespace L3_1

open libcrux_iot_ml_kem.Util Aeneas.Std Result ControlFlow

/-- Step-local accumulator type — explicitly named to keep `loop_range_spec_usize`'s
    `β` parameter mounted to a concrete type for inference. -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Loop invariant. -/
def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = 63 + 4 * k.val
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 8 * 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

/-- Step post (named to keep the `match` constant canonical across sites). -/
def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((core_models.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re iter'.start acc').holds
  | .done y => (inv re 16#usize y).holds

end L3_1

/-- Per-iteration step lemma: each body call advances `zeta_i` by 4 and
    transforms `re.coefficients[k]` from a `≤ 7·3328` PortableVector to
    a `≤ 8·3328` one (preserving all other indices and the bound chain). -/
private theorem ntt_at_layer_1_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 7 * 3328)
    (acc : L3_1.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_zeta_acc : acc.1.val = 63 + 4 * k.val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 8 * 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ L3_1.step_post re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    -- 1) `zeta_i + 1`.
    -- Bound chain: acc.1.val = 63 + 4*k.val with k.val < 16, so
    -- acc.1.val ≤ 123 and acc.1.val + 4 ≤ 127. Each Usize.add stays
    -- well within Std.Usize.max (≥ 2^32 - 1).
    have h_acc1_lt : acc.1.val ≤ 123 := by rw [h_zeta_acc]; omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_um3 : (3#usize : Std.Usize).val = 3 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      usize_add_ok_eq acc.1 1#usize h_z_max
    -- 2) `Array.index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    -- zi1.val arithmetic: zi1.val = acc.1.val + 1 = 64 + 4*k.val ≤ 124.
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by rw [h_zi1_val_arith]; omega
    -- 3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi1 h_zi1_lt)
    -- 4) `zi1 + 1`.
    have h_zi3_max : zi1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      usize_add_ok_eq zi1 1#usize h_zi3_max
    have h_zi3_val_arith : zi3.val = acc.1.val + 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]
    have h_zi3_lt : zi3.val < 128 := by rw [h_zi3_val_arith]; omega
    -- 5) `polynomial.zeta zi3`.
    obtain ⟨z2, h_z2_eq, h_z2_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi3 h_zi3_lt)
    -- 6) `zi1 + 2`.
    have h_zi5_max : zi1.val + (2#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um2]; scalar_tac
    obtain ⟨zi5, h_zi5_eq, h_zi5_val⟩ :=
      usize_add_ok_eq zi1 2#usize h_zi5_max
    have h_zi5_val_arith : zi5.val = acc.1.val + 3 := by
      rw [h_zi5_val, h_um2, h_zi1_val_arith]
    have h_zi5_lt : zi5.val < 128 := by rw [h_zi5_val_arith]; omega
    -- 7) `polynomial.zeta zi5`.
    obtain ⟨z3, h_z3_eq, h_z3_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi5 h_zi5_lt)
    -- 8) `zi1 + 3`.
    have h_zi7_max : zi1.val + (3#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um3]; scalar_tac
    obtain ⟨zi7, h_zi7_eq, h_zi7_val⟩ :=
      usize_add_ok_eq zi1 3#usize h_zi7_max
    have h_zi7_val_arith : zi7.val = acc.1.val + 4 := by
      rw [h_zi7_val, h_um3, h_zi1_val_arith]
    have h_zi7_lt : zi7.val < 128 := by rw [h_zi7_val_arith]; omega
    -- 9) `polynomial.zeta zi7`.
    obtain ⟨z4, h_z4_eq, h_z4_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi7 h_zi7_lt)
    -- 10) `OpsInst.ntt_layer_1_step t z1 z2 z3 z4`. Reduces via the
    -- @[reducible] instance to `vector.portable.ntt.ntt_layer_1_step`,
    -- to which L2.2 applies. Pre: t's elements ≤ 7·3328 (it's
    -- `re.coefficients[k]` via h_acc_undone + h_pre).
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 7 * 3328 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_bd⟩ :=
      triple_exists_ok_l3 (ntt_layer_1_step_spec t z1 z2 z3 z4
        h_z1_bd h_z2_bd h_z3_bd h_z4_bd h_t_bd)
    -- Set the next-state values.
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.2.coefficients.set k t1 with ha_def
    set acc' : L3_1.Acc := (zi7, { coefficients := a }) with hacc'_def
    -- Compose the whole body into one `.ok` equation.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : core_models.ops.range.Range Std.Usize),
                     acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      -- Force complete let-Prod-match-on-Some normalization via plain
      -- `simp` (NOT `simp only`) — this engages β-iota reductions that
      -- `simp only` skips. Compose all step hypotheses simultaneously.
      simp [bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq, h_zi3_eq,
            h_z2_eq, h_zi5_eq, h_z3_eq, h_zi7_eq, h_z4_eq]
      -- After simp, only the final `OpsInst.ntt_layer_1_step` remains
      -- (the trait instance's outer `do`-wrapper is `@[reducible]` and
      -- forwards to `vector.portable.ntt.ntt_layer_1_step`; simp doesn't
      -- unfold by default). Unfold the instance projection definitionally,
      -- then close via `h_t1_eq`.
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step t z1 z2 z3 z4
            ok (cont (({ start := s, «end» := 16#usize }
                        : core_models.ops.range.Range Std.Usize),
                      zi7,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l3 h_body
    show L3_1.step_post re k
      (.cont (({ start := s, «end» := 16#usize }
                : core_models.ops.range.Range Std.Usize),
              acc'))
    unfold L3_1.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    -- Now: invariant at (s, acc').
    apply pure_prop_holds_l3
    -- Three conjuncts of L3_1.inv at (s, acc').
    refine ⟨?_, ?_, ?_⟩
    · -- acc'.1.val = zi7.val = 63 + 4 * s.val.
      show zi7.val = 63 + 4 * s.val
      rw [h_zi7_val_arith, h_zeta_acc, hs_val]; ring
    · -- All j < s.val are bounded by 8*3328.
      intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · -- j < k.val: unchanged by the set, use h_acc_done.
        have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.2.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · -- j = k.val: it's t1.
        subst hj_eq_k
        have h_lt' : k.val < acc.2.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.2.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.2.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · -- All j ≥ s.val are unchanged.
      intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    -- Need (acc.1, acc.2) = acc as a pair; for a Prod, this is definitional.
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_l3 h_body
    show L3_1.step_post re k (.done acc)
    unfold L3_1.step_post
    show (L3_1.inv re 16#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_eq] at h_zeta_acc; rw [show (16#usize : Std.Usize).val = 16 from rfl]
      exact h_zeta_acc
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_1_spec
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_coefficient_bound : Std.Usize)
    (h_zeta : zeta_i.val = 63)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 7 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re initial_coefficient_bound
    ⦃ ⇓ p => ⌜ p.1.val = 127
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 8 * 3328 ⌝ ⦄ := by
  -- Reduce the top wrapper to the inner loop.
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1.1 acc1.2)
      (β := L3_1.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (L3_1.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l3 ⟨by rw [h_zeta]; rfl,
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · -- Post entailment.
    rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨?_, ?_⟩
    · have h16 : (16#usize : Std.Usize).val = 16 := rfl
      rw [h16] at h_zeta_eq; omega
    · intro i hi j hj
      apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · -- Step lemma application.
    intro acc k h_ge h_le hinv
    obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_1_step_lemma re h_pre acc k h_le h_zeta_acc
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : L3_1.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L3_1.step_post] using hP
    · have hP : L3_1.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L3_1.step_post] using hP

/-! ## L3.2 — `ntt_at_layer_2_spec`

Driver loop: 16 iterations over `re.coefficients`. Each iteration reads
`re.coefficients[k]` (a `PortableVector`), looks up two ζ-values via
`polynomial.zeta` (indices `zeta_i.val + 1` and `zeta_i.val + 2`),
dispatches `OpsInst.ntt_layer_2_step`, and writes back. `zeta_i.val`
advances by 2 per iter (state stores `zeta_i1 + 1 = zeta_i + 2`); the
bound per coefficient goes `6·3328 → 7·3328`. -/

namespace L3_2

open libcrux_iot_ml_kem.Util Aeneas.Std Result ControlFlow

abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = 31 + 2 * k.val
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 7 * 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((core_models.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re iter'.start acc').holds
  | .done y => (inv re 16#usize y).holds

end L3_2

private theorem ntt_at_layer_2_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 6 * 3328)
    (acc : L3_2.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_zeta_acc : acc.1.val = 31 + 2 * k.val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 7 * 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ L3_2.step_post re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    -- 1) `zeta_i + 1`. Bound chain: acc.1.val = 31 + 2*k.val with
    -- k.val < 16, so acc.1.val ≤ 61 and acc.1.val + 2 ≤ 63.
    have h_acc1_lt : acc.1.val ≤ 61 := by rw [h_zeta_acc]; omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      usize_add_ok_eq acc.1 1#usize h_z_max
    -- 2) `Array.index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    -- zi1.val = acc.1.val + 1 = 32 + 2*k.val ≤ 62 < 128.
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by rw [h_zi1_val_arith]; omega
    -- 3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi1 h_zi1_lt)
    -- 4) `zi1 + 1`.
    have h_zi3_max : zi1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      usize_add_ok_eq zi1 1#usize h_zi3_max
    have h_zi3_val_arith : zi3.val = acc.1.val + 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]
    have h_zi3_lt : zi3.val < 128 := by rw [h_zi3_val_arith]; omega
    -- 5) `polynomial.zeta zi3`.
    obtain ⟨z2, h_z2_eq, h_z2_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi3 h_zi3_lt)
    -- 6) `OpsInst.ntt_layer_2_step t z1 z2`. L2.3 fires after instance
    -- reduces. Pre: t's elements ≤ 6·3328.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 6 * 3328 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_bd⟩ :=
      triple_exists_ok_l3 (ntt_layer_2_step_spec t z1 z2 h_z1_bd h_z2_bd h_t_bd)
    -- Next-state values: state stores `zi3` (= zeta_i + 2).
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.2.coefficients.set k t1 with ha_def
    set acc' : L3_2.Acc := (zi3, { coefficients := a }) with hacc'_def
    -- Compose the whole body into one `.ok` equation.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : core_models.ops.range.Range Std.Usize),
                     acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp [bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq, h_zi3_eq, h_z2_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step t z1 z2
            ok (cont (({ start := s, «end» := 16#usize }
                        : core_models.ops.range.Range Std.Usize),
                      zi3,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l3 h_body
    show L3_2.step_post re k
      (.cont (({ start := s, «end» := 16#usize }
                : core_models.ops.range.Range Std.Usize),
              acc'))
    unfold L3_2.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · -- acc'.1.val = zi3.val = 31 + 2 * s.val.
      show zi3.val = 31 + 2 * s.val
      rw [h_zi3_val_arith, h_zeta_acc, hs_val]; ring
    · intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.2.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · subst hj_eq_k
        have h_lt' : k.val < acc.2.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.2.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.2.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_l3 h_body
    show L3_2.step_post re k (.done acc)
    unfold L3_2.step_post
    show (L3_2.inv re 16#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_eq] at h_zeta_acc; rw [show (16#usize : Std.Usize).val = 16 from rfl]
      exact h_zeta_acc
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_2_spec
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_coefficient_bound : Std.Usize)
    (h_zeta : zeta_i.val = 31)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 6 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re initial_coefficient_bound
    ⦃ ⇓ p => ⌜ p.1.val = 63
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 7 * 3328 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1.1 acc1.2)
      (β := L3_2.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (L3_2.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l3 ⟨by rw [h_zeta]; rfl,
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨?_, ?_⟩
    · have h16 : (16#usize : Std.Usize).val = 16 := rfl
      rw [h16] at h_zeta_eq; omega
    · intro i hi j hj
      apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · intro acc k h_ge h_le hinv
    obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_2_step_lemma re h_pre acc k h_le h_zeta_acc
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : L3_2.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L3_2.step_post] using hP
    · have hP : L3_2.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L3_2.step_post] using hP

/-! ## L3.3 — `ntt_at_layer_3_spec`

Driver loop: 16 iterations over `re.coefficients`. Each iteration reads
`re.coefficients[k]` (a `PortableVector`), looks up one ζ-value via
`polynomial.zeta` (index `zeta_i.val + 1`), dispatches
`OpsInst.ntt_layer_3_step`, and writes back. `zeta_i.val` advances by 1
per iter (state stores `zeta_i1 = zeta_i + 1`); the bound per
coefficient goes `5·3328 → 6·3328`. -/

namespace L3_3

open libcrux_iot_ml_kem.Util Aeneas.Std Result ControlFlow

abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = 15 + k.val
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 6 * 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((core_models.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re iter'.start acc').holds
  | .done y => (inv re 16#usize y).holds

end L3_3

private theorem ntt_at_layer_3_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 5 * 3328)
    (acc : L3_3.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_zeta_acc : acc.1.val = 15 + k.val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 6 * 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ L3_3.step_post re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    -- 1) `zeta_i + 1`. Bound chain: acc.1.val = 15 + k.val with
    -- k.val < 16, so acc.1.val ≤ 30 and acc.1.val + 1 ≤ 31.
    have h_acc1_lt : acc.1.val ≤ 30 := by rw [h_zeta_acc]; omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      usize_add_ok_eq acc.1 1#usize h_z_max
    -- 2) `Array.index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    -- zi1.val = acc.1.val + 1 = 16 + k.val ≤ 31 < 128.
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by rw [h_zi1_val_arith]; omega
    -- 3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi1 h_zi1_lt)
    -- 4) `OpsInst.ntt_layer_3_step t z1`. L2.4 fires after instance
    -- reduces. Pre: t's elements ≤ 5·3328.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 5 * 3328 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_bd⟩ :=
      triple_exists_ok_l3 (ntt_layer_3_step_spec t z1 h_z1_bd h_t_bd)
    -- Next-state values: state stores `zi1` (= zeta_i + 1).
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.2.coefficients.set k t1 with ha_def
    set acc' : L3_3.Acc := (zi1, { coefficients := a }) with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : core_models.ops.range.Range Std.Usize),
                     acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp [bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step t z1
            ok (cont (({ start := s, «end» := 16#usize }
                        : core_models.ops.range.Range Std.Usize),
                      zi1,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l3 h_body
    show L3_3.step_post re k
      (.cont (({ start := s, «end» := 16#usize }
                : core_models.ops.range.Range Std.Usize),
              acc'))
    unfold L3_3.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · -- acc'.1.val = zi1.val = 15 + s.val.
      show zi1.val = 15 + s.val
      rw [h_zi1_val_arith, h_zeta_acc, hs_val]; ring
    · intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.2.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · subst hj_eq_k
        have h_lt' : k.val < acc.2.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.2.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.2.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_l3 h_body
    show L3_3.step_post re k (.done acc)
    unfold L3_3.step_post
    show (L3_3.inv re 16#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_eq] at h_zeta_acc; rw [show (16#usize : Std.Usize).val = 16 from rfl]
      exact h_zeta_acc
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_3_spec
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_coefficient_bound : Std.Usize)
    (h_zeta : zeta_i.val = 15)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 5 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re initial_coefficient_bound
    ⦃ ⇓ p => ⌜ p.1.val = 31
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 6 * 3328 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1.1 acc1.2)
      (β := L3_3.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (L3_3.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l3 ⟨by rw [h_zeta]; rfl,
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨?_, ?_⟩
    · have h16 : (16#usize : Std.Usize).val = 16 := rfl
      rw [h16] at h_zeta_eq; omega
    · intro i hi j hj
      apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · intro acc k h_ge h_le hinv
    obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_3_step_lemma re h_pre acc k h_le h_zeta_acc
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : L3_3.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L3_3.step_post] using hP
    · have hP : L3_3.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L3_3.step_post] using hP

/-! ## L3.5 — `ntt_at_layer_7_spec`

Outermost layer of the forward NTT. No `zeta_i` (single fixed Montgomery
multiplier `-1600`). Driver loop runs 8 iterations (`step = 16/2 = 8`)
over the first half of `re.coefficients`; per iter touches lanes `j`
and `j+8`. Per-coefficient bound goes `3 → 4803` (= `3 + 1600·3`).

Per-iter body (j = k.val, i = j+8, all reads/writes from re/acc):
  scratch1 := re[i]
  scratch2 := -1600 * scratch1                       (L1.7)
  re[i]    := re[j]                                  (lane swap)
  t2       := re[j] + scratch2                       (L1.1)
  re[j]    := t2
  t4       := <re[i] now holds old re[j]> - scratch2 (L1.2)
  re[i]    := t4
So new re[j] = old re[j] + (-1600) * old re[i]; new re[i] = old re[j] -
(-1600) * old re[i] = old re[j] + 1600 * old re[i]. Both bounded by
3 + 4800 = 4803 in absolute value under |old re[*][ℓ]| ≤ 3.

See `Plan.lean § L3.5` (lines 1621–1664) for the F*-port reference. -/

/-! ### Local helpers: `Usize.div` reduction + generic-`«end»` iter-next. -/

private theorem usize_div_ok_eq (x y : Std.Usize) (hy : y.val ≠ 0) :
    ∃ z : Std.Usize, (x / y : Result Std.Usize) = .ok z ∧ z.val = x.val / y.val := by
  have hT := Std.UScalar.div_spec x hy
  obtain ⟨z, h_eq, h_v⟩ := hT
  exact ⟨z, h_eq, h_v⟩

/-- `i.val < e.val`: `IteratorRange.next` returns `.ok (some i, iter')` with
    `iter'.end = e` and `iter'.start.val = i.val + 1`. Generic version of
    `iter_next_some_eq` (which is specialised to `«end» := 16#usize`). -/
private theorem iter_next_some_eq_gen
    (i e : Std.Usize) (h_lt : i.val < e.val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      core_models.iter.range.IteratorRange.next
        core_models.Usize.Insts.Core_modelsIterRangeStep
        ({ start := i, «end» := e } : core_models.ops.range.Range Std.Usize)
      = .ok (some i,
          ({ start := s, «end» := e } : core_models.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      ∃ s : Std.Usize, s.val = i.val + 1
        ∧ oi = (some i,
                ({ start := s, «end» := e }
                  : core_models.ops.range.Range Std.Usize)) ⌝)
    (fun _ s hs => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      exact ⟨s, hs, rfl⟩)
    (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
  obtain ⟨v, hveq, hP⟩ := triple_exists_ok_l3 hT
  obtain ⟨s, hs_val, hpair⟩ := hP
  exact ⟨s, hs_val, by rw [hveq, hpair]⟩

/-- `i.val ≥ e.val`: `IteratorRange.next` returns `.ok (none, _)`. Generic
    version of `iter_next_none_eq`. -/
private theorem iter_next_none_eq_gen
    (i e : Std.Usize) (h_ge : i.val ≥ e.val) :
    core_models.iter.range.IteratorRange.next
      core_models.Usize.Insts.Core_modelsIterRangeStep
      ({ start := i, «end» := e } : core_models.ops.range.Range Std.Usize)
    = .ok ((none : Option Std.Usize),
            ({ start := i, «end» := e }
              : core_models.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      oi = ((none : Option Std.Usize),
            ({ start := i, «end» := e }
              : core_models.ops.range.Range Std.Usize)) ⌝)
    (fun hlt => absurd hlt (Nat.not_lt.mpr h_ge))
    (fun _ => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
  obtain ⟨v, hveq, hP⟩ := triple_exists_ok_l3 hT
  rw [hveq, hP]

namespace L3_5

open libcrux_iot_ml_kem.Util Aeneas.Std Result ControlFlow

/-- Step-local accumulator: a `PolynomialRingElement × scratch`. -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector ×
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Loop invariant after `k` iterations (`k.val ∈ [0, 8]`):
    - Lanes `j ∈ [0, k.val)` are processed: bounded by 4803.
    - Lanes `j ∈ [8, 8 + k.val)` are processed: bounded by 4803.
    - Lanes `j ∈ [k.val, 8)` are untouched: bounded by 3 (from `re`).
    - Lanes `j ∈ [8 + k.val, 16)` are untouched: bounded by 3 (from `re`). -/
def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4803)
    ∧ (∀ j : Nat, 8 ≤ j → j < 8 + k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4803)
    ∧ (∀ j : Nat, k.val ≤ j → j < 8 →
        acc.1.coefficients.val[j]! = re.coefficients.val[j]!)
    ∧ (∀ j : Nat, 8 + k.val ≤ j → j < 16 →
        acc.1.coefficients.val[j]! = re.coefficients.val[j]!))

/-- Per-iter step post. -/
def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((core_models.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (8#usize : Std.Usize).val ∧ iter'.«end» = 8#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re iter'.start acc').holds
  | .done y => (inv re 8#usize y).holds

end L3_5

set_option maxHeartbeats 16000000 in
private theorem ntt_at_layer_7_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3)
    (acc : L3_5.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (8#usize : Std.Usize).val)
    (h_done_lo : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4803)
    (h_done_hi : ∀ j : Nat, 8 ≤ j → j < 8 + k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4803)
    (h_undone_lo : ∀ j : Nat, k.val ≤ j → j < 8 →
        acc.1.coefficients.val[j]! = re.coefficients.val[j]!)
    (h_undone_hi : ∀ j : Nat, 8 + k.val ≤ j → j < 16 →
        acc.1.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      8#usize { start := k, «end» := 8#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ L3_5.step_post re k r ⌝ ⦄ := by
  have h8 : (8#usize : Std.Usize).val = 8 := rfl
  have h_coef_len : acc.1.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
  by_cases h_lt : k.val < (8#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_8 : k.val < 8 := by rw [h8] at h_lt; exact h_lt
    have hk_16 : k.val < 16 := by omega
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq_gen k 8#usize h_lt
    -- 1) `i = j + 8`: where j = k.
    have h_um8 : (8#usize : Std.Usize).val = 8 := rfl
    have h_i_max : k.val + (8#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um8]; scalar_tac
    obtain ⟨i, h_i_eq, h_i_val⟩ := usize_add_ok_eq k 8#usize h_i_max
    have h_i_val_arith : i.val = k.val + 8 := by rw [h_i_val, h_um8]
    have h_i_lt_16 : i.val < 16 := by rw [h_i_val_arith]; omega
    have h_i_lt_coef : i.val < acc.1.coefficients.length := by rw [h_coef_len]; exact h_i_lt_16
    -- 2) Read scratch1 = acc.1[i].
    have h_idx_i :
        Aeneas.Std.Array.index_usize acc.1.coefficients i
          = .ok (acc.1.coefficients.val[i.val]!) :=
      array_index_usize_ok_eq acc.1.coefficients i h_i_lt_coef
    have h_acc_i_eq : acc.1.coefficients.val[i.val]! = re.coefficients.val[i.val]! := by
      apply h_undone_hi i.val
      · rw [h_i_val_arith]; omega
      · exact h_i_lt_16
    have h_scratch1_bd : ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ 3 := by
      intro ℓ hℓ
      rw [h_acc_i_eq]
      exact h_pre i.val h_i_lt_16 ℓ hℓ
    -- 3) scratch2 = multiply_by_constant scratch1 (-1600). L1.7.
    have h_neg1600_val : ((-1600)#i16 : Std.I16).val = -1600 := by decide
    have h_mul_pre : ∀ ℓ : Nat, ℓ < 16 →
        (((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val
            * ((-1600)#i16 : Std.I16).val : Int).natAbs ≤ 2 ^ 15 - 1 := by
      intro ℓ hℓ
      have h_x_abs : ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ 3 :=
        h_scratch1_bd ℓ hℓ
      rw [h_neg1600_val]
      have h_abs_mul : (((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val * (-1600) : Int).natAbs
                       = ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs * 1600 := by
        rw [Int.natAbs_mul]; rfl
      rw [h_abs_mul]
      have h_mul : ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs * 1600
                    ≤ 3 * 1600 :=
        Nat.mul_le_mul_right 1600 h_x_abs
      omega
    obtain ⟨scratch2, h_scratch2_eq, h_scratch2_post⟩ :=
      triple_exists_ok_l3 (multiply_by_constant_spec (acc.1.coefficients.val[i.val]!)
                            ((-1600)#i16 : Std.I16) h_mul_pre)
    have h_scratch2_bd : ∀ ℓ : Nat, ℓ < 16 →
        (scratch2.elements.val[ℓ]!).val
          = (acc.1.coefficients.val[i.val]!).elements.val[ℓ]!.val * (-1600 : Int)
        ∧ (scratch2.elements.val[ℓ]!).val.natAbs ≤ 4800 := by
      intro ℓ hℓ
      have h_per := h_scratch2_post ℓ hℓ
      have h_v_eq : (scratch2.elements.val[ℓ]!).val
                      = (acc.1.coefficients.val[i.val]!).elements.val[ℓ]!.val * (-1600 : Int) := by
        rw [h_per.1, h_neg1600_val]
      refine ⟨h_v_eq, ?_⟩
      have h_x_abs : ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ 3 :=
        h_scratch1_bd ℓ hℓ
      have h_abs_eq : (scratch2.elements.val[ℓ]!).val.natAbs
                      = ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs * 1600 := by
        rw [h_v_eq, Int.natAbs_mul]; rfl
      rw [h_abs_eq]
      have h_mul : ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs * 1600
                    ≤ 3 * 1600 :=
        Nat.mul_le_mul_right 1600 h_x_abs
      omega
    -- 4) t = re.coefficients[j] = acc.1.coef[k]!
    have h_k_lt_coef : k.val < acc.1.coefficients.length := by rw [h_coef_len]; exact hk_16
    have h_idx_k :
        Aeneas.Std.Array.index_usize acc.1.coefficients k
          = .ok (acc.1.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.1.coefficients k h_k_lt_coef
    have h_acc_k_eq : acc.1.coefficients.val[k.val]! = re.coefficients.val[k.val]! :=
      h_undone_lo k.val (Nat.le_refl _) hk_8
    -- Per-element bound at lane k: ≤ 3 from h_pre via h_acc_k_eq.
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[k.val]!).elements.val[ℓ]!).val.natAbs ≤ 3 := by
      intro ℓ hℓ
      rw [h_acc_k_eq]
      exact h_pre k.val hk_16 ℓ hℓ
    -- Set t (for readability in downstream bounds).
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.1.coefficients.val[k.val]! with ht_def
    -- 5) a = acc.1.coef.set i t.
    have h_upd_i :
        Aeneas.Std.Array.update acc.1.coefficients i t
          = .ok (acc.1.coefficients.set i t) :=
      array_update_ok_eq acc.1.coefficients i t h_i_lt_coef
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.1.coefficients.set i t with ha_def
    -- 6) (t1, back1) = index_mut_usize a j.
    have h_a_k_lt : k.val < a.length := by
      change k.val < (acc.1.coefficients.set i t).length
      rw [Std.Array.set_length]; rw [h_coef_len]; exact hk_16
    have h_a_k_idx :
        Aeneas.Std.Array.index_usize a k = .ok (a.val[k.val]!) :=
      array_index_usize_ok_eq a k h_a_k_lt
    have h_imt_a_k :
        Aeneas.Std.Array.index_mut_usize a k = .ok (a.val[k.val]!, a.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_a_k_idx]; rfl
    have h_k_ne_i : k.val ≠ i.val := by rw [h_i_val_arith]; omega
    have h_i_ne_k : i.val ≠ k.val := fun h => h_k_ne_i h.symm
    have h_a_k_val_eq : a.val[k.val]! = acc.1.coefficients.val[k.val]! := by
      change (acc.1.coefficients.set i t).val[k.val]! = acc.1.coefficients.val[k.val]!
      have h_ne : (acc.1.coefficients.set i t)[k.val]! = (acc.1.coefficients)[k.val]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i k.val t h_i_ne_k
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_ne
    -- t1 = a.val[k.val]! (result of index_mut). Bound: t1 = acc.1.coef[k]! = t.
    have h_t1_eq_t : a.val[k.val]! = t := by
      change a.val[k.val]! = acc.1.coefficients.val[k.val]!
      exact h_a_k_val_eq
    have h_add_pre : ∀ ℓ : Nat, ℓ < 16 →
        (((a.val[k.val]!).elements.val[ℓ]!).val + (scratch2.elements.val[ℓ]!).val : Int).natAbs
          ≤ 2 ^ 15 - 1 := by
      intro ℓ hℓ
      rw [h_t1_eq_t]
      have h_t_b := h_t_bd ℓ hℓ
      have h_s2_b := (h_scratch2_bd ℓ hℓ).2
      have h_t_int_lb : -(3 : Int) ≤ (t.elements.val[ℓ]!).val := by omega
      have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ (3 : Int) := by omega
      have h_s2_int_lb : -(4800 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
      have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (4800 : Int) := by omega
      omega
    obtain ⟨t2, h_t2_eq, h_t2_post⟩ :=
      triple_exists_ok_l3 (add_spec (a.val[k.val]!) scratch2 h_add_pre)
    have h_t2_bd : ∀ ℓ : Nat, ℓ < 16 → (t2.elements.val[ℓ]!).val.natAbs ≤ 4803 := by
      intro ℓ hℓ
      have h_per := h_t2_post ℓ hℓ
      have h_v := h_per.1
      rw [h_t1_eq_t] at h_v
      have h_t_b := h_t_bd ℓ hℓ
      have h_s2_b := (h_scratch2_bd ℓ hℓ).2
      have h_t_int_lb : -(3 : Int) ≤ (t.elements.val[ℓ]!).val := by omega
      have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ (3 : Int) := by omega
      have h_s2_int_lb : -(4800 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
      have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (4800 : Int) := by omega
      omega
    -- 8/9) a1 = a.set k t2 (definitional); (t3, back2) = index_mut_usize a1 i.
    -- Use `have ... : ... := ` to define a1 as a syntactically-distinct term,
    -- but state the index_mut hypothesis directly with `a.set k t2` so simp
    -- can match the goal pattern.
    have h_a1_i_lt : i.val < (a.set k t2).length := by
      rw [Std.Array.set_length]
      change i.val < (acc.1.coefficients.set i t).length
      rw [Std.Array.set_length, h_coef_len]; exact h_i_lt_16
    have h_a1_i_idx :
        Aeneas.Std.Array.index_usize (a.set k t2) i
          = .ok ((a.set k t2).val[i.val]!) :=
      array_index_usize_ok_eq (a.set k t2) i h_a1_i_lt
    have h_imt_a1_i :
        Aeneas.Std.Array.index_mut_usize (a.set k t2) i
          = .ok ((a.set k t2).val[i.val]!, (a.set k t2).set i) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_a1_i_idx]; rfl
    have h_a1_i_val_eq : (a.set k t2).val[i.val]! = t := by
      have h_set_k_ne : (a.set k t2)[i.val]! = a[i.val]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne a k i.val t2 h_k_ne_i
      have h_a_i_eq : a[i.val]! = t := by
        change (acc.1.coefficients.set i t)[i.val]! = t
        exact Aeneas.Std.Array.getElem!_Nat_set_eq acc.1.coefficients i i.val t ⟨rfl, h_i_lt_coef⟩
      have h_chain : (a.set k t2).val[i.val]! = a.val[i.val]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_k_ne
      rw [h_chain]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_a_i_eq
    -- 10) t4 = sub t3 scratch2. State with the raw `a.set k t2` term (no `let a1`).
    have h_sub_pre : ∀ ℓ : Nat, ℓ < 16 →
        ((((a.set k t2).val[i.val]!).elements.val[ℓ]!).val
          - (scratch2.elements.val[ℓ]!).val : Int).natAbs ≤ 2 ^ 15 - 1 := by
      intro ℓ hℓ
      rw [h_a1_i_val_eq]
      have h_t_b := h_t_bd ℓ hℓ
      have h_s2_b := (h_scratch2_bd ℓ hℓ).2
      have h_t_int_lb : -(3 : Int) ≤ (t.elements.val[ℓ]!).val := by omega
      have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ (3 : Int) := by omega
      have h_s2_int_lb : -(4800 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
      have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (4800 : Int) := by omega
      omega
    obtain ⟨t4, h_t4_eq, h_t4_post⟩ :=
      triple_exists_ok_l3 (sub_spec ((a.set k t2).val[i.val]!) scratch2 h_sub_pre)
    have h_t4_bd : ∀ ℓ : Nat, ℓ < 16 → (t4.elements.val[ℓ]!).val.natAbs ≤ 4803 := by
      intro ℓ hℓ
      have h_per := h_t4_post ℓ hℓ
      have h_v := h_per.1
      rw [h_a1_i_val_eq] at h_v
      have h_t_b := h_t_bd ℓ hℓ
      have h_s2_b := (h_scratch2_bd ℓ hℓ).2
      have h_t_int_lb : -(3 : Int) ≤ (t.elements.val[ℓ]!).val := by omega
      have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ (3 : Int) := by omega
      have h_s2_int_lb : -(4800 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
      have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (4800 : Int) := by omega
      omega
    -- Introduce a1 alias AFTER stating h_t4_eq (so h_t4_eq has raw form).
    let a1 : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a.set k t2
    have ha1_def : a1 = a.set k t2 := rfl
    -- 11) a2 = a1.set i t4.
    set a2 : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a1.set i t4 with ha2_def
    set acc' : L3_5.Acc := ({ coefficients := a2 }, scratch2) with hacc'_def
    -- Compose into a single .ok equation.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          8#usize { start := k, «end» := 8#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 8#usize }
                        : core_models.ops.range.Range Std.Usize),
                     acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 8#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 8#usize }
                  : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      -- L3.1's pattern: full `simp` reduces match-on-Some + lets + Prod-binds
      -- and threads all arithmetic equations in one call. Disable two simp
      -- lemmas that would push the goal into a form our hypotheses don't match:
      --  * `List.getElem!_eq_getElem?_getD` — would unfold `[i]!` to `?.getD default`.
      --  * `Std.Array.set_val_eq` — would push `↑` inside `(a.set i x)` to
      --    yield `(↑a).set (↑i) x`, breaking the `(a.set k t2).val[i.val]!`
      --    pattern in our index_mut hypothesis.
      simp [-List.getElem!_eq_getElem?_getD, -Std.Array.set_val_eq,
        bind_tc_ok,
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.multiply_by_constant,
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.add,
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.sub,
        h_i_eq, h_idx_i, h_scratch2_eq, h_idx_k, h_upd_i, h_imt_a_k, h_t2_eq,
        h_imt_a1_i, h_t4_eq]
      -- Goal collapses to `({coefficients := (a.set k t2).set i t4}, scratch2) = acc'`;
      -- `acc'` is `({coefficients := (a.set k t2).set i t4}, scratch2)` definitionally
      -- (via the `let`-chain a1 = a.set k t2, a2 = a1.set i t4).
      rfl
    apply triple_of_ok_l3 h_body
    show L3_5.step_post re k
      (.cont (({ start := s, «end» := 8#usize }
                : core_models.ops.range.Range Std.Usize),
              acc'))
    unfold L3_5.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lanes j ∈ [0, s.val): processed.
      intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · -- j < k: unchanged by both writes.
        have h_k_ne_j : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_i_ne_j : i.val ≠ j := by rw [h_i_val_arith]; omega
        have h_chain :
            acc'.1.coefficients.val[j]! = acc.1.coefficients.val[j]! := by
          show (a1.set i t4).val[j]! = acc.1.coefficients.val[j]!
          have h1 : (a1.set i t4)[j]! = a1[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a1 i j t4 h_i_ne_j
          have h2 : (a.set k t2)[j]! = a[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_k_ne_j
          have h3 : (acc.1.coefficients.set i t)[j]! = (acc.1.coefficients)[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i j t h_i_ne_j
          have h1' : (a1.set i t4).val[j]! = a1.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
          have h2' : a1.val[j]! = a.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
          have h3' : a.val[j]! = acc.1.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h3
          rw [h1', h2', h3']
        rw [h_chain]
        exact h_done_lo j hj_lt_k ℓ hℓ
      · -- j = k: new value is t2.
        subst hj_eq_k
        have h_chain : acc'.1.coefficients.val[k.val]! = t2 := by
          show (a1.set i t4).val[k.val]! = t2
          have h1 : (a1.set i t4)[k.val]! = a1[k.val]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a1 i k.val t4 h_i_ne_k
          have h1' : (a1.set i t4).val[k.val]! = a1.val[k.val]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
          rw [h1']
          show (a.set k t2).val[k.val]! = t2
          have h2 : (a.set k t2)[k.val]! = t2 :=
            Aeneas.Std.Array.getElem!_Nat_set_eq a k k.val t2 ⟨rfl, h_a_k_lt⟩
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
        rw [h_chain]
        exact h_t2_bd ℓ hℓ
    · -- Lanes j ∈ [8, 8 + s.val): processed.
      intro j hj_lo hj_hi ℓ hℓ
      rw [hs_val] at hj_hi
      have hj_lt : j < 8 + k.val + 1 := by omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj_lt with hj_lt_ki | hj_eq_ki
      · -- j ∈ [8, 8 + k.val): unchanged by both writes.
        have h_k_ne_j : k.val ≠ j := by omega
        have h_i_ne_j : i.val ≠ j := by rw [h_i_val_arith]; omega
        have h_chain :
            acc'.1.coefficients.val[j]! = acc.1.coefficients.val[j]! := by
          show (a1.set i t4).val[j]! = acc.1.coefficients.val[j]!
          have h1 : (a1.set i t4)[j]! = a1[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a1 i j t4 h_i_ne_j
          have h2 : (a.set k t2)[j]! = a[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_k_ne_j
          have h3 : (acc.1.coefficients.set i t)[j]! = (acc.1.coefficients)[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i j t h_i_ne_j
          have h1' : (a1.set i t4).val[j]! = a1.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
          have h2' : a1.val[j]! = a.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
          have h3' : a.val[j]! = acc.1.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h3
          rw [h1', h2', h3']
        rw [h_chain]
        exact h_done_hi j hj_lo hj_lt_ki ℓ hℓ
      · -- j = 8 + k.val = i.val: new value is t4.
        have hj_eq_i : j = i.val := by rw [h_i_val_arith]; omega
        subst hj_eq_i
        have h_chain : acc'.1.coefficients.val[i.val]! = t4 := by
          show (a1.set i t4).val[i.val]! = t4
          have h1 : (a1.set i t4)[i.val]! = t4 :=
            Aeneas.Std.Array.getElem!_Nat_set_eq a1 i i.val t4 ⟨rfl, h_a1_i_lt⟩
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
        rw [h_chain]
        exact h_t4_bd ℓ hℓ
    · -- Lanes j ∈ [s.val, 8): untouched.
      intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_k_lt_j : k.val < j := by omega
      have h_k_ne_j : k.val ≠ j := by omega
      have h_i_ne_j : i.val ≠ j := by rw [h_i_val_arith]; omega
      have h_chain :
          acc'.1.coefficients.val[j]! = acc.1.coefficients.val[j]! := by
        show (a1.set i t4).val[j]! = acc.1.coefficients.val[j]!
        have h1 : (a1.set i t4)[j]! = a1[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne a1 i j t4 h_i_ne_j
        have h2 : (a.set k t2)[j]! = a[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_k_ne_j
        have h3 : (acc.1.coefficients.set i t)[j]! = (acc.1.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i j t h_i_ne_j
        have h1' : (a1.set i t4).val[j]! = a1.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
        have h2' : a1.val[j]! = a.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
        have h3' : a.val[j]! = acc.1.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h3
        rw [h1', h2', h3']
      rw [h_chain]
      have h_undone_j : k.val ≤ j := by omega
      exact h_undone_lo j h_undone_j hj_lt
    · -- Lanes j ∈ [8 + s.val, 16): untouched.
      intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_i_lt_j : i.val < j := by rw [h_i_val_arith]; omega
      have h_k_ne_j : k.val ≠ j := by omega
      have h_i_ne_j : i.val ≠ j := by omega
      have h_chain :
          acc'.1.coefficients.val[j]! = acc.1.coefficients.val[j]! := by
        show (a1.set i t4).val[j]! = acc.1.coefficients.val[j]!
        have h1 : (a1.set i t4)[j]! = a1[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne a1 i j t4 h_i_ne_j
        have h2 : (a.set k t2)[j]! = a[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_k_ne_j
        have h3 : (acc.1.coefficients.set i t)[j]! = (acc.1.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i j t h_i_ne_j
        have h1' : (a1.set i t4).val[j]! = a1.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
        have h2' : a1.val[j]! = a.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
        have h3' : a.val[j]! = acc.1.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h3
        rw [h1', h2', h3']
      rw [h_chain]
      have h_undone_j : 8 + k.val ≤ j := by omega
      exact h_undone_hi j h_undone_j hj_lt
  · -- None branch (k ≥ 8).
    have hk_ge : k.val ≥ (8#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 8 := by rw [h8] at hk_ge; omega
    have h_iter_none := iter_next_none_eq_gen k 8#usize hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          8#usize { start := k, «end» := 8#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 8#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 8#usize }
                  : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_l3 h_body
    show L3_5.step_post re k (.done acc)
    unfold L3_5.step_post
    show (L3_5.inv re 8#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj ℓ hℓ
      rw [show (8#usize : Std.Usize).val = 8 from rfl] at hj
      apply h_done_lo j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_lo hj_hi ℓ hℓ
      rw [show (8#usize : Std.Usize).val = 8 from rfl] at hj_hi
      apply h_done_hi j hj_lo _ ℓ hℓ; rw [hk_eq]; exact hj_hi
    · intro j hj_ge hj_lt
      rw [show (8#usize : Std.Usize).val = 8 from rfl] at hj_ge
      apply h_undone_lo j _ hj_lt; rw [hk_eq]; exact hj_ge
    · intro j hj_ge hj_lt
      rw [show (8#usize : Std.Usize).val = 8 from rfl] at hj_ge
      apply h_undone_hi j _ hj_lt; rw [hk_eq]; exact hj_ge

private theorem vectors_in_ring_element_eq :
    libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT = .ok (16#usize : Std.Usize) := by
  unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
  unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
  unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
  rfl

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_7_spec
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_7
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      re scratch
    ⦃ ⇓ p => ⌜ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                ((p.1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 4803 ⌝ ⦄ := by
  -- Reduce the top wrapper: i = VECTORS_IN_RING_ELEMENT = 16#usize, step = i/2 = 8#usize.
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7
  rw [vectors_in_ring_element_eq]
  simp only [bind_tc_ok]
  -- step = 16#usize / 2#usize = 8#usize.
  have h_two_nz : (2#usize : Std.Usize).val ≠ 0 := by decide
  obtain ⟨step, h_step_eq, h_step_val⟩ :=
    usize_div_ok_eq (16#usize : Std.Usize) (2#usize : Std.Usize) h_two_nz
  have h_step_val_8 : step.val = 8 := by
    rw [h_step_val]; decide
  have h_step_eq_8 : step = 8#usize := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_step_val_8]; rfl
  rw [h_step_eq]
  simp only [bind_tc_ok]
  rw [h_step_eq_8]
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          8#usize iter1 acc1.1 acc1.2)
      (β := L3_5.Acc)
      (re, scratch)
      0#usize 8#usize
      (L3_5.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (8#usize : Std.Usize).val)
      (pure_prop_holds_l3
        ⟨fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
         fun j _hj_lo hj_hi _ _ => by
            have h0 : (0#usize : Std.Usize).val = 0 := rfl
            rw [h0] at hj_hi
            omega,
         fun _ _ _ => rfl,
         fun _ _ _ => rfl⟩)
      ?_)
  · -- Post entailment.
    rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_done_lo, h_done_hi, _h_undone_lo, _h_undone_hi⟩ := of_pure_prop_holds_l3 h
    intro i hi j hj
    have h8 : (8#usize : Std.Usize).val = 8 := rfl
    by_cases hi_lt_8 : i < 8
    · apply h_done_lo i (by rw [h8]; exact hi_lt_8) j hj
    · have hi_ge_8 : 8 ≤ i := Nat.not_lt.mp hi_lt_8
      apply h_done_hi i hi_ge_8 (by rw [h8]; omega) j hj
  · -- Step lemma application.
    intro acc k h_ge h_le hinv
    obtain ⟨h_done_lo, h_done_hi, h_undone_lo, h_undone_hi⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_7_step_lemma re h_pre acc k h_le
                    h_done_lo h_done_hi h_undone_lo h_undone_hi
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : L3_5.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L3_5.step_post] using hP
    · have hP : L3_5.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L3_5.step_post] using hP

end libcrux_iot_ml_kem.Equivalence
