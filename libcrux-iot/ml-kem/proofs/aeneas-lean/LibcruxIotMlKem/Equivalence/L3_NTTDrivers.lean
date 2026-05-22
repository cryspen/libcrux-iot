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

end libcrux_iot_ml_kem.Equivalence
