/-
  I32 iterator + loop specs for `keccak.keccakf1600_loop`, plus the
  loop-equivalence theorem.

  Mirrors `LoopEquivalence/Spec.lean`'s Usize iterator/loop spec
  template, adapted to the `Std.I32` Step instance in
  `Extraction/Missing.lean:25`.

  ## Composability note

  `four_round_equiv s` proves `spec_4(lift s) = lift_perm r id impl_swap`.
  To chain it across 6 iterations, the previous chunk's spec output
  (`lift_perm s_iter id impl_swap`) must equal the next chunk's spec
  input (`lift s_iter`). This requires `lift s_iter = lift_perm s_iter
  id impl_swap` at every iteration boundary, which we encode as a
  precondition (`h_lift`) on the initial state and a preservation
  lemma (`keccakf1600_4rounds_preserves_lift_eq`).
-/
import LibcruxIotSha3.Equivalence.Keccakf1600

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## I32 iterator-next spec

The `core_models.I32.Insts.Core_modelsIterRangeStep` instance (defined
in `Extraction/Missing.lean:25`) uses `IScalar.tryMk .I32 (start.val +
1)` for `forward_checked`. For our use case (range `[0, 6)`), the
bounds are well within I32 and `tryMk` succeeds. -/

theorem IteratorRange_next_spec_i32 (i e : Std.I32)
    (h_e_lt_max : e.val < 2^31) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Std.I32), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.iter.range.IteratorRange.next core_models.I32.Insts.Core_modelsIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core_models.iter.range.IteratorRange.next
  unfold core_models.I32.Insts.Core_modelsIterRangeStep
  by_cases h : i.val < e.val
  · -- i < e: partial_cmp returns Less, forward_checked succeeds (i+1 ≤ e < 2^31).
    have hbnd : i.val + 1 < 2^31 := by omega
    have hi_min := i.hBounds.1
    have hbnd_lo : -(2^31 : Int) ≤ i.val + 1 := by
      simp only [Std.IScalar.min, Std.IScalarTy.numBits] at hi_min
      omega
    have h_lt' := h_lt h
    simp_all [compare, compareOfLessAndEq]
    have hck := Std.IScalar.tryMk_eq Std.IScalarTy.I32 (i.val + 1)
    cases hres : Std.IScalar.tryMk Std.IScalarTy.I32 (i.val + 1) with
    | ok s =>
        rw [hres] at hck
        obtain ⟨hsv, _⟩ := hck
        simp only [Option.ofResult]
        mvcgen
        exact h_lt' s hsv
    | fail _ =>
        rw [hres] at hck
        simp at hck
        omega
    | div =>
        rw [hres] at hck
        exact absurd hck (by exact False.elim)
  · -- i ≥ e: partial_cmp returns Equal or Greater (not Less); branch returns
    -- `.ok (none, range)` directly without invoking forward_checked.
    have hle : e.val ≤ i.val := Int.not_lt.mp h
    have h_ge' := h_ge hle
    -- The boolean condition `isLess` evaluates to `false` under `¬ (i < e)`.
    have hisLess_false :
        (match
          (match if i.val < e.val then Ordering.lt
                  else if i.val = e.val then Ordering.eq else Ordering.gt with
           | Ordering.lt => core_models.cmp.Ordering.Less
           | Ordering.eq => core_models.cmp.Ordering.Equal
           | Ordering.gt => core_models.cmp.Ordering.Greater) with
          | core_models.cmp.Ordering.Less => true
          | _ => false) = false := by
      simp only [if_neg h]
      by_cases hieq : i.val = e.val <;> simp [hieq]
    simp_all [compare, compareOfLessAndEq]
    mvcgen
    all_goals first
      | exact h_ge'
      | (exfalso
         rename_i hLess _ _
         have : false = true := hisLess_false.symm.trans hLess
         exact absurd this (by decide))
      | (exfalso
         rename_i hLess _
         have : false = true := hisLess_false.symm.trans hLess
         exact absurd this (by decide))

/-! ## I32 loop-over-range spec

Specialized to `loop` over `core.ops.range.Range I32`. -/

section loop_range_i32_helpers

private abbrev ResultPS := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_i32 {α : Type} {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp] using h

private theorem triple_noThrow_exists_ok_i32 {α : Type} {x : Result α}
    {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp])
  | .div, h => exact absurd h (by simp [Triple, WP.wp])

private theorem triple_of_ok_i32 {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, hp]

end loop_range_i32_helpers

set_option maxHeartbeats 2000000 in
theorem loop_range_spec_i32 {β : Type}
    (body : (core_models.ops.range.Range Std.I32 × β) →
      Result (ControlFlow (core_models.ops.range.Range Std.I32 × β) β))
    (init : β) (s e : Std.I32) (inv : Std.I32 → β → Result Prop)
    (h_le : s.val ≤ e.val)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : Std.I32), s.val ≤ i.val → i.val ≤ e.val →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body ({ start := i, «end» := e }, acc)
      ⦃ ⇓ r => match r with
        | .cont (iter', acc') =>
          ⌜ i.val < e.val ∧ iter'.«end» = e ∧ iter'.start.val = i.val + 1
            ∧ (inv iter'.start acc').holds ⌝
        | .done y => ⌜ (inv e y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body ({ start := s, «end» := e }, init)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  -- Generalize over the current iteration's `start` and induct on the number
  -- of remaining steps `n = (e.val - start.val).toNat`.
  suffices gen : ∀ (n : Nat) (acc : β) (start : Std.I32),
    (e.val - start.val).toNat = n →
    s.val ≤ start.val → start.val ≤ e.val →
    (inv start acc).holds →
    ⦃ ⌜ True ⌝ ⦄ loop body ({ start := start, «end» := e }, acc)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ by
    exact gen _ init s rfl (Int.le_refl _) h_le h_init
  intro n
  induction n with
  | zero =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_i32 hs
    have hpost := triple_noThrow_elim_i32 hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') =>
      simp at hpost; exact absurd hpost.1 (by omega)
    | .done y =>
      simp at hpost; exact triple_of_ok_i32 rfl hpost
  | succ n ih =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_i32 hs
    have hpost := triple_noThrow_elim_i32 hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp at hpost; exact triple_of_ok_i32 rfl hpost
    | .cont (iter', acc') =>
      simp at hpost
      obtain ⟨hlt, hend, hstart, hinv'⟩ := hpost
      have hiter : iter' = { start := iter'.start, «end» := e } := by
        cases iter'; cases hend; rfl
      rw [hiter]
      exact ih acc' iter'.start
        (by rw [hstart]; omega) (by rw [hstart]; omega) (by rw [hstart]; omega) hinv'

/-! ## Preservation lemma

The composability of `four_round_equiv` across iterations needs `lift s
= lift_perm s id impl_swap` (the impl-swap halves cancel under raw
reading) to hold at every iteration boundary. We state this as a
precondition and require it to be preserved by `keccakf1600_4rounds`.

### Structural reduction

The canonical condition `lift s = lift_perm s id impl_swap` is
equivalent to: *for each of the 12 `impl_swap` lanes,
`s.st.val[L]!.val[0]! = s.st.val[L]!.val[1]!`*. Call this property
**balanced** (`Balanced`).

This equivalence holds because `lift_lane_bv x y = lift_lane_bv y x ↔
x = y` (a bv_decide fact: `lift_lane_bv_swap_iff`).

The preservation lemma reduces to **balance preservation under the
12-call impl chain** (`keccakf1600_4rounds_preserves_balanced`),
which is the remaining bit-level fact. -/

/-- `lift_lane_bv` is symmetric in its arguments iff the arguments are
    equal. Discharged by `bv_decide` after unfolding the bit-deposit
    chain. -/
theorem lift_lane_bv_swap_iff (x y : BitVec 32) :
    lift_lane_bv x y = lift_lane_bv y x ↔ x = y := by
  unfold lift_lane_bv spread_to_even
  constructor
  · intro h; bv_decide
  · intro h; subst h; rfl

/-- A `UScalar` is determined by its underlying `BitVec`. -/
private theorem uscalar_eq_of_bv_eq {ty} {x y : Std.UScalar ty} (h : x.bv = y.bv) :
    x = y := by
  cases x; cases y; congr

/-- The "balanced" property: on each of the 12 `impl_swap` lanes, the
    two 32-bit halves of the impl's bit-interleaved storage are equal.
    Equivalent to the canonical condition (see `lift_eq_lift_perm_iff`). -/
def Balanced (s : state.KeccakState) : Prop :=
  ∀ i : Fin 25, impl_swap i = true →
    (s.st.val[i.val]!).val[0]! = (s.st.val[i.val]!).val[1]!

/-- The canonical condition `lift s = lift_perm s id impl_swap` is
    equivalent to `Balanced s`. -/
theorem lift_eq_lift_perm_iff (s : state.KeccakState) :
    lift s = lift_perm s id impl_swap ↔ Balanced s := by
  unfold lift lift_perm Balanced
  simp only [Function.id_def]
  rw [Subtype.mk_eq_mk, List.ofFn_inj]
  constructor
  · intro h i hsw
    have hi := congrFun h i
    unfold lift_lane_maybe_swap lift_lane at hi
    rw [hsw] at hi
    simp only [if_true, Std.UScalar.mk.injEq] at hi
    rw [lift_lane_bv_swap_iff] at hi
    exact uscalar_eq_of_bv_eq hi
  · intro h
    funext i
    unfold lift_lane_maybe_swap
    by_cases hsw : impl_swap i = true
    · simp only [hsw, if_true]
      unfold lift_lane
      simp only [Std.UScalar.mk.injEq]
      rw [lift_lane_bv_swap_iff]
      exact congrArg _ (h i hsw)
    · simp only [Bool.not_eq_true] at hsw
      rw [hsw]; simp

/-- **Remaining bit-level fact.** `keccakf1600_4rounds` preserves the
    `Balanced` property on the 12 `impl_swap` lanes.

    *Strategy for closing:* per-call mvcgen on each of the 12 inlined
    impl calls (round0_theta, pi_rho_chi_1, pi_rho_chi_2 for each of
    rounds 0/1/2/3), tracking which lanes maintain `val[0] = val[1]`
    after each call. The chi/iota/theta steps act lane-locally with
    XOR/AND/rotation; balance preservation per lane is a finite
    `bv_decide` check on the 32-bit halves of the involved lanes.

    Estimated effort: 200-500 lines. -/
theorem keccakf1600_4rounds_preserves_balanced
    (s : state.KeccakState) (h_i : s.i.val + 4 ≤ 24) (h_bal : Balanced s) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_4rounds 0#usize s
    ⦃ ⇓ r => ⌜ Balanced r ⌝ ⦄ := by
  sorry

/-- Preservation of the canonical condition through 4 impl rounds.
    Reduces to `keccakf1600_4rounds_preserves_balanced` via the
    `Balanced ↔ lift = lift_perm id impl_swap` bridge. -/
theorem keccakf1600_4rounds_preserves_lift_eq
    (s : state.KeccakState) (h_i : s.i.val + 4 ≤ 24)
    (h_lift : lift s = lift_perm s id impl_swap) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_4rounds 0#usize s
    ⦃ ⇓ r_impl => ⌜ lift r_impl = lift_perm r_impl id impl_swap ⌝ ⦄ := by
  have h_bal : Balanced s := (lift_eq_lift_perm_iff s).mp h_lift
  apply Triple.of_entails_right _ (keccakf1600_4rounds_preserves_balanced s h_i h_bal)
  rw [PostCond.entails_noThrow]
  intro r h_bal_r
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_bal_r ⊢
  exact (lift_eq_lift_perm_iff r).mpr h_bal_r

/-! ## Spec-chain helper

`fold_body` is the per-step function used inside the `Nat.fold 24`
spec chain in `keccakf1600_loop_post`. Wrapping it lets us reason
about the chain uniformly when peeling off iterations. -/

def spec_round_step_at (round_idx : Nat) (st : Std.Array Std.U64 25#usize) :
    Result (Std.Array Std.U64 25#usize) :=
  if h : round_idx < 24 then spec_round_step st (roundOfNat round_idx (by omega))
  else .fail .panic

/-- `spec_chain n s_lift` applies `n` spec rounds (indices 0..n-1) to
    the lifted initial state `s_lift`. -/
def spec_chain (s_lift : Std.Array Std.U64 25#usize) (n : Nat) :
    Result (Std.Array Std.U64 25#usize) :=
  Nat.fold n (fun i _ acc => acc >>= fun st => spec_round_step_at i st) (pure s_lift)

theorem spec_chain_zero (s_lift : Std.Array Std.U64 25#usize) :
    spec_chain s_lift 0 = .ok s_lift := by
  rfl

theorem spec_chain_succ (s_lift : Std.Array Std.U64 25#usize) (n : Nat) :
    spec_chain s_lift (n + 1) =
      spec_chain s_lift n >>= fun st => spec_round_step_at n st := by
  unfold spec_chain
  rw [Nat.fold_succ]

/-- The `Nat.fold 24` chain in `keccakf1600_loop_post` equals `spec_chain s 24`. -/
theorem keccakf1600_loop_post_eq_spec_chain
    (s : state.KeccakState) (s_final : state.KeccakState) :
    keccakf1600_loop_post s s_final =
      (do let lifted_final ← spec_chain (lift s) 24
          pure (lifted_final = lift_perm s_final id impl_swap)).holds := by
  unfold keccakf1600_loop_post spec_chain spec_round_step_at
  -- Both sides have shape `Nat.fold 24 body init`. Under `i < 24` (from
  -- Nat.fold's signature), the `if` in `spec_round_step_at` reduces to
  -- the spec_round_step branch.
  congr 1

/-! ## 4-round i-increment

Chains the four `round_k_i_inc` lemmas to show that
`keccakf1600_4rounds` advances `s.i` by 4. Needed for propagating the
loop invariant's `s_iter.i.val = 4 * k` field across iterations. -/

set_option maxHeartbeats 2000000 in
theorem keccakf1600_4rounds_i_inc (s : state.KeccakState) (h_i : s.i.val + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_4rounds 0#usize s
    ⦃ ⇓ r_impl => ⌜ r_impl.i.val = s.i.val + 4 ⌝ ⦄ := by
  rw [keccakf1600_4rounds_fold]
  apply Std.Do.Triple.bind _ _ (round0_i_inc s (by omega))
  intro r0
  apply triple_imp_intro
  intro h_i0
  apply Std.Do.Triple.bind _ _ (round1_i_inc r0 (by omega))
  intro r1
  apply triple_imp_intro
  intro h_i1
  apply Std.Do.Triple.bind _ _ (round2_i_inc r1 (by omega))
  intro r2
  apply triple_imp_intro
  intro h_i2
  apply Std.Do.Triple.of_entails_right _ (round3_i_inc r2 (by omega))
  rw [PostCond.entails_noThrow]
  intro r3 h_i3
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_i3 ⊢
  omega

/-! ## 4-round chunk equiv (composable form)

A composable version of `four_round_equiv`: given `lift s = lift_perm s
id impl_swap` (so input is canonical), the 4 spec rounds run from the
*canonical* spec state, and the output is also canonical. -/

set_option maxHeartbeats 2000000 in
theorem four_round_chunk_equiv
    (s : state.KeccakState) (h_i : s.i.val + 4 ≤ 24)
    (h_lift : lift s = lift_perm s id impl_swap) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_4rounds 0#usize s
    ⦃ ⇓ r => ⌜
      (do
        let st1 ← spec_round_step_at s.i.val (lift_perm s id impl_swap)
        let st2 ← spec_round_step_at (s.i.val + 1) st1
        let st3 ← spec_round_step_at (s.i.val + 2) st2
        let r_spec ← spec_round_step_at (s.i.val + 3) st3
        pure (r_spec = lift_perm r id impl_swap)).holds
      ∧ lift r = lift_perm r id impl_swap ⌝ ⦄ := by
  -- Combine `four_round_equiv` (algebraic chain) and
  -- `keccakf1600_4rounds_preserves_lift_eq` (preservation of canonicality).
  apply Triple.of_entails_right _
    (triple_conj_post (four_round_equiv s h_i)
      (keccakf1600_4rounds_preserves_lift_eq s h_i h_lift))
  rw [PostCond.entails_noThrow]
  intro r ⟨h4, h_lift_r⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h4 ⊢
  refine ⟨?_, h_lift_r⟩
  -- Unfold `four_round_post` and rewrite spec input from `lift s` to `lift_perm s id impl_swap`.
  unfold four_round_post at h4
  rw [← h_lift]
  -- Reduce `spec_round_step_at` to `spec_round_step` under the i < 24 bound.
  unfold spec_round_step_at
  have h0 : s.i.val < 24 := by omega
  have h1 : s.i.val + 1 < 24 := by omega
  have h2 : s.i.val + 2 < 24 := by omega
  have h3 : s.i.val + 3 < 24 := by omega
  simp [h0, h1, h2, h3]
  -- Bridge the `s.i` (Usize) in four_round_post with `roundOfNat s.i.val` here.
  have h_idx0 : roundOfNat s.i.val (by omega) = s.i := by
    apply Std.UScalar.eq_of_val_eq
    unfold roundOfNat
    rw [Std.UScalar.ofNatCore_val_eq]
  rw [h_idx0]
  exact h4

/-! ## Loop equivalence

Iterates `four_round_chunk_equiv` 6 times via `loop_range_spec_i32`. The
invariant tracks `s_iter.i.val = 4 * iter.start.toNat`, the canonical
condition `lift s_iter = lift_perm s_iter id impl_swap`, and the
4k-fold spec chain matching `lift_perm s_iter id impl_swap`. -/

/-- The loop invariant: at iteration boundary `k`,
  - `k ∈ [0, 6]`,
  - `s_iter.i.val = 4 * k`,
  - the impl state is canonical (lift = lift_perm id impl_swap),
  - and the spec chain through `4k` rounds matches `lift_perm s_iter id impl_swap`. -/
def loop_inv_prop (s_0 : state.KeccakState) (k : Std.I32) (s_iter : state.KeccakState) :
    Prop :=
  0 ≤ k.val ∧ k.val ≤ 6 ∧
  s_iter.i.val = 4 * k.val.toNat ∧
  lift s_iter = lift_perm s_iter id impl_swap ∧
  spec_chain (lift s_0) (4 * k.val.toNat) = .ok (lift_perm s_iter id impl_swap)

/-- 4-step chain version of `holds_chain_eq_ok`: from the `.holds` of a
    `do let st1 ← f0; let st2 ← f1 st1; let st3 ← f2 st2; let r ← f3 st3;
    pure (r = X)`, derive the underlying `Result` equation for the 3-bind
    left-associated chain (matching the shape produced by peeling
    `spec_chain_succ` four times). -/
private theorem holds_chain4_eq_ok {α : Type} {f0 : Result α} {f1 f2 f3 : α → Result α} {X : α}
    (h : (do let st1 ← f0
             let st2 ← f1 st1
             let st3 ← f2 st2
             let r ← f3 st3
             pure (r = X)).holds) :
    (do let st1 ← f0
        let st2 ← f1 st1
        let st3 ← f2 st2
        f3 st3) = .ok X := by
  cases hf0 : f0 with
  | ok v1 =>
    cases hf1 : f1 v1 with
    | ok v2 =>
      cases hf2 : f2 v2 with
      | ok v3 =>
        cases hf3 : f3 v3 with
        | ok v4 =>
          simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
                    Std.Do.SPred.down_pure]
        | fail e =>
          simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
                    Std.Do.SPred.down_pure]
        | div =>
          simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
                    Std.Do.SPred.down_pure]
      | fail e =>
        simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
                  Std.Do.SPred.down_pure]
      | div =>
        simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
                  Std.Do.SPred.down_pure]
    | fail e =>
      simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
                Std.Do.SPred.down_pure]
    | div =>
      simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
                Std.Do.SPred.down_pure]
  | fail e =>
    simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
              Std.Do.SPred.down_pure]
  | div =>
    simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
              Std.Do.SPred.down_pure]

theorem pure_prop_holds {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]
  intro _
  exact h

theorem of_pure_prop_holds {P : Prop} (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h
  exact h trivial

set_option maxHeartbeats 4000000 in
/-- Loop equivalence with the canonical precondition `lift s = lift_perm s
    id impl_swap` (initial half-swaps cancel). The post couples
    `keccakf1600_loop_post` with the canonical condition on the output. -/
theorem keccakf1600_loop_equiv
    (s : state.KeccakState) (h_i : s.i = 0#usize)
    (h_lift : lift s = lift_perm s id impl_swap) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_loop { start := 0#i32, «end» := 6#i32 } s
    ⦃ ⇓ s_final => ⌜ keccakf1600_loop_post s s_final
                    ∧ lift s_final = lift_perm s_final id impl_swap ⌝ ⦄ := by
  unfold keccak.keccakf1600_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_i32
      (fun (iter1, s1) => keccak.keccakf1600_loop.body iter1 s1)
      s 0#i32 6#i32
      (fun k s_iter => pure (loop_inv_prop s k s_iter))
      (by decide)
      (by -- h_init: invariant at iter start (k=0, s_iter = s).
          apply pure_prop_holds
          refine ⟨by decide, by decide, ?_, h_lift, ?_⟩
          · rw [h_i]; rfl
          · rw [show (4 * (0#i32 : Std.I32).val.toNat) = 0 from rfl, spec_chain_zero,
                  ← h_lift])
      ?_)
  · -- Post-entailment: derive keccakf1600_loop_post + lift = lift_perm from inv at k=6.
    rw [PostCond.entails_noThrow]
    intro s_final hinv
    dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hinv ⊢
    have ⟨_, _, _, h_lift_f, h_chain⟩ := of_pure_prop_holds hinv
    refine ⟨?_, h_lift_f⟩
    rw [keccakf1600_loop_post_eq_spec_chain]
    have h24 : (4 * (6#i32 : Std.I32).val.toNat) = 24 := by decide
    rw [h24] at h_chain
    -- Goal: (do let lifted ← spec_chain (lift s) 24; pure (lifted = lift_perm s_final id impl_swap)).holds
    -- h_chain: spec_chain (lift s) 24 = .ok (lift_perm s_final id impl_swap)
    rw [h_chain]
    apply pure_prop_holds
    rfl
  · -- h_step: per-iteration body Triple.
    intro acc k h_ge h_le hinv
    have hk_inv := of_pure_prop_holds hinv
    obtain ⟨h_ge_k, h_le_k, h_acc_i, h_lift_acc, h_chain_acc⟩ := hk_inv
    -- The body: `do let (o, iter1) ← iter.next; match o with | none => done acc | some _ => ...`
    unfold keccak.keccakf1600_loop.body
    -- Apply Triple.bind with the iterator spec. Q encodes the case-split: in the
    -- `none` branch we get `k.val = 6`; in the `some` branch we get the next iter.
    apply Std.Do.Triple.bind _ _
      (IteratorRange_next_spec_i32 k 6#i32 (by decide)
        (Q := PostCond.noThrow fun (oi : Option Std.I32 × _) => ⌜
          match oi.1 with
          | none => k.val ≥ (6#i32 : Std.I32).val ∧ oi.2 = { start := k, «end» := 6#i32 }
          | some i => i = k ∧ k.val < (6#i32 : Std.I32).val ∧
                      oi.2.«end» = 6#i32 ∧ oi.2.start.val = k.val + 1
        ⌝)
        (fun hlt s hs => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          refine ⟨rfl, hlt, rfl, hs⟩)
        (fun hge => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨hge, rfl⟩))
    intro ⟨o, iter1⟩
    apply triple_imp_intro
    -- Now case-split on `o` to handle the match in the body.
    rcases o with _ | i
    · -- none branch: body's match returns `ok (done acc)`. k.val = 6.
      rintro ⟨hge, hiter1_eq⟩
      have h6 : (6#i32 : Std.I32).val = 6 := by decide
      have hk_eq : k.val = 6 := by omega
      have hk_eq_i32 : k = 6#i32 := Std.IScalar.eq_of_val_eq (by rw [hk_eq, h6])
      -- body reduces to: ok (done acc)
      show ⦃⌜True⌝⦄ (ok (done acc) : Result _) ⦃_⦄
      apply triple_of_ok_i32 rfl
      -- Goal: (inv 6#i32 acc).holds (matched in the `done` arm)
      apply pure_prop_holds
      refine ⟨by decide, by decide, ?_, h_lift_acc, ?_⟩
      · rw [hk_eq_i32] at h_acc_i; exact h_acc_i
      · rw [hk_eq_i32] at h_chain_acc; exact h_chain_acc
    · -- some i branch: body's match runs keccakf1600_4rounds then returns cont (iter1, s1).
      rintro ⟨hi_eq, hk_lt, hiter1_end, hiter1_start⟩
      have h6 : (6#i32 : Std.I32).val = 6 := by decide
      -- Replace `i` everywhere with `k` (since the bind passes the original index `k`).
      cases hi_eq
      -- We need acc.i.val + 4 ≤ 24 from h_acc_i and hk_lt.
      have hk_lt' : k.val < 6 := by rw [← h6]; exact hk_lt
      have hk_toNat_lt : k.val.toNat < 6 := by omega
      have h_i_bnd : acc.i.val + 4 ≤ 24 := by rw [h_acc_i]; omega
      -- The body's `match` collapses to:
      --   do let s1 ← keccakf1600_4rounds 0#usize acc; ok (cont (iter1, s1))
      show ⦃⌜True⌝⦄
        (do let s1 ← keccak.keccakf1600_4rounds 0#usize acc; ok (cont (iter1, s1))) ⦃_⦄
      -- Apply Triple.bind with four_round_chunk_equiv combined with i_inc.
      apply Std.Do.Triple.bind _ _
        (triple_conj_post
          (four_round_chunk_equiv acc h_i_bnd h_lift_acc)
          (keccakf1600_4rounds_i_inc acc h_i_bnd))
      intro s1
      apply triple_imp_intro
      rintro ⟨⟨h_chain_post, h_lift_s1⟩, h_i_inc⟩
      -- Now body: ok (cont (iter1, s1))
      apply triple_of_ok_i32 rfl
      -- Goal:
      --   k.val < (6#i32).val ∧ iter1.end = 6#i32 ∧ iter1.start.val = k.val + 1
      --   ∧ (inv iter1.start s1).holds
      refine ⟨hk_lt, hiter1_end, hiter1_start, ?_⟩
      apply pure_prop_holds
      have h_start_val : iter1.start.val = k.val + 1 := hiter1_start
      have h_start_ge : 0 ≤ iter1.start.val := by rw [h_start_val]; omega
      have h_start_le : iter1.start.val ≤ 6 := by rw [h_start_val]; omega
      have h_start_toNat : iter1.start.val.toNat = k.val.toNat + 1 := by
        rw [h_start_val, Int.toNat_add (by omega) (by decide)]; rfl
      refine ⟨h_start_ge, h_start_le, ?_, h_lift_s1, ?_⟩
      · -- s1.i.val = 4 * iter1.start.val.toNat
        -- Combine h_i_inc (s1.i.val = acc.i.val + 4), h_acc_i, and h_start_toNat.
        rw [h_i_inc, h_acc_i, h_start_toNat]; ring
      · -- spec_chain (lift s) (4 * iter1.start.val.toNat) = .ok (lift_perm s1 id impl_swap)
        rw [h_start_toNat, show 4 * (k.val.toNat + 1) = 4 * k.val.toNat + 4 from by ring]
        -- Extract the 4-step chain equation from h_chain_post.
        have h_C : (do let st1 ← spec_round_step_at acc.i.val (lift_perm acc id impl_swap)
                       let st2 ← spec_round_step_at (acc.i.val + 1) st1
                       let st3 ← spec_round_step_at (acc.i.val + 2) st2
                       spec_round_step_at (acc.i.val + 3) st3)
                    = .ok (lift_perm s1 id impl_swap) := by
          exact holds_chain4_eq_ok h_chain_post
        -- Peel off 4 levels of spec_chain via spec_chain_succ.
        rw [show 4 * k.val.toNat + 4 = (4 * k.val.toNat + 3) + 1 from rfl, spec_chain_succ]
        rw [show 4 * k.val.toNat + 3 = (4 * k.val.toNat + 2) + 1 from rfl, spec_chain_succ]
        rw [show 4 * k.val.toNat + 2 = (4 * k.val.toNat + 1) + 1 from rfl, spec_chain_succ]
        rw [show 4 * k.val.toNat + 1 = (4 * k.val.toNat) + 1 from rfl, spec_chain_succ]
        rw [h_chain_acc]
        -- Goal:
        --   (.ok (lift_perm acc id impl_swap) >>= λ st => spec_round_step_at (4n) st)
        --     >>= ... >>= λ st => spec_round_step_at (4n+3) st
        --   = .ok (lift_perm s1 id impl_swap)
        simp only [Aeneas.Std.bind_tc_ok]
        rw [← h_acc_i]
        simp only [Nat.add_assoc, bind_assoc, show 1 + 1 = 2 from rfl,
                   show 1 + 1 + 1 = 3 from rfl]
        exact h_C

/-! ## Top-level keccakf1600 equivalence -/

/-- Top-level equivalence: `keccak.keccakf1600` (the full 24-round
    permutation) on the canonical bit-interleaved impl produces a state
    whose swap-aware lift equals the spec's 24-fold round application.

    Proof delegates to `keccakf1600_loop_equiv` and handles the trailing
    `i := 0` reset (the reset preserves `lift_perm` since it reads only
    `.st`). -/
theorem keccakf1600_equiv (s : state.KeccakState) (h_i : s.i = 0#usize)
    (h_lift : lift s = lift_perm s id impl_swap) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakf1600_post s r_impl ⌝ ⦄ := by
  -- Weaken the strong post (which adds `lift r = lift_perm r id impl_swap`)
  -- to just `keccakf1600_post`.
  have h_strong := keccakf1600_loop_equiv s h_i h_lift
  have h_weakened : ⦃ ⌜True⌝ ⦄
      keccak.keccakf1600_loop { start := 0#i32, «end» := 6#i32 } s
      ⦃ ⇓ s_final => ⌜keccakf1600_loop_post s s_final⌝ ⦄ := by
    apply Triple.of_entails_right _ h_strong
    rw [PostCond.entails_noThrow]
    intro s_final hpost
    dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hpost ⊢
    exact hpost.1
  unfold keccak.keccakf1600
  apply Std.Do.Triple.bind _ _ h_weakened
  intro s_final
  apply triple_imp_intro
  intro h_loop
  unfold keccakf1600_post
  unfold keccakf1600_loop_post at h_loop
  have h_lift_perm_eq : lift_perm { s_final with i := 0#usize } id impl_swap
                      = lift_perm s_final id impl_swap := by
    unfold lift_perm; rfl
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h_loop ⊢
  rw [h_lift_perm_eq]
  simpa using h_loop

end libcrux_iot_sha3.Equivalence
