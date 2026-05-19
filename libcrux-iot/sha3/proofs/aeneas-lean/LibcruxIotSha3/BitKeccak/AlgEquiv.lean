/-
  Campaign 2 (algebraic): the pure-Lean bit_keccak_spec equals the hacspec
  24-round application under the canonical lift.

  Outline:

  1. Per-round step functions `bit_round0..3 : KState → KState` (composing
     `theta + pi_rho_chi_1 + pi_rho_chi_2` per round).
  2. `bit_keccakf1600_4rounds_eq_chain` (`bit_keccakf1600_4rounds 0 s =
     bit_round3 (bit_round2 (bit_round1 (bit_round0 s)))`) — by `rfl`,
     since both sides unfold to the same 12-call let-chain.
  3. KState round-trip `KState.toAeneas (KState.fromAeneas s) = s` — bridges
     Campaign 1's pure-Lean output back into the Aeneas universe for the
     spec equation. Needed at the top-level composition.
  4. `BalancedAt k s` predicate — under `(impl_perm^[k], impl_swap)`,
     the state lifts identically with or without `impl_swap`. Required
     because the pure bit-side `bit_round{k}` reads halves literally,
     while the spec under `lift_perm _ p impl_swap` reads them swap-aware
     — they agree only on Balanced states (verified by counterexample).
  5. Per-round algebraic correspondence theorems
     `bit_round{k}_alg_eq` (k ∈ {0,1,2,3}) — the load-bearing algebra
     of Campaign 2. Each says
     `BalancedAt k s →`
     `spec_round_step (lift_perm s.toAeneas (impl_perm^[k]) impl_swap) s.i`
     `  = .ok (lift_perm (bit_round{k} s).toAeneas (impl_perm^[k+1]) impl_swap)`.
     *Currently `sorry`.* Paired with 4 preservation lemmas
     `bit_round{k}_preserves_balanced` (also `sorry`) that thread the
     invariant `BalancedAt k → BalancedAt (k+1)` across rounds; bundled
     by `bit_keccakf1600_4rounds_preserves_balanced` (using
     `impl_perm^[4] = id` to close the 4-round loop on `BalancedAt 0`).
  6. 4-round closure `bit_4rounds_alg_eq` — composes the 4 sorry'd
     per-round identities through `Result.bind`. Uses `impl_perm_pow4_eq_id`
     to collapse `impl_perm^[4]` to `id` at the group boundary.
  7. 24-round closure `bit_keccak_alg_eq` — 6-iteration induction over
     `Nat.iterate (bit_keccakf1600_4rounds 0) 6`. Threads both the
     `s.i.val = 4k` chain (for iota constants) and the `BalancedAt 0`
     invariant (via the chunk-preservation lemma).
  8. Top-level `keccakf1600_equiv_via_bit` — composes Campaign 1's
     `keccakf1600_eq` with Campaign 2's `bit_keccak_alg_eq` to retarget
     the impl-level `keccakf1600_post`. Discharges `BalancedAt 0` from
     the existing `h_lift : Equivalence.lift s = lift_perm s id impl_swap`
     hypothesis via `lift_perm_id` + `KState.toAeneas_fromAeneas`.

  Plan: `~/.claude/plans/fancy-gliding-swan.md`, Phase 3.
-/
import LibcruxIotSha3.BitKeccak.StructEquiv
import LibcruxIotSha3.Equivalence.Keccakf1600Loop

namespace libcrux_iot_sha3.BitKeccak

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 libcrux_iot_sha3.Equivalence

/-! ## Per-round step on `KState` (theta + pi_rho_chi_1 + pi_rho_chi_2). -/

@[inline] def bit_round0 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round0_theta s
  let s2 := bit_keccakf1600_round0_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round0_pi_rho_chi_2 s2

@[inline] def bit_round1 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round1_theta s
  let s2 := bit_keccakf1600_round1_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round1_pi_rho_chi_2 s2

@[inline] def bit_round2 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round2_theta s
  let s2 := bit_keccakf1600_round2_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round2_pi_rho_chi_2 s2

@[inline] def bit_round3 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round3_theta s
  let s2 := bit_keccakf1600_round3_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round3_pi_rho_chi_2 s2

/-- `bit_keccakf1600_4rounds 0 = bit_round3 ∘ bit_round2 ∘ bit_round1 ∘ bit_round0`. -/
theorem bit_keccakf1600_4rounds_eq_chain (s : KState) :
    bit_keccakf1600_4rounds 0#usize s
    = bit_round3 (bit_round2 (bit_round1 (bit_round0 s))) := by
  rfl

/-! ## KState ↔ state.KeccakState round-trip

    Required for the top-level composition: Campaign 1's `keccakf1600_eq`
    outputs `KState.fromAeneas r = bit_keccak_spec (KState.fromAeneas s)`,
    and Campaign 2's `bit_keccak_alg_eq` reads its input via `KState.toAeneas`.
    The bridge `KState.toAeneas (KState.fromAeneas s) = s` (for the cases
    where the input is the impl's initial state with well-formed lanes)
    closes the loop. -/

private theorem stateArray25_toAeneas_fromAeneas
    (a : Aeneas.Std.Array lane.Lane2U32 25#usize) :
    stateArray25ToAeneas (stateArray25FromAeneas a) = a := by
  obtain ⟨vals, hlen⟩ := a
  apply Subtype.ext
  show ((vals.map Lane.fromAeneas).toArray.toList.map Lane.toAeneas) = vals
  rw [List.toList_toArray, List.map_map]
  rw [show (Lane.toAeneas ∘ Lane.fromAeneas) = id from
        funext (fun l => Lane.toAeneas_fromAeneas l)]
  exact List.map_id vals

private theorem stateArray5_toAeneas_fromAeneas
    (a : Aeneas.Std.Array lane.Lane2U32 5#usize) :
    stateArray5ToAeneas (stateArray5FromAeneas a) = a := by
  obtain ⟨vals, hlen⟩ := a
  apply Subtype.ext
  show ((vals.map Lane.fromAeneas).toArray.toList.map Lane.toAeneas) = vals
  rw [List.toList_toArray, List.map_map]
  rw [show (Lane.toAeneas ∘ Lane.fromAeneas) = id from
        funext (fun l => Lane.toAeneas_fromAeneas l)]
  exact List.map_id vals

theorem KState.toAeneas_fromAeneas (s : state.KeccakState) :
    KState.toAeneas (KState.fromAeneas s) = s := by
  unfold KState.toAeneas KState.fromAeneas
  rcases s with ⟨st, c, d, i⟩
  refine state.KeccakState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, rfl⟩
  · exact stateArray25_toAeneas_fromAeneas st
  · exact stateArray5_toAeneas_fromAeneas c
  · exact stateArray5_toAeneas_fromAeneas d

/-- Reverse round-trip: `KState.fromAeneas (KState.toAeneas s) = s`.
    Used by the algebraic correspondence proofs to turn Campaign 1's
    bit-side equation `KState.fromAeneas r_impl = bit_round{k} (KState.fromAeneas s.toAeneas)`
    into `bit_round{k} s` (collapsing the inner round-trip). -/
theorem KState.fromAeneas_toAeneas (s : KState) :
    KState.fromAeneas (KState.toAeneas s) = s := by
  cases s
  simp [KState.fromAeneas, KState.toAeneas, stateArray25FromAeneas, stateArray25ToAeneas,
        stateArray5FromAeneas, stateArray5ToAeneas, Lane.fromAeneas_toAeneas, List.map_map,
        Function.comp_def]
  refine ⟨?_, ?_, ?_⟩
  all_goals (obtain ⟨_, _⟩ := ‹Vector _ _›; rfl)

/-! ## Per-round `s.i` increments on the bit side

    Each `bit_round{k}` bumps `s.i` by 1 (the `_zeta1` sub-piece in
    `pi_rho_chi_1` is the only one that increments). Used to thread the
    `s.i.val = 4 * group_idx + k` chain across the 4-round group. -/

/-- Converting `(⟨s.i.bv + 1⟩ : Std.Usize).val` to `s.i.val + 1` under
    a tame upper bound on `s.i.val`. The structural `_i` lemmas in
    `StructEquiv.lean` give the bit-side increment in `⟨_ + 1⟩` form;
    this bridges to `.val + 1` form. -/
private theorem usize_succ_val (s : Aeneas.Std.Usize) (hi : s.val < 24) :
    (⟨s.bv + (1 : BitVec System.Platform.numBits)⟩ : Aeneas.Std.Usize).val = s.val + 1 := by
  show (s.bv + (1 : BitVec System.Platform.numBits)).toNat = s.val + 1
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq; omega
  have hone : (1 : BitVec System.Platform.numBits).toNat = 1 := by
    have h1 : (1 : Nat) % 2 ^ System.Platform.numBits = 1 := by
      apply Nat.mod_eq_of_lt
      have : (2 : Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
        Nat.pow_le_pow_right (by decide) h32
      omega
    simp [BitVec.toNat_ofNat, h1]
  rw [BitVec.toNat_add, hone]
  apply Nat.mod_eq_of_lt
  have hsv : s.bv.toNat = s.val := rfl
  have : (2 : Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) h32
  rw [hsv]; omega

theorem bit_round0_i (s : KState) (hi : s.i.val < 24) :
    (bit_round0 s).i.val = s.i.val + 1 := by
  unfold bit_round0
  rw [bit_keccakf1600_round0_pi_rho_chi_2_i,
      bit_keccakf1600_round0_pi_rho_chi_1_i,
      bit_keccakf1600_round0_theta_i]
  exact usize_succ_val s.i hi

theorem bit_round1_i (s : KState) (hi : s.i.val < 24) :
    (bit_round1 s).i.val = s.i.val + 1 := by
  unfold bit_round1
  rw [bit_keccakf1600_round1_pi_rho_chi_2_i,
      bit_keccakf1600_round1_pi_rho_chi_1_i,
      bit_keccakf1600_round1_theta_i]
  exact usize_succ_val s.i hi

theorem bit_round2_i (s : KState) (hi : s.i.val < 24) :
    (bit_round2 s).i.val = s.i.val + 1 := by
  unfold bit_round2
  rw [bit_keccakf1600_round2_pi_rho_chi_2_i,
      bit_keccakf1600_round2_pi_rho_chi_1_i,
      bit_keccakf1600_round2_theta_i]
  exact usize_succ_val s.i hi

theorem bit_round3_i (s : KState) (hi : s.i.val < 24) :
    (bit_round3 s).i.val = s.i.val + 1 := by
  unfold bit_round3
  rw [bit_keccakf1600_round3_pi_rho_chi_2_i,
      bit_keccakf1600_round3_pi_rho_chi_1_i,
      bit_keccakf1600_round3_theta_i]
  exact usize_succ_val s.i hi

/-! ## "Balanced" precondition — a load-bearing fix to the architecture.

    The pure bit-side `bit_round{k}` definitions read `s.st[i].z0` /
    `s.st[i].z1` literally, matching the impl's storage convention. The
    spec under `lift_perm s p impl_swap` reads `s.st[(p i)].val[swap?1:0]`,
    which swaps halves on `impl_swap`-true lanes. The two readings agree
    exactly when the `impl_swap`-true lanes (under permutation `p`) have
    `z0 = z1` — captured below as `BalancedAt k s`.

    Computational counterexample: for `s` with `z0 ≠ z1` on the
    `impl_swap`-true lanes (2, 3, 5, 8, 12, 13, 14, 16, 17, 18, 20, 22),
    `spec_round_step (lift_perm s.toAeneas id impl_swap) s.i` differs
    from `lift_perm (bit_round0 s).toAeneas impl_perm impl_swap` at all
    25 lanes. Verified via `native_decide` on a concrete state — see
    the 2026-05-19 session report. -/

/-- `BalancedAt k s` says the canonical lift of `s` (with permutation
    `impl_perm^[k]` and swap `impl_swap`) matches the naive lift (no
    swap). Equivalently: for every `i` with `impl_swap (impl_perm^[k] i)
    = true`, the physical lane `s.st[(impl_perm^[k] i).val]` has
    `z0 = z1`. Required as a precondition on each per-round algebraic
    correspondence; threaded across 4-round groups by
    `bit_keccakf1600_4rounds_preserves_balanced`.

    **Key observation (to be formalized as `balancedAt_iff_balancedAt_zero`):**
    `BalancedAt k s` is *independent of k* — since `impl_perm^[k]` is a
    bijection on `Fin 25` (`impl_perm_pow4_eq_id` makes `impl_perm` an
    element of order dividing 4), the condition reduces to
    `∀ j ∈ Fin 25, impl_swap j = true → z0 = z1 at s.st.val[j.val]!`
    (the swap-true set `{2,3,5,8,12,13,14,16,17,18,20,22}` is fixed).
    Formalizing this simplification collapses the 4 per-round
    preservation lemmas to a single `bit_round{k} s preserves Balanced`
    claim, dischargeable lane-by-lane via `bv_decide`. -/
def BalancedAt (k : Nat) (s : KState) : Prop :=
  lift_perm s.toAeneas (impl_perm^[k]) impl_swap
  = lift_perm s.toAeneas (impl_perm^[k]) (fun _ => false)

/-! ## Per-round algebraic correspondence (the load-bearing 4 sorries).

    Statement shape (for k ∈ {0,1,2,3}):

    `BalancedAt k s →`
    `spec_round_step (lift_perm s.toAeneas (impl_perm^[k]) impl_swap) s.i`
    `  = .ok (lift_perm (bit_round{k} s).toAeneas (impl_perm^[k+1]) impl_swap)`

    Each says: under the Balanced precondition, the spec round-step on
    the canonically-lifted input matches the canonical lift of the
    bit-side per-round update. -/

/-! ### Generic extractors

    Each round's algebra proof uses the same pattern: combine the spec
    `round{k}_equiv_spec` Triple with the Campaign 1 chain Triple
    `round{k}_full_bit_eq`, weaken the post into the goal Prop, and
    extract via `triple_imp_prop` (a Triple whose post is a
    `r`-independent Prop yields the Prop). -/

/-- From a Triple whose post is a `r`-independent Prop, derive the Prop.
    Works because in the `Result α` tower with `noThrow` post, `.fail`/`.div`
    cases force the post to hold vacuously *with `False`*, so the only way
    the Triple holds is via the success case satisfying `P`. -/
private theorem triple_imp_prop {α : Type} {C : Aeneas.Std.Result α} {P : Prop}
    (h : ⦃⌜True⌝⦄ C ⦃⇓ _ => ⌜P⌝⦄) : P := by
  cases C
  all_goals simp_all [Std.Do.Triple, Std.Do.WP.wp, Std.Do.SPred.down_pure]

/-! ### Round-0 chain Triple (bit-side equivalence over the 3-step impl) -/

/-- Campaign 1 bundled at the 3-step round-0 chain: the impl call
    `do { theta; prc_1; prc_2 }` on `s` produces some `r` such that
    `KState.fromAeneas r = bit_round0 (KState.fromAeneas s)`.

    Chains `keccakf1600_round0_theta_eq` + `..._pi_rho_chi_1_eq` +
    `..._pi_rho_chi_2_eq` via `Std.Do.Triple.bind`, threading
    `s_after_theta.i.val < 24` (derived from the bit-side post via
    `bit_keccakf1600_round0_theta_i`) into the `pi_rho_chi_1`
    precondition. -/
private theorem round0_full_bit_eq (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃⌜True⌝⦄
    (do let s1 ← keccak.keccakf1600_round0_theta s
        keccakf1600_round0_pi_rho_chi_chain s1)
    ⦃⇓ r => ⌜KState.fromAeneas r = bit_round0 (KState.fromAeneas s)⌝⦄ := by
  apply Std.Do.Triple.bind _ _ (keccakf1600_round0_theta_eq s)
  intro s1
  apply triple_imp_intro
  intro h_theta
  -- Derive s1.i = s.i from the bit-side equation + bit_keccakf1600_round0_theta_i.
  have h_s1_i : s1.i = s.i := by
    have h : (KState.fromAeneas s1).i = (bit_keccakf1600_round0_theta (KState.fromAeneas s)).i :=
      congrArg (·.i) h_theta
    rw [bit_keccakf1600_round0_theta_i] at h
    exact h
  unfold keccakf1600_round0_pi_rho_chi_chain
  apply Std.Do.Triple.bind _ _
    (keccakf1600_round0_pi_rho_chi_1_eq 0#usize s1 (by rw [h_s1_i]; exact hi))
  intro s2
  apply triple_imp_intro
  intro h_prc1
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round0_pi_rho_chi_2_eq s2)
  rw [PostCond.entails_noThrow]
  intro r h_prc2
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_prc2 ⊢
  unfold bit_round0
  rw [h_prc2, h_prc1, h_theta]

/-- Round 0 algebraic equivalence. Composes the existing closed
    `round0_equiv_spec` (which couples the impl chain to the spec
    `do { θ; ρ; π; χ; ι }`) with Campaign 1's bit-side chain Triple
    `round0_full_bit_eq`; the `BalancedAt 0` precondition collapses
    `lift_perm s.toAeneas id impl_swap` to `lift s.toAeneas` (via
    `lift_perm_id`) so the spec call matches `round0_equiv_spec`'s
    input. The conjunction Triple's post is independent of `r` and
    *is* the goal, extracted via `triple_imp_prop`. -/
theorem bit_round0_alg_eq (s : KState) (hi : s.i.val < 24)
    (h_bal : BalancedAt 0 s) :
    spec_round_step (lift_perm s.toAeneas id impl_swap) s.i
    = .ok (lift_perm (bit_round0 s).toAeneas impl_perm impl_swap) := by
  -- Step 1: BalancedAt 0 s → lift_perm s.toAeneas id impl_swap = Equivalence.lift s.toAeneas.
  have h_lift_eq : lift_perm s.toAeneas id impl_swap = Equivalence.lift s.toAeneas := by
    have h : lift_perm s.toAeneas (impl_perm^[0]) impl_swap
           = lift_perm s.toAeneas (impl_perm^[0]) (fun _ => false) := h_bal
    rw [Function.iterate_zero] at h
    rw [h, lift_perm_id]
  rw [h_lift_eq]
  -- Step 2: Combine round0_equiv_spec + Campaign 1 chain Triple, extract via triple_imp_prop.
  apply triple_imp_prop
  apply Std.Do.Triple.of_entails_right _
    (triple_conj_post (round0_equiv_spec s.toAeneas hi) (round0_full_bit_eq s.toAeneas hi))
  rw [PostCond.entails_noThrow]
  intro r ⟨h_round0_post, h_from_eq⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_round0_post h_from_eq ⊢
  -- (a) Derive r = (bit_round0 s).toAeneas via the toAeneas / fromAeneas round-trips.
  have h_r_eq : r = (bit_round0 s).toAeneas := by
    rw [← KState.toAeneas_fromAeneas r, h_from_eq, KState.fromAeneas_toAeneas]
  -- (b) Extract spec_round_step = .ok (lift_perm r impl_perm impl_swap) from round0_post.
  unfold round0_post at h_round0_post
  have h_spec_eq : spec_round_step (Equivalence.lift s.toAeneas) s.toAeneas.i
                 = .ok (lift_perm r impl_perm impl_swap) := by
    unfold spec_round_step
    exact holds_chain_eq_ok h_round0_post
  show spec_round_step (Equivalence.lift s.toAeneas) s.i = .ok (lift_perm (bit_round0 s).toAeneas impl_perm impl_swap)
  rw [show s.i = s.toAeneas.i from rfl, h_spec_eq, h_r_eq]

/-- Round 1 algebraic equivalence. Algebra mirrors `theta_lift_spec_1 +
    prc_lift_spec_1` (currently sorry'd in `ThetaLiftRound1.lean` +
    `PrcLiftRound1.lean`), transcribed against `bit_round1`. Requires
    `BalancedAt 1 s` (i.e., balance under the round-1 storage layout). -/
theorem bit_round1_alg_eq (s : KState) (hi : s.i.val < 24)
    (h_bal : BalancedAt 1 s) :
    spec_round_step (lift_perm s.toAeneas impl_perm impl_swap) s.i
    = .ok (lift_perm (bit_round1 s).toAeneas (impl_perm ∘ impl_perm) impl_swap) := by
  sorry

/-- Round 2 algebraic equivalence. Algebra mirrors `theta_lift_spec_2 +
    prc_lift_spec_2` (sorry'd in `ThetaLiftRound2.lean` +
    `PrcLiftRound2.lean`), transcribed against `bit_round2`. -/
theorem bit_round2_alg_eq (s : KState) (hi : s.i.val < 24)
    (h_bal : BalancedAt 2 s) :
    spec_round_step (lift_perm s.toAeneas (impl_perm ∘ impl_perm) impl_swap) s.i
    = .ok (lift_perm (bit_round2 s).toAeneas (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap) := by
  sorry

/-- Round 3 algebraic equivalence. After round 3, `impl_perm^[4] = id`
    collapses the permutation. Algebra mirrors `theta_lift_spec_3 +
    prc_lift_spec_3` (sorry'd in `ThetaLiftRound3.lean` +
    `PrcLiftRound3.lean`), transcribed against `bit_round3`. -/
theorem bit_round3_alg_eq (s : KState) (hi : s.i.val < 24)
    (h_bal : BalancedAt 3 s) :
    spec_round_step (lift_perm s.toAeneas (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap) s.i
    = .ok (lift_perm (bit_round3 s).toAeneas id impl_swap) := by
  sorry

/-! ## Balance preservation across rounds and 4-round groups.

    Each `bit_round{k}` should map a state Balanced at layout `k` to one
    Balanced at layout `k+1`. After four rounds, `impl_perm^[4] = id`
    aligns the layout back to `k=0`, so a chunk-level preservation
    closes the inductive step in `bit_keccak_spec_alg_eq`. -/

/-- Round-0 preserves balance: `BalancedAt 0 s → BalancedAt 1 (bit_round0 s)`. -/
theorem bit_round0_preserves_balanced (s : KState) (hi : s.i.val < 24)
    (h_bal : BalancedAt 0 s) :
    BalancedAt 1 (bit_round0 s) := by
  sorry

/-- Round-1 preserves balance: `BalancedAt 1 s → BalancedAt 2 (bit_round1 s)`. -/
theorem bit_round1_preserves_balanced (s : KState) (hi : s.i.val < 24)
    (h_bal : BalancedAt 1 s) :
    BalancedAt 2 (bit_round1 s) := by
  sorry

/-- Round-2 preserves balance: `BalancedAt 2 s → BalancedAt 3 (bit_round2 s)`. -/
theorem bit_round2_preserves_balanced (s : KState) (hi : s.i.val < 24)
    (h_bal : BalancedAt 2 s) :
    BalancedAt 3 (bit_round2 s) := by
  sorry

/-- Round-3 preserves balance: `BalancedAt 3 s → BalancedAt 0 (bit_round3 s)`. -/
theorem bit_round3_preserves_balanced (s : KState) (hi : s.i.val < 24)
    (h_bal : BalancedAt 3 s) :
    BalancedAt 0 (bit_round3 s) := by
  sorry

/-- 4-round groups preserve `BalancedAt 0` — the inductive invariant used
    by `bit_keccak_spec_alg_eq` across the 6 chunks. -/
theorem bit_keccakf1600_4rounds_preserves_balanced (s : KState) (hi : s.i.val + 4 ≤ 24)
    (h_bal : BalancedAt 0 s) :
    BalancedAt 0 (bit_keccakf1600_4rounds 0#usize s) := by
  rw [bit_keccakf1600_4rounds_eq_chain]
  -- Apply the 4 per-round preservation lemmas, threading the i-bound.
  have h_i0 : (bit_round0 s).i.val = s.i.val + 1 := bit_round0_i s (by omega)
  have hb0 := bit_round0_preserves_balanced s (by omega) h_bal
  have h_i1 : (bit_round1 (bit_round0 s)).i.val = s.i.val + 2 := by
    rw [bit_round1_i _ (by rw [h_i0]; omega), h_i0]
  have hb1 := bit_round1_preserves_balanced (bit_round0 s) (by rw [h_i0]; omega) hb0
  have h_i2 : (bit_round2 (bit_round1 (bit_round0 s))).i.val = s.i.val + 3 := by
    rw [bit_round2_i _ (by rw [h_i1]; omega), h_i1]
  have hb2 := bit_round2_preserves_balanced (bit_round1 (bit_round0 s)) (by rw [h_i1]; omega) hb1
  exact bit_round3_preserves_balanced _ (by rw [h_i2]; omega) hb2

/-! ## 4-round closure

    Composes the 4 per-round algebraic identities via `Result.bind`
    associativity. Uses the i-increment chain to align iota constants. -/

set_option maxHeartbeats 4000000 in
theorem bit_4rounds_alg_eq (s : KState) (hi : s.i.val + 4 ≤ 24)
    (h_bal : BalancedAt 0 s) :
    (do
      let s1 ← spec_round_step (lift_perm s.toAeneas id impl_swap) s.i
      let s2 ← spec_round_step s1 (roundOfNat (s.i.val + 1) (by omega))
      let s3 ← spec_round_step s2 (roundOfNat (s.i.val + 2) (by omega))
      spec_round_step s3 (roundOfNat (s.i.val + 3) (by omega)))
    = .ok (lift_perm (bit_keccakf1600_4rounds 0#usize s).toAeneas id impl_swap) := by
  rw [bit_keccakf1600_4rounds_eq_chain]
  -- Round 0
  have h0 := bit_round0_alg_eq s (by omega) h_bal
  rw [h0]; simp only [Aeneas.Std.bind_tc_ok]
  -- Round 1: align iota constant via i-chain
  have h_i0_val : (bit_round0 s).i.val = s.i.val + 1 := bit_round0_i s (by omega)
  have hb1 : BalancedAt 1 (bit_round0 s) :=
    bit_round0_preserves_balanced s (by omega) h_bal
  have h_i1 : (bit_round0 s).i = roundOfNat (s.i.val + 1) (by omega) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_i0_val]
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  have h1 := bit_round1_alg_eq (bit_round0 s) (by rw [h_i0_val]; omega) hb1
  rw [← h_i1, h1]; simp only [Aeneas.Std.bind_tc_ok]
  -- Round 2
  have h_i1_val : (bit_round1 (bit_round0 s)).i.val = s.i.val + 2 := by
    rw [bit_round1_i _ (by rw [h_i0_val]; omega), h_i0_val]
  have hb2 : BalancedAt 2 (bit_round1 (bit_round0 s)) :=
    bit_round1_preserves_balanced (bit_round0 s) (by rw [h_i0_val]; omega) hb1
  have h_i2 : (bit_round1 (bit_round0 s)).i = roundOfNat (s.i.val + 2) (by omega) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_i1_val]
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  have h2 := bit_round2_alg_eq (bit_round1 (bit_round0 s)) (by rw [h_i1_val]; omega) hb2
  rw [← h_i2, h2]; simp only [Aeneas.Std.bind_tc_ok]
  -- Round 3
  have h_i2_val : (bit_round2 (bit_round1 (bit_round0 s))).i.val = s.i.val + 3 := by
    rw [bit_round2_i _ (by rw [h_i1_val]; omega), h_i1_val]
  have hb3 : BalancedAt 3 (bit_round2 (bit_round1 (bit_round0 s))) :=
    bit_round2_preserves_balanced _ (by rw [h_i1_val]; omega) hb2
  have h_i3 : (bit_round2 (bit_round1 (bit_round0 s))).i = roundOfNat (s.i.val + 3) (by omega) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_i2_val]
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  have h3 := bit_round3_alg_eq (bit_round2 (bit_round1 (bit_round0 s)))
    (by rw [h_i2_val]; omega) hb3
  rw [← h_i3, h3]

set_option maxHeartbeats 2000000 in
/-- Index-parameterized variant of `bit_4rounds_alg_eq`. Takes a `Nat`
    index `n` and the equation `n = s.i.val`; substitution then makes
    this identical in shape to `bit_4rounds_alg_eq` modulo the first
    `s.i` ↔ `roundOfNat n _` identity (closed by `Std.UScalar.eq_of_val_eq`). -/
theorem bit_4rounds_alg_eq_at (s : KState) (n : Nat) (h_n : n + 4 ≤ 24)
    (h_i : n = s.i.val) (h_bal : BalancedAt 0 s) :
    (do
      let s1 ← spec_round_step (lift_perm s.toAeneas id impl_swap)
                  (roundOfNat n (by omega))
      let s2 ← spec_round_step s1 (roundOfNat (n + 1) (by omega))
      let s3 ← spec_round_step s2 (roundOfNat (n + 2) (by omega))
      spec_round_step s3 (roundOfNat (n + 3) (by omega)))
    = .ok (lift_perm (bit_keccakf1600_4rounds 0#usize s).toAeneas id impl_swap) := by
  subst h_i
  -- Indices are now `s.i.val + k`, matching bit_4rounds_alg_eq.
  have h_chain := bit_4rounds_alg_eq s h_n h_bal
  -- The only difference: goal has `roundOfNat s.i.val _` at position 0,
  -- h_chain has `s.i`. Rewrite the goal direction (not h_chain) to avoid
  -- dependent-rewrite friction on the remaining roundOfNat indices.
  have h_si_eq : roundOfNat s.i.val (by omega) = s.i := by
    apply Std.UScalar.eq_of_val_eq
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  rw [h_si_eq]
  exact h_chain

/-! ## i-increment for `bit_keccakf1600_4rounds` -/

theorem bit_keccakf1600_4rounds_i (s : KState) (hi : s.i.val + 4 ≤ 24) :
    (bit_keccakf1600_4rounds 0#usize s).i.val = s.i.val + 4 := by
  rw [bit_keccakf1600_4rounds_eq_chain]
  have h0 : (bit_round0 s).i.val = s.i.val + 1 := bit_round0_i s (by omega)
  have h1 : (bit_round1 (bit_round0 s)).i.val = s.i.val + 2 := by
    rw [bit_round1_i _ (by rw [h0]; omega), h0]
  have h2 : (bit_round2 (bit_round1 (bit_round0 s))).i.val = s.i.val + 3 := by
    rw [bit_round2_i _ (by rw [h1]; omega), h1]
  rw [bit_round3_i _ (by rw [h2]; omega), h2]

/-! ## 24-round closure (the Campaign 2 target)

    Induct over 6 iterations of `bit_keccakf1600_4rounds 0`, threading
    the `s.i.val = 4k` chain to align spec_round_step indices. -/

private theorem nat_iterate_i (s : KState) (h_i : s.i.val = 0) (k : Nat) (hk : k ≤ 6) :
    (Nat.iterate (bit_keccakf1600_4rounds 0#usize) k s).i.val = 4 * k := by
  induction k with
  | zero => simpa using h_i
  | succ n IH =>
    have hn : n ≤ 6 := by omega
    have hIH := IH hn
    rw [Function.iterate_succ_apply']
    rw [bit_keccakf1600_4rounds_i _ (by rw [hIH]; omega)]
    rw [hIH]; ring

/-- `BalancedAt 0` propagates across `k` iterations of the 4-round group,
    threading the i-counter so we can discharge each chunk's bound. -/
private theorem nat_iterate_balanced (s : KState) (h_i_val : s.i.val = 0)
    (h_bal : BalancedAt 0 s) (k : Nat) (hk : k ≤ 6) :
    BalancedAt 0 (Nat.iterate (bit_keccakf1600_4rounds 0#usize) k s) := by
  induction k with
  | zero => simpa
  | succ n IH =>
    have hn : n ≤ 6 := by omega
    have hIH := IH hn
    have h_iter_i : (Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s).i.val = 4 * n :=
      nat_iterate_i s h_i_val n hn
    rw [Function.iterate_succ_apply']
    exact bit_keccakf1600_4rounds_preserves_balanced _ (by rw [h_iter_i]; omega) hIH

set_option maxHeartbeats 4000000 in
/-- The 24-round Campaign 2 closure on the pure-Lean side. Requires
    `BalancedAt 0 s` (the initial state is balanced under impl_swap);
    the inductive step uses `bit_keccakf1600_4rounds_preserves_balanced`
    to thread the invariant across 6 chunks. -/
theorem bit_keccak_spec_alg_eq (s : KState) (h_i : s.i = 0#usize)
    (h_bal : BalancedAt 0 s) :
    spec_chain (lift_perm s.toAeneas id impl_swap) 24
    = .ok (lift_perm (Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 s).toAeneas id impl_swap) := by
  have h_i_val : s.i.val = 0 := by rw [h_i]; rfl
  -- Induct over k ∈ {0..6}, tracking the i counter.
  suffices h : ∀ k ≤ 6,
      spec_chain (lift_perm s.toAeneas id impl_swap) (4 * k)
      = .ok (lift_perm (Nat.iterate (bit_keccakf1600_4rounds 0#usize) k s).toAeneas id impl_swap) by
    have h6 := h 6 (by omega)
    rw [show (24 : Nat) = 4 * 6 from rfl]; exact h6
  intro k hk
  induction k with
  | zero =>
    simp only [Nat.mul_zero, spec_chain_zero, Function.iterate_zero, id_eq]
  | succ n IH =>
    have hn : n ≤ 6 := by omega
    have IH' := IH hn
    -- 4 * (n+1) = 4 * n + 4
    rw [show 4 * (n + 1) = 4 * n + 4 from by ring]
    -- spec_chain (4*n + 4) = spec_chain (4*n) >>= (4-step group)
    rw [show 4 * n + 4 = (4 * n + 3) + 1 from rfl, spec_chain_succ]
    rw [show 4 * n + 3 = (4 * n + 2) + 1 from rfl, spec_chain_succ]
    rw [show 4 * n + 2 = (4 * n + 1) + 1 from rfl, spec_chain_succ]
    rw [show 4 * n + 1 = 4 * n + 1 from rfl, spec_chain_succ]
    rw [IH']
    simp only [Aeneas.Std.bind_tc_ok]
    -- Goal: 4-step chain starting from (lift_perm (iter^[n] s) id impl_swap) at index 4*n
    --       = .ok (lift_perm (iter^[n+1] s) id impl_swap)
    rw [Function.iterate_succ_apply']
    -- Set acc := iter^[n] s and use bit_4rounds_alg_eq_at.
    have h_acc_i_val : (Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s).i.val = 4 * n :=
      nat_iterate_i s h_i_val n hn
    have h_acc_bal : BalancedAt 0 (Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s) :=
      nat_iterate_balanced s h_i_val h_bal n hn
    have h_acc_i_bnd : (Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s).i.val + 4 ≤ 24 := by
      rw [h_acc_i_val]; omega
    set acc := Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s
    have h_chain := bit_4rounds_alg_eq_at acc (4 * n) (by omega) h_acc_i_val.symm h_acc_bal
    -- Goal has spec_round_step_at; reduce to spec_round_step + roundOfNat
    -- and align do-block desugaring with bind_assoc.
    unfold spec_round_step_at
    simp only [show (4 * n + 1 + 1 : Nat) = 4 * n + 2 from rfl,
               show (4 * n + 1 + 1 + 1 : Nat) = 4 * n + 3 from rfl,
               dif_pos (show 4 * n < 24 by omega),
               dif_pos (show 4 * n + 1 < 24 by omega),
               dif_pos (show 4 * n + 2 < 24 by omega),
               dif_pos (show 4 * n + 3 < 24 by omega),
               bind_assoc]
    exact h_chain

/-! ## Top-level composition with Campaign 1

    Combines `keccakf1600_eq` (Campaign 1: impl ≡ bit_keccak_spec on
    pure-Lean side) with `bit_keccak_spec_alg_eq` (Campaign 2: 24-fold
    spec on lift_perm equals lift_perm of bit_keccak_spec) to derive
    the impl-level top-level `keccakf1600_equiv` post (with `Balanced`
    precondition via `h_lift`). -/

theorem keccakf1600_equiv_via_bit (s : state.KeccakState)
    (h_i : s.i = 0#usize)
    (h_lift : Equivalence.lift s = lift_perm s id impl_swap) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakf1600_post s r_impl ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_eq s h_i)
  rw [PostCond.entails_noThrow]
  intro r h_fromAeneas
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_fromAeneas ⊢
  unfold keccakf1600_post
  -- Bridge: `keccakf1600_post`'s Nat.fold IS `spec_chain` (it's just inlined).
  -- (`keccakf1600_loop_post_eq_spec_chain` formalizes this for `_loop_post`;
  -- the same proof works here.)
  have h_post_eq :
      (do let lifted_final ← Nat.fold 24
            (fun i h acc => acc >>= fun st => spec_round_step st (roundOfNat i (by omega)))
            (pure (Equivalence.lift s))
          pure (lifted_final = lift_perm r id impl_swap)).holds
      = (do let lifted_final ← spec_chain (Equivalence.lift s) 24
            pure (lifted_final = lift_perm r id impl_swap)).holds := by
    unfold spec_chain spec_round_step_at
    congr 1
  rw [h_post_eq]
  -- Bridge lift s → lift_perm s id impl_swap (h_lift) → lift_perm (toAeneas (fromAeneas s)) id impl_swap.
  rw [h_lift, show lift_perm s id impl_swap
                = lift_perm (KState.toAeneas (KState.fromAeneas s)) id impl_swap from by
        rw [KState.toAeneas_fromAeneas]]
  -- Apply Campaign 2.
  have h_i' : (KState.fromAeneas s).i = 0#usize := by
    show (KState.fromAeneas s).i = 0#usize
    unfold KState.fromAeneas
    exact h_i
  -- `h_lift` is exactly `BalancedAt 0 (KState.fromAeneas s)` up to direction +
  -- the `toAeneas ∘ fromAeneas = id` round-trip, and `lift = lift_perm _ id _`
  -- with `fun _ => false` (by `lift_perm_id`).
  have h_bal : BalancedAt 0 (KState.fromAeneas s) := by
    show lift_perm (KState.fromAeneas s).toAeneas (impl_perm^[0]) impl_swap
       = lift_perm (KState.fromAeneas s).toAeneas (impl_perm^[0]) (fun _ => false)
    rw [Function.iterate_zero, KState.toAeneas_fromAeneas, ← h_lift, lift_perm_id]
  rw [bit_keccak_spec_alg_eq (KState.fromAeneas s) h_i' h_bal]
  unfold bit_keccak_spec at h_fromAeneas
  -- Bridge: r.st = (toAeneas (iter^[6] (fromAeneas s))).st (since lift_perm
  -- reads only .st, and `with i := 0` preserves `.st` on both sides).
  have h_lift_perm_st_only :
      ∀ (a b : state.KeccakState), a.st = b.st →
        lift_perm a id impl_swap = lift_perm b id impl_swap := by
    intro a b hab
    unfold lift_perm
    apply Subtype.ext
    show List.ofFn (fun i : Fin 25 => lift_lane_maybe_swap (a.st.val[(id i).val]!) (impl_swap (id i)))
       = List.ofFn (fun i : Fin 25 => lift_lane_maybe_swap (b.st.val[(id i).val]!) (impl_swap (id i)))
    rw [hab]
  have h_r_eq_iter_st :
      r.st = (KState.toAeneas
                (Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 (KState.fromAeneas s))).st := by
    -- r.st = toAeneas (fromAeneas r).st (round-trip on .st)
    have hrt : r.st = stateArray25ToAeneas (KState.fromAeneas r).st :=
      (stateArray25_toAeneas_fromAeneas r.st).symm
    rw [hrt]
    -- (fromAeneas r).st = (iter^[6] _).st (from h_fromAeneas; `with i := 0` keeps `.st`)
    have h_from_st : (KState.fromAeneas r).st
                   = (Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 (KState.fromAeneas s)).st := by
      rw [h_fromAeneas]
    rw [h_from_st]
    rfl
  apply pure_prop_holds
  exact h_lift_perm_st_only _ _ h_r_eq_iter_st.symm

end libcrux_iot_sha3.BitKeccak
