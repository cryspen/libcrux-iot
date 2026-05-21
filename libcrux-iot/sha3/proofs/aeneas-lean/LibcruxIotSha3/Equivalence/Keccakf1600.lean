/-
  Top-level Keccak-f[1600] equivalence (24-round permutation).

  Architecture:
  - `four_round_equiv` composes `round{0,1,2,3}_equiv_spec` via the
    extracted `keccakf1600_4rounds` chain. After 4 rounds,
    `impl_perm_pow4_eq_id` collapses the lane permutation to `id`,
    leaving only the half-swap `impl_swap`.
  - `keccakf1600_equiv` runs `four_round_equiv` 6 times via the outer
    loop in `keccak.keccakf1600`. The state at the end of round 24
    satisfies `lift_perm r id impl_swap = spec_keccakf1600 (lift s)`.

  Status: `four_round_equiv` is closed (assuming the round-1/2/3
  `round_k_equiv_spec` + `round_k_i_inc` lemmas, which are themselves
  blocked on `theta_lift_spec_k` / `prc_lift_spec_k`).
  `keccakf1600_equiv` remains `sorry` pending the outer-loop induction
  in `keccak.keccakf1600`.
-/
import LibcruxIotSha3.Equivalence.RoundEquiv


open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3


namespace libcrux_iot_sha3.Equivalence

/-! ## Helper: extract Triple from a `(do C; pure (r = X)).holds` -/

/-- From a `.holds` claim of the form `(do let r ← C; pure (r = X)).holds`
    derive the corresponding Triple `⦃True⦄ C ⦃⇓ r => ⌜r = X⌝⦄`. Used in
    `four_round_equiv` to extract per-round chain Triples from each
    `round_k_post` hypothesis. -/
theorem holds_pure_eq_imp_triple {α : Type} {C : Aeneas.Std.Result α} {X : α}
    (h : (do let r ← C; pure (r = X)).holds) :
    ⦃⌜True⌝⦄ C ⦃⇓ r => ⌜r = X⌝⦄ := by
  cases C
  all_goals simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
                      Std.Do.SPred.down_pure]

/-- From a `.holds` claim of the form `(do let r ← C; pure (r = X)).holds`
    derive the underlying Result equation `C = .ok X`. -/
theorem holds_chain_eq_ok {α : Type} {C : Aeneas.Std.Result α} {X : α}
    (h : (do let r ← C; pure (r = X)).holds) : C = .ok X := by
  cases C
  all_goals simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, Functor.map,
                      Std.Do.SPred.down_pure]

/-! ## Spec-side one-round step (theta + rho + pi + chi + iota)

Bundles the 5-step spec round into a single function so we can talk
about iterating it. -/

def spec_round_step (state : Std.Array Std.U64 25#usize) (round : Std.Usize) :
    Result (Std.Array Std.U64 25#usize) := do
  let s_theta ← keccak_f.theta_unrolled state
  let s_rho ← keccak_f.rho_unrolled s_theta
  let s_pi ← keccak_f.pi_unrolled s_rho
  let s_chi ← keccak_f.chi_unrolled s_pi
  keccak_f.iota s_chi round


/-- Convert a `Nat` ≤ 24 to `Std.Usize`. Used in `four_round_post` /
    `keccakf1600_post` to bridge `Nat.fold` indices and `+ k` round
    offsets into the `Std.Usize` argument that `spec_round_step`
    requires. Since `24 < 2^32 ≤ 2^System.Platform.numBits`, the
    bound proof is trivial. -/
private def roundOfNat (k : Nat) (h : k ≤ 24) : Std.Usize :=
  Std.UScalar.ofNatCore k (by
    have h24 : (24 : Nat) < 2 ^ Std.UScalarTy.Usize.numBits := by
      simp only [Std.UScalarTy.Usize_numBits_eq]
      rcases System.Platform.numBits_eq with hpn | hpn <;> rw [hpn] <;> decide
    omega)

theorem keccakf1600_equiv (s : state.KeccakState) (h_i : s.i = 0#usize) :
    keccak_f.keccak_f (lift s) = lift <$> keccak.keccakf1600 s := sorry



/-! ## 4-round composition

Each round transforms a `KeccakState` with an associated layout
`(impl_perm^[k], impl_swap)`. After 4 rounds, `impl_perm^[4] = id`
(by `impl_perm_pow4_eq_id`), so the lane permutation cancels and the
output lift uses just `impl_swap`. -/

@[irreducible]
def four_round_post (s : state.KeccakState) (h : s.i.val + 4 ≤ 24)
    (r_impl : state.KeccakState) : Prop :=
  (do
    let s1 ← spec_round_step (lift s) s.i
    let s2 ← spec_round_step s1 (roundOfNat (s.i.val + 1) (by omega))
    let s3 ← spec_round_step s2 (roundOfNat (s.i.val + 2) (by omega))
    let r_spec ← spec_round_step s3 (roundOfNat (s.i.val + 3) (by omega))
    pure (r_spec = lift_perm r_impl id impl_swap)).holds

/-! ## Fold lemma: bundle inline 12-call chain into 4 nested (theta_k, chain_k) pairs

The extracted `keccak.keccakf1600_4rounds 0#usize s` is a 12-call inline
do-block. Each per-round `(pi_rho_chi_1 0#usize; pi_rho_chi_2)` pair is
packaged in `RoundEquiv.lean` as `keccakf1600_round{k}_pi_rho_chi_chain`
(a named `def`). This lemma folds the inline pairs into chain-wrapper
calls and groups each round as a nested 2-call do-block so `Triple.bind`
can split exactly at round boundaries, dispatching each pair via
`round_k_equiv_spec`. -/
set_option maxHeartbeats 8000000 in
theorem keccakf1600_4rounds_fold (s : state.KeccakState) :
    keccak.keccakf1600_4rounds 0#usize s = (do
      let r0 ← (do let s1 ← keccak.keccakf1600_round0_theta s
                   keccakf1600_round0_pi_rho_chi_chain s1)
      let r1 ← (do let s1 ← keccak.keccakf1600_round1_theta r0
                   keccakf1600_round1_pi_rho_chi_chain s1)
      let r2 ← (do let s1 ← keccak.keccakf1600_round2_theta r1
                   keccakf1600_round2_pi_rho_chi_chain s1)
      do let s1 ← keccak.keccakf1600_round3_theta r2
         keccakf1600_round3_pi_rho_chi_chain s1) := by
  unfold keccak.keccakf1600_4rounds
    keccakf1600_round0_pi_rho_chi_chain
    keccakf1600_round1_pi_rho_chi_chain
    keccakf1600_round2_pi_rho_chi_chain
    keccakf1600_round3_pi_rho_chi_chain
  simp [bind_assoc]

-- 4-round equivalence: `keccakf1600_4rounds` on impl produces a state
-- `r_impl` such that the spec applied 4 times equals
-- `lift_perm r_impl id impl_swap`.
--
-- Proof composes `round{0,1,2,3}_equiv_spec` through the inlined
-- impl chain (theta + prc_chi_1 + prc_chi_2 per round). After
-- round 3 the cumulative permutation is `impl_perm^[4] = id`.
set_option maxHeartbeats 4000000 in
theorem four_round_equiv (s : state.KeccakState) (hi : s.i.val + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_4rounds 0#usize s
    ⦃ ⇓ r_impl => ⌜ four_round_post s hi r_impl ⌝ ⦄ := by
  -- Strategy: rewrite the inline 12-call chain to the nested 4-round
  -- form (each round = inner do-block of `theta_k; chain_k`). Then
  -- chain the four `round_k_equiv_spec`s via `Triple.bind`. Each round's
  -- chain spec needs `s.i.val < 24`, so we thread i-increment side-info
  -- via `round_k_i_inc` sidecars combined with `triple_conj_post`.
  -- After 4 rounds, the cumulative permutation is `impl_perm^[4] = id`,
  -- discharged via `impl_perm_pow4_eq_id`.
  rw [keccakf1600_4rounds_fold]
  -- Round 0: precondition `⌜True⌝`, no precondition extraction needed.
  apply Std.Do.Triple.bind _ _
    (triple_conj_post (round0_equiv_spec s (by omega)) (round0_i_inc s (by omega)))
  intro r0
  -- After Round 0's Triple.bind, the precondition for the continuation
  -- is the conjunction post: ⌜round0_post s r0 ∧ r0.i.val = s.i.val + 1⌝.
  -- Lift it into proof-context hypotheses via `triple_imp_intro` so
  -- subsequent round preconditions can use omega over the i-chain.
  apply triple_imp_intro
  rintro ⟨h_round0, h_i0⟩
  apply Std.Do.Triple.bind _ _
    (triple_conj_post (round1_equiv_spec r0 (by omega)) (round1_i_inc r0 (by omega)))
  intro r1
  apply triple_imp_intro
  rintro ⟨h_round1, h_i1⟩
  apply Std.Do.Triple.bind _ _
    (triple_conj_post (round2_equiv_spec r1 (by omega)) (round2_i_inc r1 (by omega)))
  intro r2
  apply triple_imp_intro
  rintro ⟨h_round2, h_i2⟩
  -- Round 3 is the tail of the do-block (no outer `let r3 ← …`), so we
  -- finish by weakening the post of the combined Triple to derive
  -- `four_round_post s hi r3`. The analytical step uses the four
  -- per-round posts (h_round0/h_round1/h_round2 in scope, h_round3
  -- from the round-3 Triple's post) plus `impl_perm_pow4_eq_id` to
  -- collapse `impl_perm^[4]` to `id`.
  apply Std.Do.Triple.of_entails_right _
    (triple_conj_post (round3_equiv_spec r2 (by omega)) (round3_i_inc r2 (by omega)))
  -- Goal: ⌜round3_post r2 r ∧ r.i.val = r2.i.val + 1⌝ ⊢ ⌜four_round_post s hi r⌝
  rw [PostCond.entails_noThrow]
  intro r3 hpost
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hpost ⊢
  obtain ⟨h_round3, h_i3⟩ := hpost
  -- Unfold the 4 per-round posts to expose the spec chains.
  unfold round0_post at h_round0
  unfold round1_post at h_round1
  unfold round2_post at h_round2
  unfold round3_post at h_round3
  -- Extract Result equations from each round.
  have h_c0 : (do
      let s_theta ← keccak_f.theta_unrolled (lift s)
      let s_rho ← keccak_f.rho_unrolled s_theta
      let s_pi ← keccak_f.pi_unrolled s_rho
      let s_chi ← keccak_f.chi_unrolled s_pi
      keccak_f.iota s_chi s.i) = .ok (lift_perm r0 impl_perm impl_swap) :=
    holds_chain_eq_ok h_round0
  -- Unfold the goal's four_round_post + spec_round_step.
  unfold four_round_post spec_round_step
  -- Now try to rewrite using h_c0.
  rw [h_c0]
  simp only [Aeneas.Std.bind_tc_ok]
  -- Round-index equalities so subsequent rewrites can dispatch h_c{1,2,3}.
  have h_idx1 : roundOfNat (s.i.val + 1) (by omega) = r0.i :=
    Std.UScalar.eq_of_val_eq (by
      unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]; omega)
  have h_idx2 : roundOfNat (s.i.val + 2) (by omega) = r1.i :=
    Std.UScalar.eq_of_val_eq (by
      unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]; omega)
  have h_idx3 : roundOfNat (s.i.val + 3) (by omega) = r2.i :=
    Std.UScalar.eq_of_val_eq (by
      unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]; omega)
  rw [h_idx1, h_idx2, h_idx3]
  -- Extract round-1 chain equation.
  have h_c1 : (do
      let s_theta ← keccak_f.theta_unrolled (lift_perm r0 impl_perm impl_swap)
      let s_rho ← keccak_f.rho_unrolled s_theta
      let s_pi ← keccak_f.pi_unrolled s_rho
      let s_chi ← keccak_f.chi_unrolled s_pi
      keccak_f.iota s_chi r0.i) =
        .ok (lift_perm r1 (impl_perm ∘ impl_perm) impl_swap) :=
    holds_chain_eq_ok h_round1
  rw [h_c1]
  simp only [Aeneas.Std.bind_tc_ok]
  -- Round 2.
  have h_c2 : (do
      let s_theta ← keccak_f.theta_unrolled (lift_perm r1 (impl_perm ∘ impl_perm) impl_swap)
      let s_rho ← keccak_f.rho_unrolled s_theta
      let s_pi ← keccak_f.pi_unrolled s_rho
      let s_chi ← keccak_f.chi_unrolled s_pi
      keccak_f.iota s_chi r1.i) =
        .ok (lift_perm r2 (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap) :=
    holds_chain_eq_ok h_round2
  rw [h_c2]
  simp only [Aeneas.Std.bind_tc_ok]
  -- Round 3.
  have h_c3 : (do
      let s_theta ← keccak_f.theta_unrolled
        (lift_perm r2 (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap)
      let s_rho ← keccak_f.rho_unrolled s_theta
      let s_pi ← keccak_f.pi_unrolled s_rho
      let s_chi ← keccak_f.chi_unrolled s_pi
      keccak_f.iota s_chi r2.i) =
        .ok (lift_perm r3 id impl_swap) :=
    holds_chain_eq_ok h_round3
  rw [h_c3]
  -- Goal reduces to: (do let r ← .ok X; pure (r = X)).holds, which is True.
  simp only [Aeneas.Std.bind_tc_ok]
  -- Now: (pure (lift_perm r3 id impl_swap = lift_perm r3 id impl_swap)).holds
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]
  trivial

/-! ## 24-round (keccakf1600) equivalence

The outer loop body in `keccak.keccakf1600` calls `keccakf1600_4rounds`
6 times. Each iteration advances `s.i` by 4 and accumulates 4 more
spec rounds. -/

@[irreducible]
def keccakf1600_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  -- Apply spec_round_step 24 times starting from `lift s` with round
  -- indices 0..23 (each `Nat` index `< 24` converted via `roundOfNat`).
  -- The folded `Result (Std.Array …)` is then compared to the impl
  -- lift inside a final `pure (… = …)`, yielding `Result Prop` whose
  -- `.holds` is the post.
  (do
    let lifted_final ← Nat.fold 24
      (fun i h acc => acc >>= fun st => spec_round_step st (roundOfNat i (by omega)))
      (pure (lift s))
    pure (lifted_final = lift_perm r_impl id impl_swap)).holds

/-! ## Loop spec (Thread C)

The loop spec talks only about the `.st` field of the loop output —
`lift_perm` is independent of `.i`. Concretely: after the 6-iteration
loop, the lifted (`id`-perm) output `.st` equals the 24-fold spec
round application of `lift s`. -/

def keccakf1600_loop_post (s : state.KeccakState) (s_final : state.KeccakState) : Prop :=
  (do
    let lifted_final ← Nat.fold 24
      (fun i h acc => acc >>= fun st => spec_round_step st (roundOfNat i (by omega)))
      (pure (lift s))
    pure (lifted_final = lift_perm s_final id impl_swap)).holds

/-- Pending: full loop induction via `loop.spec_decr_nat` (Aeneas's
    generic well-founded loop combinator), threading `four_round_equiv`
    through each of 6 iterations. The invariant tracks
    `s_iter.i.val = 4 * iter.start.toNat` and the 4k-fold spec state. -/
theorem keccakf1600_loop_equiv (s : state.KeccakState) (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_loop { start := 0#i32, «end» := 6#i32 } s
    ⦃ ⇓ s_final => ⌜ keccakf1600_loop_post s s_final ⌝ ⦄ := by
  sorry

/-- Top-level equivalence: `keccak.keccakf1600` (the full 24-round
    permutation) on the bit-interleaved impl produces a state whose
    swap-aware lift equals the spec's 24-fold round application.

    Proof iterates `four_round_equiv` 6 times via the outer
    `keccakf1600_loop`. The loop invariant tracks `s.i` and the
    accumulated spec state. -/
theorem keccakf1600_equiv (s : state.KeccakState) (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakf1600_post s r_impl ⌝ ⦄ := by
  -- Strategy: split via `Triple.bind` at the `i := 0` reset. The reset
  -- preserves `lift_perm` since `lift_perm` reads only `.st`. The loop
  -- side delegates to `keccakf1600_loop_equiv` (Thread C).
  unfold keccak.keccakf1600
  apply Std.Do.Triple.bind _ _ (keccakf1600_loop_equiv s h_i)
  intro s_final
  apply triple_imp_intro
  intro h_loop
  -- Goal: ⦃True⦄ ok {s_final with i := 0#usize} ⦃⇓ r => ⌜keccakf1600_post s r⌝⦄
  -- The post `keccakf1600_post s r` says
  --   (Nat.fold 24 spec_round_step (lift s) = lift_perm r id impl_swap).
  -- `lift_perm` ignores `.i`, so `lift_perm {s_final with i := 0} = lift_perm s_final`.
  -- Reduces to `h_loop` (which is `keccakf1600_loop_post s s_final`).
  unfold keccakf1600_post
  unfold keccakf1600_loop_post at h_loop
  -- `lift_perm` reads only `.st`, so setting `.i := 0` doesn't change the lift.
  have h_lift_eq : lift_perm { s_final with i := 0#usize } id impl_swap
                 = lift_perm s_final id impl_swap := by
    unfold lift_perm; rfl
  -- Reduce `⦃True⦄ Result.ok v ⦃⇓ r => ⌜Q r⌝⦄` to `Q v`, then bridge by h_lift_eq.
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h_loop ⊢
  rw [h_lift_eq]
  simpa using h_loop


end libcrux_iot_sha3.Equivalence
