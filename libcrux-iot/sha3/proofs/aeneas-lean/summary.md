# Keccakf1600 top-down equivalence — proof status (2026-05-18)

## Target

The top-level equivalence theorem in `LibcruxIotSha3/Equivalence/Keccakf1600.lean`:

```lean
theorem keccakf1600_equiv (s : state.KeccakState) (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakf1600_post s r_impl ⌝ ⦄
```

`keccakf1600_post s r_impl` asserts that the lift-aware view of the impl
end-state equals the result of applying the spec round function
`spec_round_step` 24 times to `lift s`.

It depends on two intermediate theorems:

1. `four_round_equiv` (Keccakf1600.lean:101) — proves the 4-round block
   `keccak.keccakf1600_4rounds` equivalent to 4 spec rounds, collapsing
   the cumulative lane permutation to `id` via `impl_perm_pow4_eq_id`.

2. `keccakf1600_equiv` (Keccakf1600.lean:163) — iterates `four_round_equiv`
   six times via the outer `keccakf1600_loop`.

## What has been proven so far

### Lift infrastructure (`Lift.lean`, no sorries)

- Lane representation: `lift_lane_bv`, `lift_lane`, `lift_lane_maybe_swap`,
  `lift` (no-perm, no-swap), `lift_perm` (per-lane permutation + half-swap).
- Permutation algebra: `impl_perm` (rho-table-driven lane permutation),
  `impl_perm_pow4_eq_id` (closed by `decide`), `impl_swap` (per-lane
  parity table), `lift_perm_id`.
- ~40 `rot_N` lemmas (`N = 0..62`, bv_decide-closed) describing how a
  64-bit rotation factors through `lift_lane_bv` (the even-N family
  rotates each half by `N/2`; the odd-N family rotates by `N/2` and
  `(N+1)/2` with halves swapped).
- Lifting algebra: `lift_xor`, `lift_td` (theta-delta combining),
  `lift_getElem_bv_{0..24}` (25 per-lane peel lemmas).

### Spec-side `@[spec]`s (`PrcLift.lean`, `RoundEquiv.lean`)

The five spec round functions all have a pure-semantics
`*_applied` definition and an auto-firing `@[spec]` Triple:

| Spec function           | Pure form                | `@[spec]` lemma          |
|-------------------------|--------------------------|--------------------------|
| `keccak_f.theta_unrolled` | `theta_unrolled_applied` | `theta_unrolled_spec`    |
| `keccak_f.rho_unrolled`   | `rho_applied`            | `rho_unrolled_spec`      |
| `keccak_f.pi_unrolled`    | `pi_applied`             | `pi_unrolled_spec`       |
| `keccak_f.chi_unrolled`   | `chi_applied`            | `chi_unrolled_spec`      |
| `keccak_f.iota`           | `iota_applied`           | `iota_spec` (pre `round.val < 24`) |

### Round 0 (impl `keccakf1600_round0_*`, complete)

- `theta_lift_spec` — impl-θ ≅ spec-θ on `lift s`, with `r_impl.i = s.i`
  (`ThetaLift.lean`).
- `prc_lift_spec` — impl-πρχι ≅ spec-`ρ;π;χ;ι _ s.i` on
  `lift_theta_applied s`, producing `lift_perm r_impl impl_perm impl_swap`
  (`PrcLift.lean`). Backed by ~12 per-FC `@[spec]`s for the
  `pi_rho_chi_y{0..4}_z{0,1}` sub-functions.
- `keccakf1600_round0_pi_rho_chi_chain_spec` — chain-wrapper for the
  2-call πρχι pair (`RoundEquiv.lean`).
- `round0_equiv_spec` — full per-round equivalence: impl-θ then
  impl-πρχι ≅ the 5 spec calls (`RoundEquiv.lean`).
- `round0_i_inc` — sidecar exposing `r_impl.i.val = s.i.val + 1`
  (`RoundEquiv.lean`).

### Composition skeleton (`Keccakf1600.lean`)

- `spec_round_step` — bundles the 5-step spec round.
- `roundOfNat` — Nat → Std.Usize converter for indices `≤ 24`.
- `four_round_post`, `keccakf1600_post` — top-level post defs.
- `keccakf1600_4rounds_fold` — folds the inline 12-call extracted
  `keccak.keccakf1600_4rounds` into 4 nested 2-call (theta_k; chain_k)
  do-blocks so `Triple.bind` can split at round boundaries.
- `triple_conj_post`, `triple_imp_intro`, `triple_weaken_precond` —
  Triple combinators for chaining algebraic + i-bump posts and lifting
  pure-prop preconditions (`RoundEquiv.lean`).
- The structural part of `four_round_equiv`: 3 × `Triple.bind` dispatching
  rounds 0–2 via `triple_conj_post (round_k_equiv_spec) (round_k_i_inc)`,
  with `triple_imp_intro` lifting each round's post into proof context.

## Where we are right now

### Solved this session

- `holds_pure_eq_imp_triple` and `holds_chain_eq_ok` helpers
  (Keccakf1600.lean:25-44) — extract a usable Triple / Result equation
  from a `(do C; pure (r = X)).holds` hypothesis. Closed by
  `cases C <;> simp_all [Result.holds, Triple, WP.wp, Functor.map, SPred.down_pure]`.

- **`four_round_equiv` (Keccakf1600.lean) is now closed** (modulo the
  round-1/2/3 stubs it transitively depends on). Pattern: after the
  pre-existing Triple.bind scaffolding lands `h_round{0,1,2,3}` and
  `h_i{0,1,2,3}` in scope, the analytical step is:
  1. `rw [PostCond.entails_noThrow]; intro r3 hpost; dsimp; obtain ⟨h_round3, h_i3⟩ := hpost`.
  2. `unfold round{0,1,2,3}_post` in the four `h_round_k` hyps.
  3. For each k, `have h_c_k : <explicit chain type> = .ok X_k := holds_chain_eq_ok h_round_k`.
  4. `unfold four_round_post spec_round_step` on the goal.
  5. Alternate `rw [h_c_k]` and `simp only [Aeneas.Std.bind_tc_ok]`,
     prefixed by `rw [h_idx1, h_idx2, h_idx3]` (round-index
     `roundOfNat (s.i.val + k) _ = r_{k-1}.i` via
     `UScalar.eq_of_val_eq` + `UScalar.ofNatCore_val_eq` + `h_i{k-1}`).
  6. Close with `simp only [Result.holds, Triple, WP.wp]; trivial`.
  File-level build: 11.5 s, under the 60 s budget. The theorem uses
  `set_option maxHeartbeats 4000000`.

### Open in this file (`Keccakf1600.lean`)

- `keccakf1600_loop_equiv` (sorry) — the 6-iteration loop spec; the
  only remaining sorry in this file. Plan: apply Aeneas's
  `loop.spec_decr_nat` with measure
  `iter.end.toNat - iter.start.toNat`, invariant
  `s_iter.i.val = 4 * iter.start.toNat ∧
   (Nat.fold (4 * iter.start.toNat) spec_round_step (lift s) =
    lift_perm s_iter (impl_perm^k) impl_swap).holds`
  (with `impl_perm^[4] = id` collapsing every 4 rounds). Each step
  uses `four_round_equiv` once. Needs an I32 iterator-`next` spec
  (analogous to `IteratorRange_next_spec` in the hax
  `LoopEquivalence` example, but for I32 instead of Usize).

- `keccakf1600_equiv` is now **closed conditional on
  `keccakf1600_loop_equiv`**: the proof splits via `Triple.bind` at
  the final `i := 0` reset, observes that `lift_perm` reads only
  `.st` (so setting `.i := 0` doesn't change the lift, witnessed by
  `lift_perm {s_final with i := 0} _ _ = lift_perm s_final _ _ := by
   unfold lift_perm; rfl`), and discharges the loop side via
  `keccakf1600_loop_equiv`.

### Open in lift files (`ThetaLiftRound{1,2,3}.lean`, `PrcLiftRound{1,2,3}.lean`)

- `theta_lift_spec_{1,2,3}` (3 sorries) — each is the round-0
  `theta_lift_spec` re-stated with input `lift_perm s (impl_perm^k) impl_swap`
  for k=1,2,3. Same proof shape expected once filled in.
- `prc_lift_spec_{1,2,3}` (3 sorries) — analogous to `prc_lift_spec`,
  with output permutation `impl_perm^(k+1)` (and `id` for k=3 via
  `impl_perm_pow4_eq_id`). PrcLift's round 0 backbone is ~280 lines of
  per-FC `@[spec]`s; the round-1/2/3 versions will need analogous
  per-FC layers.

### Open in `RoundEquiv.lean`

- `round{1,2,3}_equiv_spec` (lines 281, 305, 322) — per-round
  algebraic equivalence specs. Blocked by `theta_lift_spec_k` +
  `prc_lift_spec_k` for k=1,2,3 in `ThetaLiftRound{1,2,3}.lean` and
  `PrcLiftRound{1,2,3}.lean`. Once those exist, transcribe the round-0
  proof shape (one `hax_mvcgen`, side-goal `scalar_tac`,
  `unfold round{k}_post + casesm + second hax_mvcgen + simp_all`).

- `round{1,2,3}_i_inc` (lines 390, 401, 410) — per-round i-increment
  sidecars. Needs per-FC `@[spec]`s in `PrcLiftRound{1,2,3}.lean`
  analogous to `pi_rho_chi_y0_zeta1_spec_fc` in `PrcLift.lean`. The
  recipe is validated: `round0_i_inc` is proven in 5 lines
  (`unfold` chain + `pi_rho_chi_{1,2}` + `hax_mvcgen` + `scalar_tac`).

## Lessons learned

The key blocker for `four_round_equiv`: applying
`holds_chain_eq_ok h_round0` *without* a type ascription yields a
Result equation whose pretty-printed LHS shows the spec chain fully
reduced to a single `iota (Array.make 25 [...explicit 25-tuple...]) idx`
form (Lean's elaborator eagerly reduces the spec-function chain during
unification). **Giving the `have` an explicit type ascription forces
Lean to keep the chain shape**, after which `rw [h_c_k]` matches the
goal's chain (post `unfold spec_round_step`). Same trick used for all
four `h_c_k`s.

## Discipline (binding, unchanged)

- ≤ 16M heartbeats per theorem.
- ≤ 60 s per file.
- No `simp_all` inside `mvcgen` contexts unless the post-mvcgen goal is
  provably bounded.
- Don't modify `PrcLift.lean`, `ThetaLift.lean`, `Lift.lean` (have
  valid .oleans); don't modify `LibcruxIotSha3.lean` (extraction-driven).
