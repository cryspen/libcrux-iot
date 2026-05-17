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

  Status: lemma statements present; proof bodies sorry, with comments
  documenting which round_equiv specs are needed. The point is to show
  that the per-round specs are *sufficient* — once the prc_lift and
  theta_lift specs for rounds 1, 2, 3 are discharged, the entire
  chain follows mechanically.
-/
import LibcruxIotSha3.Equivalence.RoundEquiv

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

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

-- 4-round equivalence: `keccakf1600_4rounds` on impl produces a state
-- `r_impl` such that the spec applied 4 times equals
-- `lift_perm r_impl id impl_swap`.
--
-- Proof composes `round{0,1,2,3}_equiv_spec` through the inlined
-- impl chain (theta + prc_chi_1 + prc_chi_2 per round). After
-- round 3 the cumulative permutation is `impl_perm^[4] = id`.
theorem four_round_equiv (s : state.KeccakState) (hi : s.i.val + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_4rounds 0#usize s
    ⦃ ⇓ r_impl => ⌜ four_round_post s hi r_impl ⌝ ⦄ := by
  -- Strategy: unfold keccakf1600_4rounds (a chain of 12 sub-calls);
  -- introduce intermediate states s_θ_k and s_prc_k for k=0..3 via the
  -- chain wrappers; apply round_{0,1,2,3}_equiv_spec sequentially via
  -- Triple.bind, threading the i increments (each prc_chi_1 bumps i);
  -- at the end, fold `lift_perm r impl_perm_4 impl_swap` to
  -- `lift_perm r id impl_swap` via impl_perm_pow4_eq_id.
  sorry

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
  -- Strategy: unfold keccak.keccakf1600 → keccakf1600_loop with its
  -- I32 range iterator over [0, 6); each loop body call is
  -- keccakf1600_4rounds 0#usize. Apply hax_loop with invariant:
  --   ∃ i ∈ [0, 6], s_iter.i.val = 4*i ∧
  --     (Nat.fold (4*i) spec_round_step) (lift s) holds
  --     for the lifted intermediate.
  -- Each loop iteration consumes one four_round_equiv to advance the
  -- invariant. After 6 iterations, s_iter.i = 24 and the spec has been
  -- applied 24 times.
  sorry

end libcrux_iot_sha3.Equivalence
