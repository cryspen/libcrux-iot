/-
  Per-round functional equivalence (impl-side `keccakf1600_round{N}_*`
  composed against the spec-side `theta_unrolled ∘ rho_unrolled ∘
  pi_unrolled ∘ chi_unrolled ∘ iota`).

  This file composes `theta_lift_spec` and `prc_lift_spec` (round 0)
  into a single Triple establishing the full per-round equivalence.

  ## Status — all four rounds proven

  `round{0,1,2,3}_equiv_spec` each build at 16M heartbeats. The four
  proofs follow the same shape (one `hax_mvcgen`, side-goal `scalar_tac`
  chain, `unfold round{k}_post` + `casesm` + second `hax_mvcgen` +
  `simp_all`) and each is tagged `@[spec]` for the top-level composition.

  ### Key discipline (don't break)
  Each `round{k}_post` is declared `@[irreducible]`. This is load-bearing:
  without it, `hax_mvcgen` unfolds the post, sees the spec do-block
  `(do θ; ρ; π; χ; ι _ s.i).holds`, and recursively dispatches
  `theta_unrolled_spec / rho_unrolled_spec / …` *in addition to* the
  impl-side `theta_lift_spec + chain_spec` dispatches — blowing the
  heartbeat budget past 32M. With `@[irreducible]` the post stays
  opaque during impl-side mvcgen; we then unfold it and run a
  *second* `hax_mvcgen` (the spec do-block has the chain hypotheses
  already in scope from the first mvcgen, so the spec dispatch is
  cheap). See `feedback_irreducible_post_def_for_mvcgen` memory.

  ## Architecture

  - `theta_unrolled_applied` + `@[spec] theta_unrolled_spec` —
    pure semantics + auto-firing spec for `keccak_f.theta_unrolled`.
    (NB: placed here, not in `PrcLift.lean`, so the @[spec] is only
    in scope for files that import RoundEquiv. Putting it in PrcLift
    pushed prc_lift_spec's mvcgen budget past 128M.)
  - `keccakf1600_round{k}_pi_rho_chi_chain` + `@[spec]` wrappers
    package `pi_rho_chi_1 ; pi_rho_chi_2` so the @[spec] matcher
    fires on a single named function in chain context.
  - `round{k}_post` (each `@[irreducible]`) names the spec-side
    `(do θ; ρ; π; χ; ι _ s.i).holds` predicate so `hax_mvcgen` does
    not recursively dispatch the 5 spec lemmas during impl
    advancement.

  ## Round dependencies

  Each `round{k}_equiv_spec` discharges via the underlying
  `theta_lift_spec_k` and `prc_lift_spec_k` lemmas (see
  `ThetaLiftRound{1,2,3}.lean`, `PrcLiftRound{1,2,3}.lean`). All four
  round specs are tagged `@[spec]` so the top-level `four_round_equiv`
  fires them automatically.
-/
import LibcruxIotSha3.Equivalence.ThetaLift
import LibcruxIotSha3.Equivalence.ThetaLiftRound1
import LibcruxIotSha3.Equivalence.ThetaLiftRound2
import LibcruxIotSha3.Equivalence.ThetaLiftRound3
import LibcruxIotSha3.Equivalence.PrcLift
import LibcruxIotSha3.Equivalence.PrcLiftRound1
import LibcruxIotSha3.Equivalence.PrcLiftRound2
import LibcruxIotSha3.Equivalence.PrcLiftRound3
import LibcruxIotSha3.Equivalence.Lift
import Hax

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

/-! ## Spec-side `@[spec]` for `keccak_f.theta_unrolled`

Kept here (not in `PrcLift.lean`) so the @[spec] registration only
applies to files that import `RoundEquiv`. Adding it to `PrcLift.lean`
caused `prc_lift_spec`'s mvcgen pass to drift past the 128M heartbeat
cap (HEAD baseline was just under). -/

/-- Pure semantics of `keccak_f.theta_unrolled`: column XOR (c_x), then
    d_x = c_{x-1} ^ rot64(c_{x+1}, 1), then state[k] ^ d_{k/5}.
    Mirrors `HacspecSha3/.../Funs.lean:546`. -/
def theta_unrolled_applied (state : Std.Array Std.U64 25#usize) :
    Std.Array Std.U64 25#usize :=
  let c0 := state.val[0]! ^^^ state.val[1]! ^^^ state.val[2]! ^^^ state.val[3]! ^^^ state.val[4]!
  let c1 := state.val[5]! ^^^ state.val[6]! ^^^ state.val[7]! ^^^ state.val[8]! ^^^ state.val[9]!
  let c2 := state.val[10]! ^^^ state.val[11]! ^^^ state.val[12]! ^^^ state.val[13]! ^^^ state.val[14]!
  let c3 := state.val[15]! ^^^ state.val[16]! ^^^ state.val[17]! ^^^ state.val[18]! ^^^ state.val[19]!
  let c4 := state.val[20]! ^^^ state.val[21]! ^^^ state.val[22]! ^^^ state.val[23]! ^^^ state.val[24]!
  let d0 : Std.U64 := c4 ^^^ ⟨c1.bv.rotateLeft 1⟩
  let d1 : Std.U64 := c0 ^^^ ⟨c2.bv.rotateLeft 1⟩
  let d2 : Std.U64 := c1 ^^^ ⟨c3.bv.rotateLeft 1⟩
  let d3 : Std.U64 := c2 ^^^ ⟨c4.bv.rotateLeft 1⟩
  let d4 : Std.U64 := c3 ^^^ ⟨c0.bv.rotateLeft 1⟩
  Std.Array.make 25#usize [
    state.val[0]! ^^^ d0, state.val[1]! ^^^ d0, state.val[2]! ^^^ d0,
    state.val[3]! ^^^ d0, state.val[4]! ^^^ d0,
    state.val[5]! ^^^ d1, state.val[6]! ^^^ d1, state.val[7]! ^^^ d1,
    state.val[8]! ^^^ d1, state.val[9]! ^^^ d1,
    state.val[10]! ^^^ d2, state.val[11]! ^^^ d2, state.val[12]! ^^^ d2,
    state.val[13]! ^^^ d2, state.val[14]! ^^^ d2,
    state.val[15]! ^^^ d3, state.val[16]! ^^^ d3, state.val[17]! ^^^ d3,
    state.val[18]! ^^^ d3, state.val[19]! ^^^ d3,
    state.val[20]! ^^^ d4, state.val[21]! ^^^ d4, state.val[22]! ^^^ d4,
    state.val[23]! ^^^ d4, state.val[24]! ^^^ d4
  ]

set_option maxHeartbeats 16000000 in
@[spec]
theorem theta_unrolled_spec (state : Std.Array Std.U64 25#usize) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f.theta_unrolled state
    ⦃ ⇓ r => ⌜ r = theta_unrolled_applied state ⌝ ⦄ := by
  unfold keccak_f.theta_unrolled
  hax_mvcgen
  all_goals try scalar_tac
  unfold theta_unrolled_applied
  apply Subtype.ext
  simp only [Std.Array.make]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
  all_goals simp_all only [Std.UScalar.bv_xor, Std.UScalarTy.U64_numBits_eq,
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
    show ((0#u32 : Std.U32).val) = 0 from rfl,
    show ((1#u32 : Std.U32).val) = 1 from rfl]

/-! ## Chain wrapper for round-0 πρχι

`prc_lift_spec` is keyed on a 2-call do-block `(do prc_1; prc_2)`,
which mvcgen's `@[spec]` matcher does not auto-fire in chain context.
Wrapping the two calls in a named function lets the `@[spec]` matcher
fire on the chain inside `round0_equiv_spec`. -/

def keccakf1600_round0_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round0_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round0_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round0_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round0_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled (lift_theta_applied s)
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl impl_perm impl_swap)).holds ⌝ ⦄ := by
  unfold keccakf1600_round0_pi_rho_chi_chain
  exact prc_lift_spec s hi

/-- Spec-chain claim for round 0 (opaque to `mvcgen`). Wrapping the
    spec do-block in this `def` prevents `mvcgen` from trying to
    advance `wp⟦theta_unrolled (lift s)⟧` in the post during impl
    advancement. -/
@[irreducible]
def round0_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta_unrolled (lift s)
    let s_rho ← keccak_f.rho_unrolled s_theta
    let s_pi ← keccak_f.pi_unrolled s_rho
    let s_chi ← keccak_f.chi_unrolled s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl impl_perm impl_swap)).holds

set_option maxHeartbeats 16000000 in
theorem round0_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round0_theta s
        keccakf1600_round0_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round0_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round0_post
       -- Spec post is now `(do θ; ρ; π; χ; ι _ s.i).holds`.
       -- Use the chain hypotheses (already in scope from mvcgen's
       -- dispatch of chain_spec) to thread through each spec.
       casesm* _ ∧ _
       hax_mvcgen
       all_goals first | scalar_tac | simp_all)

/-! ## Chain wrappers + round equivs for rounds 1, 2, 3

Each round's chain wrapper packages `pi_rho_chi_1; pi_rho_chi_2` so the
`@[spec]` matcher can fire on a single named function. The post chains
the round-k spec via `theta_lift_spec_k` (auto-firing on the theta call)
+ `prc_lift_spec_k` (auto-firing via the chain wrapper).
-/

def keccakf1600_round1_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round1_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round1_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round1_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round1_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled
            (lift_theta_applied_perm s impl_perm (impl_swap_k 1))
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm) (impl_swap_k 2))).holds ⌝ ⦄ := by
  unfold keccakf1600_round1_pi_rho_chi_chain
  exact prc_lift_spec_1 s hi

def keccakf1600_round2_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round2_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round2_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round2_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round2_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled
            (lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2))
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl
            (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))).holds ⌝ ⦄ := by
  unfold keccakf1600_round2_pi_rho_chi_chain
  exact prc_lift_spec_2 s hi

def keccakf1600_round3_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round3_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round3_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round3_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round3_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled
            (lift_theta_applied_perm s
              (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          -- Round 3 output uses canonical `lift` (= `lift_perm _ id swZero`,
          -- via `impl_perm^[4] = id` and `impl_swap_k 4 = swZero`).
          pure (r_spec = Equivalence.lift r_impl)).holds ⌝ ⦄ := by
  unfold keccakf1600_round3_pi_rho_chi_chain
  exact prc_lift_spec_3 s hi

/-- Spec-chain claim for round 1 (input s is the round-0 impl output, so
    the spec lift uses `impl_perm` permutation + `impl_swap_k 1`, where
    `impl_swap_k 1 = impl_swap`). Output uses `impl_swap_k 2`. -/
@[irreducible]
def round1_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta_unrolled (lift_perm s impl_perm (impl_swap_k 1))
    let s_rho ← keccak_f.rho_unrolled s_theta
    let s_pi ← keccak_f.pi_unrolled s_rho
    let s_chi ← keccak_f.chi_unrolled s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm) (impl_swap_k 2))).holds

set_option maxHeartbeats 16000000 in
theorem round1_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round1_theta s
        keccakf1600_round1_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round1_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round1_post
       casesm* _ ∧ _
       hax_mvcgen
       all_goals first | scalar_tac | simp_all)

@[irreducible]
def round2_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta_unrolled
      (lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2))
    let s_rho ← keccak_f.rho_unrolled s_theta
    let s_pi ← keccak_f.pi_unrolled s_rho
    let s_chi ← keccak_f.chi_unrolled s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))).holds

set_option maxHeartbeats 16000000 in
theorem round2_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round2_theta s
        keccakf1600_round2_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round2_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round2_post
       casesm* _ ∧ _
       hax_mvcgen
       all_goals first | scalar_tac | simp_all)

@[irreducible]
def round3_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta_unrolled
      (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))
    let s_rho ← keccak_f.rho_unrolled s_theta
    let s_pi ← keccak_f.pi_unrolled s_rho
    let s_chi ← keccak_f.chi_unrolled s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    -- Output uses `impl_swap_k 4 = (fun _ => false)`, i.e. the canonical
    -- `lift` (after `impl_perm^[4] = id`). Equivalent to `lift r_impl`.
    pure (r_spec = Equivalence.lift r_impl)).holds

set_option maxHeartbeats 16000000 in
theorem round3_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round3_theta s
        keccakf1600_round3_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round3_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round3_post
       casesm* _ ∧ _
       hax_mvcgen
       all_goals first | scalar_tac | simp_all)

/-! ## Triple combinator: conjunction of posts (deterministic monad)

For `Result α` (a deterministic monad), if we have two Triples
proving distinct posts about the same computation, their conjunction
also holds. Used in `four_round_equiv` to combine each round's
algebraic `round_k_post` with the `r_impl.i.val = s.i.val + 1`
i-increment fact, so the subsequent round's `s.i.val < 24`
precondition can be discharged. -/

theorem triple_conj_post {α} {e : Aeneas.Std.Result α} {Q R : α → Prop}
    (hQ : ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄)
    (hR : ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜R r⌝⦄) :
    ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r ∧ R r⌝⦄ := by
  cases e
  · simp_all [Std.Do.Triple, WP.wp]
  · simp_all [Std.Do.Triple, WP.wp]
  · simp_all [Std.Do.Triple, WP.wp]

/-- Lift a pure-prop precondition `⌜P⌝` of a `Triple` into a `Lean`-level
hypothesis. Used in `four_round_equiv` so that the post of each round
(threaded into the next round's `Triple` as a pure precondition) can
be destructured to extract the i-increment chain
(`r0.i.val = s.i.val + 1`, `r1.i.val = r0.i.val + 1`, …). -/
theorem triple_imp_intro {α} {e : Aeneas.Std.Result α} {P : Prop} {Q : α → Prop}
    (h : P → ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄) :
    ⦃⌜P⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄ := by
  cases e
  · simp_all [Std.Do.Triple, WP.wp]
  · simp_all [Std.Do.Triple, WP.wp]
  · simp_all [Std.Do.Triple, WP.wp]

/-- Weaken precondition of a `Triple` from `⌜True⌝` to any `P`. Trivial
because `P ⊢ ⌜True⌝` always holds. Used in `four_round_equiv` to thread
the post of each round (a non-trivial precondition) into the next
round's `Triple` (which has `⌜True⌝` precondition). -/
theorem triple_weaken_precond {α} {e : Aeneas.Std.Result α}
    {P : Std.Do.Assertion
      (Std.Do.PostShape.except Aeneas.Std.Error
        (Std.Do.PostShape.except PUnit.{1} Std.Do.PostShape.pure))}
    {Q : α → Prop} (h : ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄) :
    ⦃P⦄ e ⦃⇓ r => ⌜Q r⌝⦄ := by
  apply Std.Do.Triple.of_entails_left _ h
  intro _
  trivial

/-! ## Per-round i-increment sidecars

The `round_k_equiv_spec` post (`round_k_post`) gives the algebraic
equivalence but does not expose `r_impl.i.val = s.i.val + 1`. The
impl bumps `i` by 1 per round (the `pi_rho_chi_y0_zeta1` step in
each `pi_rho_chi_1`). These sidecar lemmas expose that fact so
`four_round_equiv` can discharge each subsequent round's precondition
`s.i.val < 24`. -/

set_option maxHeartbeats 16000000 in
theorem round0_i_inc (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round0_theta s
        keccakf1600_round0_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜ r_impl.i.val = s.i.val + 1 ⌝ ⦄ := by
  unfold keccakf1600_round0_pi_rho_chi_chain
  unfold keccak.keccakf1600_round0_pi_rho_chi_1
  unfold keccak.keccakf1600_round0_pi_rho_chi_2
  hax_mvcgen
  all_goals scalar_tac

set_option maxHeartbeats 16000000 in
theorem round1_i_inc (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round1_theta s
        keccakf1600_round1_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜ r_impl.i.val = s.i.val + 1 ⌝ ⦄ := by
  unfold keccakf1600_round1_pi_rho_chi_chain
  unfold keccak.keccakf1600_round1_pi_rho_chi_1
  unfold keccak.keccakf1600_round1_pi_rho_chi_2
  hax_mvcgen
  all_goals scalar_tac

set_option maxHeartbeats 16000000 in
theorem round2_i_inc (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round2_theta s
        keccakf1600_round2_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜ r_impl.i.val = s.i.val + 1 ⌝ ⦄ := by
  unfold keccakf1600_round2_pi_rho_chi_chain
  unfold keccak.keccakf1600_round2_pi_rho_chi_1
  unfold keccak.keccakf1600_round2_pi_rho_chi_2
  hax_mvcgen
  all_goals scalar_tac

set_option maxHeartbeats 16000000 in
theorem round3_i_inc (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round3_theta s
        keccakf1600_round3_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜ r_impl.i.val = s.i.val + 1 ⌝ ⦄ := by
  unfold keccakf1600_round3_pi_rho_chi_chain
  unfold keccak.keccakf1600_round3_pi_rho_chi_1
  unfold keccak.keccakf1600_round3_pi_rho_chi_2
  hax_mvcgen
  all_goals scalar_tac

end libcrux_iot_sha3.Equivalence
