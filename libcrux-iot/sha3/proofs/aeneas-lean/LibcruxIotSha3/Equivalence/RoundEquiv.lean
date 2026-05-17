/-
  Per-round functional equivalence (impl-side `keccakf1600_round{N}_*`
  composed against the spec-side `theta_unrolled ∘ rho_unrolled ∘
  pi_unrolled ∘ chi_unrolled ∘ iota`).

  This file composes `theta_lift_spec` and `prc_lift_spec` (round 0)
  into a single Triple establishing the full per-round equivalence.

  ## ⚠️ Status warning — there is NO WORKING `prc_lift_spec` here

  HEAD's 128M monolithic cascade was once built (early in the prior
  session) and produced a `.olean`, but **it has been unreproducible
  ever since**. Rebuilds time out at 128M and 256M alike in this
  environment. There is **no fallback proof**. The only proof of
  `prc_lift_spec` known to work is on the `alex/compositional-round-proof`
  branch (forward-simp algebraic bridge, 20M heartbeats, monolithic
  impl extraction). The current `prc_lift_spec` in `PrcLift.lean`
  must be migrated to that proof shape (R1+R2 in
  `~/.claude/plans/bright-waddling-kettle.md`) — reverting to the
  128M cascade is NOT an option.

  ## Status (2026-05-16 session)

  ### What was added in this session (in this file)
  - `theta_unrolled_applied` + `@[spec] theta_unrolled_spec` —
    pure semantics + auto-firing spec for `keccak_f.theta_unrolled`.
    (NB: placed here, not in `PrcLift.lean`, so the @[spec] is only
    in scope for files that import RoundEquiv. Putting it in PrcLift
    pushed prc_lift_spec's mvcgen budget past 128M.)
  - `keccakf1600_round0_pi_rho_chi_chain` + `@[spec]` —
    wraps `pi_rho_chi_1 ; pi_rho_chi_2` so mvcgen can auto-fire it;
    chain's @[spec] is `exact prc_lift_spec s hi`.
  - `round0_post` (kept from prior session) + the `round0_equiv_spec`
    skeleton using the chain wrapper.

  ### Blocker (HEAD prc_lift_spec is fragile at 128M)
  HEAD's `prc_lift_spec` was once built successfully at 128M
  heartbeats earlier in this session (.olean produced). Every
  subsequent rebuild — *with exactly the same source* (verified via
  `git diff HEAD --stat`) — times out at 128M during whnf, leaving
  no .olean. Bumping to 256M or 400M lets the simp cascade finish
  but then leaves 25 unsolved lane goals; `grind` and `bv_decide`
  fallbacks couldn't close them either. The proof is at the edge
  of mvcgen's non-determinism budget and is not reproducibly
  buildable in this environment without further restructuring.

  Until that's fixed, RoundEquiv.lean cannot build (it depends on
  the chain wrapper, which depends on prc_lift_spec).

  ### What's mathematically verified to suffice
  `theta_lift_spec` (with i-preservation from commit 659f142) +
  `prc_lift_spec` are sufficient to prove `round0_equiv_spec`.
  The composition substitutes
    `theta_unrolled (lift s) = lift_theta_applied r_θ`  (theta's post)
  into prc_lift_spec's post, with `r_θ.i = s.i` discharging the
  `s.i < 24` precondition on the chain. The result is literally
  `round0_post s r_impl`.

  ### Recommended next steps (in priority order)
  1. **Stabilize prc_lift_spec.** Either find a deterministic
     closer to replace the simp cascade (the current `simp only
     [..., ← lift_xor, ← rot_*, rc_equiv]` succeeds non-
     deterministically), or split the algebraic cascade into a
     small fixed set of named helper lemmas each closed via
     `bv_decide` on a pure BV equation (after explicit rc_equiv
     bridging).
  2. **Correct K→M mapping for the stashed per-lane bridges.**
     The stash@{0} attempt used `M = impl_perm K`. The user
     identified this is wrong due to a 5·x+y vs 5·j+i convention
     mismatch between spec and impl: the spec's lane index is
     `5·x+y` while the impl's `get_with_zeta s i j zeta` returns
     `s.st[5·j+i]`. The right map is `K → impl_perm (transpose K)`
     where `transpose : Fin 25 → Fin 25` swaps the two base-5
     digits. Recover the stash, fix the K→M map per this rule,
     and retry the cascade.
  3. **Convention helpers.** Either change the impl's Rust source
     to use spec's 5·x+y (touches `get_with_zeta`, re-extraction),
     or change the spec to 5·j+i (touches `pi_table`, `rho_offset`,
     `chi_applied`; both blocked by the immutability rule in
     `feedback_spec_changes_rust_and_lean.md`),
     or introduce a Lean-only `transpose : Fin 25 → Fin 25` and
     use `impl_perm ∘ transpose` everywhere lift_perm appears.
     The transpose helper is least invasive.

  ## Status (2026-05-17 session: per-lane cascade root-cause)

  Resumed from 2026-05-16 stash apply. Investigated the
  `simp made no progress` blocker on the per-lane bridges and
  confirmed the structural mismatch via LSP probing:

  **Goal state at `prc_lane_cascade` entry** (Lane 0, after
  `unfold prc_spec; simp only [Std.Array.make]`):
  ```
  LHS = lift_lane_bv (impl_chi_0_z0).bv (impl_chi_0_z1).bv
  RHS = [chi_0_U64, chi_1_U64, ..., chi_24_U64][0]!.bv
  ```
  Both sides are at U64 level. Issue 1: the RHS list lookup
  `[...][0]!.bv` is not evaluated by `simp only [Std.Array.make]` —
  needs `List.getElem!_cons_zero, List.getElem!_cons_succ`.

  After adding those, the goal becomes:
  ```
  LHS = lift_lane_bv (((sst[0][0].bv ^^^ sd[0][0].bv).rotateLeft 0 ^^^
        ~~~(...).rotateLeft 22 &&& (...).rotateLeft 22 ^^^ RC0.bv)) (z1)
  RHS = (lift_lane_bv (sst[0][0].bv ^^^ sd[0][0].bv) (sst[0][1].bv ^^^
        sd[0][1].bv)).rotateLeft 0 ^^^ ~~~(lift_lane_bv ...).rotateLeft 44
        &&& (lift_lane_bv ...).rotateLeft 43 ^^^ ROUND_CONSTANTS[s.i]!.bv
  ```
  Issue 2: LHS is **fused** (single `lift_lane_bv` of impl chi); RHS
  is **split** (chain of `(lift_lane_bv ...).rotateLeft` terms). The
  `← lift_xor, ← rot_N` cascade cannot bridge these — the rewrites
  require their input pattern on the goal, and neither side has the
  pattern needed to fold to the other's form.

  Why the **original 128M cascade** closes the analogous goal: after
  `simp_all only []` substitutes chain hypotheses from mvcgen, the
  impl side becomes a chain of `(rot32 (impl_chi).bv N) ^^^ ...` —
  the **split** form at half level. Then `lift_xor` folds halves
  into `lift_lane_bv`, and `rot_N` folds rotations. The bridges
  bypass mvcgen so they don't get the split chain — they have the
  fused form pre-substituted into a single chi formula per zeta.

  ### Workable approaches (not completed)

  Option A (chain-hyp helper bridges) — most viable:
  ```
  theorem prc_lift_lane_K_helper
      (h_chain_z0 : r_impl.st.val[M]!.val[0]! = <chi_K_z0 of s>)
      (h_chain_z1 : r_impl.st.val[M]!.val[1]! = <chi_K_z1 of s>) :
      lift_lane (r_impl.st.val[M]!) = (prc_spec ...).val[K]! := by
    rw [← Std.U64.bv_eq_imp_eq]
    simp only [lift_lane]
    simp_all only []   -- substitutes h_chain_z0, h_chain_z1
    -- Now LHS = lift_lane_bv <chi_K_z0>.bv <chi_K_z1>.bv (split form)
    --     RHS = (prc_spec ...).val[K]!.bv (still in chi-formula form)
    unfold prc_spec
    simp only [Std.Array.make, List.getElem!_cons_zero, List.getElem!_cons_succ]
    apply Std.U64.bv_eq_imp_eq
    simp only [rot64, Std.UScalar.bv_xor, lift_theta_applied_bv_*, ...]
    simp only [← lift_xor, ← rot_*, rc_equiv]
  ```
  prc_lift_spec then passes the chain hyps from its mvcgen output
  to each helper.

  Option B (skip bridges, golf monolithic cascade): factor the third
  `simp_all only []` and fourth `simp only [← lift_xor, ...]` into
  a single tactic that's specifically tuned. May not help heartbeats.

  Option C (halves-level intermediate `prc_spec_halves`): the stash
  contains this. Bridge 1 (impl → halves) is near-rfl. Bridge 2
  (halves → prc_spec) is a pure spec-level lemma where lift_xor
  cascade works. Not attempted in detail this session.

  ### Current commit state (this session)
  - All 25 `prc_lift_lane_K` bridges have full statements + sorry bodies.
  - `prc_lane_cascade` macro retained for future iteration.
  - `prc_spec_halves` definition retained.
  - `prc_lift_spec` body refactored to call bridges via `exact (prc_lift_lane_K s hi).symm`.
  - With sorry bridges, `prc_lift_spec` and `RoundEquiv` compile but with
    pending `sorry` warnings. Verified via `lean_diagnostic_messages` that
    the structural cascade through `cons_eq_cons + bv_eq_imp_eq + lift_lane`
    splits to 25 goals as expected; bridges close each via `exact`.

  ## Status (2026-05-16 session: per-lane bridge attempt)

  Goal of this session: bring `prc_lift_spec` from 128M heartbeats to
  ≤32M (user's project rule). Attempted decomposition: extract the
  algebraic cascade in `prc_lift_spec` into 25 per-lane bridge lemmas
  + a halves-shaped intermediate `prc_spec_halves`.

  ### What worked
  - HEAD's 128M `prc_lift_spec` rebuild verified clean (45 min wall).
  - Designed and wrote `prc_spec_halves` (50-cell U32-halves intermediate)
    + 25 per-lane bridge statements + a refactored prc_lift_spec body
    that uses them. ~600 lines added.
  - Audited the 25 bridge statements against the 10 sub-fn FCs; found
    and fixed Lane 23 (bx0/bx1 swapped between zetas).

  ### What didn't work
  Three failure modes hit, each blocked the build:

  1. **Original cascade direction (← lift_xor, ← rot_*, rc_equiv)**:
     `simp_all` made no progress in the per-lane bridges. Root cause:
     the existing 128M proof's `simp_all` step relies on **chain
     hypotheses** from `hax_mvcgen` to substitute `r_impl.st.val[M]!.
     val[zeta]!` cells with their chi formulas. The bridges are
     standalone theorems with no chain hyps in context, so `simp_all`
     has nothing to do and fails with "no progress" (since `only [...]`
     requires progress).

  2. **`try simp_all` + cascade**: the `try` swallowed the no-op, but
     then the final `simp [← lift_xor, ...]` step failed similarly —
     no patterns in the goal matched the reverse-direction lemmas
     because the bridge's RHS is in fused form (single `lift_lane_bv`
     with chi inside) while the LHS is in factored form (chain of
     `lift_lane_bv ... ^^^ ...` with `rotateLeft`).

  3. **`bv_decide` after unfolding `lift_lane_bv + spread_to_even`**:
     bv_decide returned "potentially spurious counterexamples" for
     all 25 bridges. Counterexample values look like spurious from
     opaque `RC_INTERLEAVED_0/1` and `ROUND_CONSTANTS` not being linked
     (via `rc_equiv`). The `try rw [← rc_equiv _ (by assumption)]` in
     the macro may not have fired; need to debug. Also: bv_decide on
     the 5-step `spread_to_even` × 6 rot32 × chi formula at U32 halves
     is likely past bv_decide's effective tractability budget (16M
     heartbeats per bridge insufficient).

  ### Key blocker (not fully diagnosed)

  The existing 128M `prc_lift_spec` proof closes via:
  ```
  all_goals simp only [← lift_xor, ← lift_chi, ← rot_*, rc_equiv]
  ```
  This is the same simp set I tried per-lane. The per-lane invocations
  fail "no progress". The existing 25-fold `all_goals` invocation works.

  Hypothesis: simp's matching across 25 simultaneous goals somehow
  enables progress that doesn't happen on individual goals. Or there's
  a critical state-difference at the entry to step 4 that my bridges
  don't replicate (despite the same upstream simps).

  Need to query LSP `lean_goal` at the failing line of one bridge AND
  at the corresponding step in the existing proof to compare exactly.
  This session's LSP queries timed out; next session needs fresh
  warmup + targeted query.

  ### Stashed work

  The 598-line refactor (prc_spec_halves + 25 bridges + refactored
  prc_lift_spec body) is in `git stash@{0}` ("WIP on alex/verification").
  Recover with `git stash show stash@{0} -p` or `git stash apply
  stash@{0}`. Keep the macro and bridge statements; rework the bridge
  proof strategy.

  ### Recommended next steps (in priority order)

  1. **Use LSP to inspect goal state**: With a fresh build of HEAD,
     query `lean_goal` at the per-lane simp step (after `all_goals (apply
     Std.U64.bv_eq_imp_eq)` in the existing proof) for lane K=0. Then
     compare to the goal state at the bridge's entry to the final simp.
     If they differ, that's the discrepancy to fix.

  2. **Alternative**: Pass chain hypotheses as explicit parameters to
     per-lane bridges:
     ```
     theorem prc_lift_lane_K_helper
         (s : state.KeccakState) (h : s.i.val < 24)
         (r_impl : state.KeccakState)
         (h_cell_z0 : r_impl.st.val[M]!.val[0]! = chi_z0_concrete)
         (h_cell_z1 : r_impl.st.val[M]!.val[1]! = chi_z1_concrete) :
         (prc_spec (lift_theta_applied s) s.i).val[K]!.bv =
         lift_lane(r_impl.st.val[M]!).bv := by
       <existing 128M cascade per-lane>
     ```
     With chain hyps in scope, simp_all + cascade closes (just like
     in the existing proof). Each helper ≤5M. prc_lift_spec uses 25
     helpers; itself ≤16M for impl-side work.

  3. **If both fail**: leave prc_lift_spec at 128M but document that
     the user's ≤32M rule cannot be met without a deeper architectural
     change (e.g., different intermediate spec shape, or different
     simp set for the cascade).

  ## Prior session status (preserved for context)

  Three structural issues from the prior session — all still apply:

  - **FIXED in 2026-05-15 session**: `theta_lift_spec` now preserves
    `r_impl.i = s.i` (commit 659f142).

  - **NOT FIXED**: `keccak_f.theta_unrolled` has no `@[spec]` lemma.
    Need `theta_unrolled_applied` + `@[spec] theta_unrolled_spec`
    mirroring `rho_unrolled_spec`. 25-cell Array.make body.

  - **NOT FIXED**: `prc_lift_spec` is keyed on a 2-call do-block, not
    a single function. mvcgen's `@[spec]` matcher does not auto-fire
    do-block specs in chain context. Wrap impl 2-call in
    `def keccakf1600_round0_pi_rho_chi_chain` and rekey prc_lift_spec.

  ## Resumption

  See `~/.claude/plans/breezy-leaping-dove.md` Step 8 follow-on for
  the planned `theta_unrolled_applied` + `prc_chain` refactor.
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
def round0_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta_unrolled (lift s)
    let s_rho ← keccak_f.rho_unrolled s_theta
    let s_pi ← keccak_f.pi_unrolled s_rho
    let s_chi ← keccak_f.chi_unrolled s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl impl_perm impl_swap)).holds

set_option maxHeartbeats 32000000 in
theorem round0_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round0_theta s
        keccakf1600_round0_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round0_post s r_impl⌝ ⦄ := by
  unfold round0_post
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _
       simp_all)

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

-- @[spec] (added when prc_lift_spec_1 body is filled in)
theorem keccakf1600_round1_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round1_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled (lift_theta_applied s)
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm) impl_swap)).holds ⌝ ⦄ := by
  unfold keccakf1600_round1_pi_rho_chi_chain
  exact prc_lift_spec_1 s hi

def keccakf1600_round2_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round2_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round2_pi_rho_chi_2 r1

-- @[spec] (added when prc_lift_spec_2 body is filled in)
theorem keccakf1600_round2_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round2_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled (lift_theta_applied s)
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap)).holds ⌝ ⦄ := by
  unfold keccakf1600_round2_pi_rho_chi_chain
  exact prc_lift_spec_2 s hi

def keccakf1600_round3_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round3_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round3_pi_rho_chi_2 r1

-- @[spec] (added when prc_lift_spec_3 body is filled in)
theorem keccakf1600_round3_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round3_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled (lift_theta_applied s)
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl id impl_swap)).holds ⌝ ⦄ := by
  unfold keccakf1600_round3_pi_rho_chi_chain
  exact prc_lift_spec_3 s hi

/-- Spec-chain claim for round 1 (input s is the round-0 impl output, so
    the spec lift uses `impl_perm` permutation + `impl_swap`). -/
def round1_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta_unrolled (lift_perm s impl_perm impl_swap)
    let s_rho ← keccak_f.rho_unrolled s_theta
    let s_pi ← keccak_f.pi_unrolled s_rho
    let s_chi ← keccak_f.chi_unrolled s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm) impl_swap)).holds

theorem round1_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round1_theta s
        keccakf1600_round1_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round1_post s r_impl⌝ ⦄ := by
  -- Same shape as round0_equiv_spec; closes by `hax_mvcgen + simp_all`
  -- once `theta_lift_spec_1` and `prc_lift_spec_1` are tagged `@[spec]`
  -- (currently sorry'd in their stub files).
  sorry

def round2_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta_unrolled (lift_perm s (impl_perm ∘ impl_perm) impl_swap)
    let s_rho ← keccak_f.rho_unrolled s_theta
    let s_pi ← keccak_f.pi_unrolled s_rho
    let s_chi ← keccak_f.chi_unrolled s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap)).holds

theorem round2_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round2_theta s
        keccakf1600_round2_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round2_post s r_impl⌝ ⦄ := by sorry

def round3_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta_unrolled
      (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap)
    let s_rho ← keccak_f.rho_unrolled s_theta
    let s_pi ← keccak_f.pi_unrolled s_rho
    let s_chi ← keccak_f.chi_unrolled s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl id impl_swap)).holds

theorem round3_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round3_theta s
        keccakf1600_round3_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round3_post s r_impl⌝ ⦄ := by sorry

end libcrux_iot_sha3.Equivalence
