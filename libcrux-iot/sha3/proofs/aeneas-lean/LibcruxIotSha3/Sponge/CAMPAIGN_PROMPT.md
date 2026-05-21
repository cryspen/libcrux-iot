# Campaign 3 — Autonomous SHA-3 sponge verification

You are running an AUTONOMOUS multi-agent proof campaign. Do not stop for
confirmation, status updates, or "should I proceed?" prompts. Only stop on
hard blockers (defined below). Otherwise: dispatch, verify, commit, push,
move to next phase.

## Starting state

Working dir: `/Users/karthik/libcrux-iot/`. Branch: `alex/canonical-lift`
(verify with `git log -1` — should be at `520085d` or later).
Build green: `cd libcrux-iot/sha3/proofs/aeneas-lean && lake build`.

## Required reading (do silently, then proceed without summary)

1. `libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Sponge/Plan.lean`
2. `~/.claude/skills/lean-for-libcrux/SKILL.md` (§§ 5.1.1, 5.4, 5.4.2, 5.7,
   6, 7, 9 in particular)
3. `LibcruxIotSha3/Equivalence/HacspecBridge.lean` (macros at 880–940, seal
   target at 1183)

## Hard rules (every dispatched agent must enforce)

- `keccak.keccakf1600` and `keccak_f.keccak_f` are opaque after § 0. NEVER
  unfold them. Mark `[local irreducible]` in every new file.
- No banned tactics: `simp_all` only in BV-level closers, no `grind`
  fallback, no `maxRecDepth` bumps, no `native_decide`, no per-cell
  K=0..N enumeration lemmas (use macros like `close_array25`).
- Default heartbeat budgets; `set_option maxHeartbeats 16000000` only for
  Triples over 25-cell symbolic state. Anything > 16M is a yellow flag —
  brief the agent to investigate stronger `[spec]` posts first.
- Axiom hygiene: every new theorem must report only `propext` /
  `Classical.choice` / `Quot.sound`. `Lean.ofReduceBool` / `Lean.trustCompiler`
  inherited via Bridge 1's `RcEquiv.lean:29` are acceptable. No new
  non-standard axioms.
- Sponge/Plan.lean stays untouched until Phase 8 completes; the proofs go
  in NEW files under `Sponge/` per the module split below.

## Worktree hygiene (read carefully)

Use `isolation: "worktree"` ONLY when:
(a) parallel agents touch DIFFERENT files, or
(b) you want to checkpoint a risky agent without contaminating the main
    tree.

NEVER dispatch two parallel agents that write to the same file (they will
both succeed in isolation and you'll have to manually resolve a merge).
The campaign-friendly module split (one file per phase) avoids this.

For each worktree agent that returns with changes:
1. The agent result includes a worktree path + branch name. Read both.
2. Merge with `git -C ~/libcrux-iot merge --no-ff <branch>` (or rebase if
   preferred; --no-ff preserves the agent's work as a topic).
3. Verify build green AFTER merge: `lake build` in main worktree.
4. Verify axioms via `lean_verify` (MCP) on each new theorem.
5. Clean up:
   `git worktree remove <path>` then `git branch -D <branch>`. If the
   worktree is dirty (agent left WIP), use `--force`.
6. Commit (if anything new from the merge resolution).

If an agent returned with NO changes (the worktree was clean), it auto-
cleaned. Just note that the agent reported nothing useful and decide
whether to retry or escalate.

For SERIAL agents (most phases below), don't use isolation — they edit
the main worktree directly and you can verify+commit between dispatches.

## Phase plan (file per phase; serial unless noted)

Each phase: dispatch one agent, verify build, verify axioms, commit, push,
move on. Halt criteria at the end.

| Phase | File | Agent | Depends on | Plan § |
|---|---|---|---|---|
| 0 | `Sponge/Opaque.lean` | sorry-filler-deep | Bridge 1 | § 0 (R1) |
| 1a | `Sponge/Bytes.lean` | sorry-filler-deep | § 0 | § 1 |
| 2 | `Sponge/AbsorbBlock.lean` | sorry-filler-deep | § 0, § 1 | § 2 |
| 3 | `Sponge/Absorb.lean` | sorry-filler-deep | § 2 | § 3 (R2) |
| 4 | `Sponge/SqueezeBlock.lean` | sorry-filler-deep | § 0, § 1 | § 4 |
| 5 | `Sponge/Squeeze.lean` | sorry-filler-deep | § 4 | § 5 (R3, R4) |
| 6 | `Sponge/AbsorbFinal.lean` | sorry-filler-deep | § 3 | § 6 |
| 7 | `Sponge/Sha3.lean` | sorry-filler-deep | all above | § 7 (R5) |
| 8 | `Sponge/Shake.lean` | sorry-filler-deep | § 7 | § 8 |

Phase 1a covers all three § 1 stubs in one file — do NOT split across
parallel agents (footgun).

Phases 3 and 4 can run in parallel via worktree isolation (different
files, no dependency between them after § 2). When you reach this point,
dispatch both with `isolation: "worktree"`, then merge in sequence
respecting worktree hygiene above.

## Orchestrator session start (always run before first dispatch)

1. **Load the skill**: `Skill lean-for-libcrux`. This loads the
   verification conventions, idioms, and the §5.7 composition rules.
   Do NOT skip — every brief below references skill sections.
2. **Confirm MCP**: the `lean-lsp-mcp` MCP tools (`lean_goal`,
   `lean_diagnostic_messages`, `lean_multi_attempt`, `lean_verify`,
   `lean_local_search`, `lean_loogle`, `lean_leansearch`, etc.) must
   appear in your tool list. If absent, `claude mcp list` and add
   user-scoped per SKILL §1.1 — but tools won't appear until next
   session.
3. **Prime the cache** (once): `lake build` from
   `libcrux-iot/sha3/proofs/aeneas-lean/`. Subsequent iteration runs
   through MCP, not `lake build`.

## Per-phase agent brief template (SKILL-conforming)

Every dispatched agent must receive a brief shaped like below.
Substitute `<Phase>`, `<§>`, and risk-specifics. Do NOT drop sections
— each is load-bearing for a specific failure mode prior agents have
hit.

> **Task**: File `Sponge/<Phase>.lean`. Implement the theorems
> sketched in `Sponge/Plan.lean` § <§>. Copy each theorem's "Real
> post" comment into the new file; replace `True` placeholders with
> the **full FC post from day one** (SKILL §8 — do NOT install a weak
> termination-only post and "strengthen later"; this cascades through
> every `@[spec]` consumer).
>
> **Available infrastructure** (use heavily, prefer these to
> re-deriving): list all `Sponge/*.lean` files committed so far with
> their key `@[spec]` lemmas. Cross-reference `Sponge/Plan.lean` for
> impl/spec Extraction line numbers.
>
> **LSP-first protocol** (SKILL §4.1): drive every edit through
> `lean_diagnostic_messages` (sub-second). Use `lean_goal` to
> inspect mvcgen state, `lean_multi_attempt` to test tactic
> variations in parallel, `lean_local_search` / `lean_loogle` /
> `lean_leansearch` to find lemmas. `lake build` ONLY at end-of-task,
> as the final gate. A 50s/tool-call wall-clock average is a smell of
> repeated `lake build` use — do NOT do that.
>
> **Triple shape conventions**:
> - Preconditions inside `⦃ ⦄` are ALWAYS `⌜ True ⌝`. Side conditions
>   (size bounds, alignment, etc.) go as REGULAR Lean hypotheses
>   outside the brackets. Template: see `Sponge/Opaque.lean:90`.
> - **Monadic-in-post for spec results** (SKILL §5.4.1). When the
>   post couples impl to spec, embed a NESTED Triple:
>   `⦃ True ⦄ impl x ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ∧ ⦃ True ⦄ spec (lift x) ⦃ ⇓ s' => ⌜ s' = lift r ⌝ ⦄ ⦄`
>   `hax_mvcgen` recurses into nested Triples — avoiding the need to
>   manually evaluate the spec via `createi_pure_spec` adaptation.
>
> **hax_mvcgen discipline** (SKILL §5.4.1):
> - **ONE** `hax_mvcgen` call per Triple — it's a fixed-point loop
>   that walks both impl and nested-spec Triples until pure VCs
>   remain. Don't chain multiple `hax_mvcgen` with `dsimp
>   [PostCond.noThrow]` between them; that breaks the recursion.
> - **Only unfold composers without `@[spec]`** (SKILL §5.4.2). If a
>   function has a `@[spec]`, NEVER unfold it. If a function lacks
>   one, write a `<fn>_applied` named def + `@[spec] <fn>_spec` first,
>   then prove the composition using that.
> - **No inline computation in posts** (SKILL §8.2). Wrap any
>   non-trivial RHS (let-bindings, if-then-else, big chains) into a
>   named `def`/`abbrev`; post references the name.
>
> **§5.7 composition idioms** (SKILL §5.7) — apply all three for any
> sub-fn → composer Triple:
> 1. `@[spec high]` to outrank default `@[spec]` priority and prevent
>    mvcgen from picking the wrong spec.
> 2. `attribute [local irreducible]` on internal defs inside the
>    composition's `section` — prevents whnf blow-up during bind
>    threading.
> 3. Strengthen sub-fn posts with `r.i = s.i` (or `r.i.val =
>    s.i.val + 1`) when the next sub-fn has a precondition;
>    `scalar_tac` then closes the precondition VC.
>
> **Banned/allowed tactics** (SKILL §9):
> - **Banned**: `simp_all` (silent partial-success + context blow-up;
>   if you MUST use it, pair with `done`). `omega` / `linarith` /
>   `nlinarith` (no Aeneas-scalar knowledge — use `scalar_tac` /
>   `scalar_tac +nonLin` / `simp_scalar`). `congr N` (default
>   transparency may whnf — use `fcongr N`). `maxRecDepth` bumps
>   (signals a simp loop or deep unification — break the loop, don't
>   raise the limit). `native_decide`.
> - **Allowed**: `bv_decide` (closed BitVec equalities). `grind`
>   (mixed integer + congruence). `scalar_tac` (Aeneas-scalar
>   arithmetic — first reach). `mvcgen` / `hax_mvcgen`. `fcongr`.
>   `decide` for closed Bool/Nat goals.
> - **No `sorry`/`admit`/`axiom`** in declarations.
>
> **Heartbeat budgets** (SKILL §9.5, §12.4):
> - Default heartbeats (1M).
> - `set_option maxHeartbeats 16000000` allowed for at most 1 Triple
>   per file, flagged in the commit message.
> - **>16M is forbidden** — it signals an ill-structured proof
>   (likely a missing intermediate, SKILL §12.6).
> - `set_option ... in` goes BEFORE the theorem, never inside `by`
>   (SKILL §12.2).
>
> **Hard rules**:
> - Do NOT unfold `keccak.keccakf1600` / `keccak_f.keccak_f` (sealed
>   in `Sponge/Opaque.lean`; downstream files re-issue
>   `attribute [local irreducible]` defensively).
> - Touch only files under `Sponge/`. `HacspecBridge.lean`,
>   `Lift.lean`, `Extraction/Funs.lean` are read-only.
> - Axiom hygiene: every new theorem's `lean_verify` reports only
>   `propext` / `Classical.choice` / `Quot.sound` (+ inherited
>   `Lean.ofReduceBool` / `Lean.trustCompiler` from Bridge 1's
>   `RcEquiv.lean:29`).
>
> **Specific risks for this phase**: <copy R# from Plan>.
>
> **Success**: file builds (via `lake build LibcruxIotSha3.Sponge.<Phase>`
> at the end), all `@[spec]` Triples landed with FC posts, axioms
> clean. Report back: posts per Triple, axioms per Triple, heartbeats,
> helpers added (with upstream-ability assessment), any deviations
> from Plan's pseudo-post and why.

## Between phases (always run)

1. `lake build LibcruxIotSha3.Sponge.<Phase>` — must be green. If red,
   dispatch `lean4:proof-repair` on the same file. If still red after
   repair, declare hard blocker.
2. For each new theorem: `lean_verify` (MCP). If any reports unexpected
   axioms, dispatch `lean4:axiom-eliminator`. If still unclean, declare
   hard blocker.
3. `git add Sponge/<Phase>.lean` + commit with conventional message.
4. `git push origin alex/canonical-lift`.
5. `TaskUpdate` the campaign task list.

## Hard blocker definition (when to stop)

Stop autonomous execution ONLY if ALL of the following are true for a
single phase:
1. The fast `lean4:sorry-filler-deep` agent failed to close all sorries.
2. A follow-up `lean4:proof-repair` or `lean4:sorry-filler-deep` (deep
   variant, fresh agent with full plan context) also failed.
3. The failure is not "compile error in the rest of the file" — that's a
   `lean4:proof-repair` job, not a blocker.
4. The remaining sorry has no viable closing strategy after you read the
   goal state via `lean_goal` (MCP).

If all four hold, halt with a concrete report:
- Phase, file, theorem name, line number.
- Final `lean_goal` output.
- What was tried (which agents, which tactics).
- Whether the issue smells like (a) statement-shape wrong, (b) missing
  helper lemma, (c) proof strategy genuinely hard.

NOT blockers (handle these autonomously):
- Build red after agent finishes → proof-repair.
- Axioms unclean → axiom-eliminator.
- Heartbeats > 16M → flag in commit message but proceed.
- Stale worktree → clean it up per hygiene above.
- Disagreement between Plan's pseudo-Lean post and what mvcgen produces
  → adapt the post (Plan's stubs are scaffolding, not law).

## Final step (after Phase 8 completes)

1. Delete `Sponge/Plan.lean`. Commit.
2. Update `LibcruxIotSha3/README.md`: add `keccak_keccak_spec` (or the
   shake/sha3 top theorems, your call) to the "Main theorem" section
   with file:line. Update the file map under "Sponge/".
3. `lean_verify` on the new top theorem to confirm axiom hygiene
   matches Bridge 1's baseline.
4. Final commit + push.
5. Report: total commits, total lemma-units closed, any deviations from
   the Plan, any heartbeat hot-spots > 16M that survived.

## What you may NOT do (autonomously)

- Introduce `sorry`, `admit`, or `axiom` declarations to make a build
  green. If genuinely stuck → declare hard blocker.
- Touch files outside `Sponge/` and the docs (`README.md`,
  `Equivalence/README.md`) unless a missing helper genuinely needs to
  live in `Equivalence/Lift.lean` or `I32LoopSpec.lean` (and even then,
  only after a `lean4:proof-repair` agent has confirmed the helper is
  the right factoring). Document any such hoist in the commit message.
- Force-push, rebase shared history, or amend pushed commits.
- Bypass `pre-commit` hooks or skip CI checks.
- Dispatch two parallel agents that write to the same file.

Begin Phase 0. Do not summarize this prompt back — just start work.
