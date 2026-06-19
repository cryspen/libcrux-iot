# ML-DSA NTT FC campaign — orchestration prompt

**Branch**: `iot-mldsa-proofs` (worktree `/Users/karthik/libcrux-iot-mldsa-proofs`).
**Target tree**: `libcrux-iot/ml-dsa/proofs/aeneas-lean/`.
**Goal**: prove the libcrux-iot ML-DSA Montgomery-domain SIMD NTT equivalent to
the clean `Z_q` (q = 8 380 417) hacspec, mirroring the completed ML-KEM tree.
**Method**: Plan-driven sub-agent dispatch (`lean-for-libcrux/SKILL.md §13`).

This file is the contract for the orchestrator. The phase catalog + FC posts +
sketches live in [`Plan.lean`](Plan.lean). The design rationale, the
ML-KEM↔ML-DSA delta, and the F*-derived precondition hints live in
`~/.claude/plans/encapsulated-waddling-panda.md`.

---

## Required reading before any dispatch

1. `~/.claude/skills/lean-for-libcrux/SKILL.md` — esp. §5.4/§5.7 (`hax_mvcgen`,
   composition idioms), §8.1 (FC quality), §9 (banned tactics), §13 (the whole
   methodology), §13.13 (cross-spec R-factor reconciliation).
2. `~/.claude/plans/encapsulated-waddling-panda.md` — this campaign's design.
3. `LibcruxIotMlDsa/Plan.lean` — the phase + target catalog.
4. The ML-KEM reference for the function/file being mirrored, e.g.
   `ml-kem/proofs/aeneas-lean/LibcruxIotMlKem/{Ntt,InvertNtt}.lean`,
   `.../Polynomial/PolyOpsFc.lean`, `.../Matrix/ComputeMessage/FC.lean`,
   `.../Spec/Lift.lean`.
5. Memory: `feedback_strong_postconditions`, `feedback_per_contract_pbt`,
   `feedback_no_sorry_increase_no_weakening`, `feedback_ledger_maintenance_discipline`.

## Phase order

**Phase 0** (extraction) is a hard prerequisite and is NOT a sorry-filler
dispatch — it is toolchain + scaffolding work the orchestrator does directly:

0.1 Align the hax/aeneas toolchain to `hax_aeneas.py`'s pins (`ffdf432…` /
    `8d2077c`); build aeneas from source if needed (ml-kem `README.md`).
0.2 Run `libcrux-iot/ml-dsa/hax_aeneas.py` → `Extraction/Funs.lean`.
    **Feasibility gate**: confirm aeneas monomorphizes the const-generic
    `outer_3_plus` / `shift_left_then_reduce` into usable defs. If it does not,
    STOP and report — the campaign's decomposition assumes per-layer defs exist.
0.3 Fill `Extraction/Missing.lean` from the first build's `libcrux_secrets`
    errors (i32-centric; adapt — don't copy — the ml-kem i16 list).
0.4 Port `Util/{SliceSpecs,LoopSpecs,CreateI}.lean` from ml-kem (re-point
    imports to `LibcruxIotMlDsa.Extraction.Funs` + the spec lib; rename
    namespace `libcrux_iot_ml_kem` → `libcrux_iot_ml_dsa`). Wire
    `portable_ops_inst`.
0.5 Re-enable the commented imports in `LibcruxIotMlDsa.lean`; `lake build`.

**Phases 1–8** then run bottom-up exactly as in `Plan.lean` (Spec → L0 → L1 →
L2/zeta → L3 drivers → pointwise/reduce → rounding → matrix). Phase 1 first
machine-validates `Spec/Pure.lean` (it is a hand-translation — `plausible` the
`intt (ntt p) = p` round-trip and `#eval`-cross-check vs the Rust spec BEFORE
any Triple depends on it; fix the spec if either fails — spec is mutable, impl
is not).

## Per-phase agent brief template (SKILL §13.2 — every clause load-bearing)

> **Task**: File `<phase file>`. Close the Triple(s) sketched in `Plan.lean`
> §<phase>. Copy each FC post verbatim; **full FC equality post from day one**
> (no bounds-only, no incremental weakening — §8.1).
>
> **Available infrastructure**: <prior committed files + their key `@[spec]`s,
> with line numbers>. Spec reference: `Spec.Pure.*`, lift: `Spec.Lift.*`.
> ML-KEM analogue to mirror: <path + theorem>.
>
> **LSP-first** (§4.1): drive edits via `lean_diagnostic_messages`; `lake build
> LibcruxIotMlDsa` only at end. >50s/tool-call avg ⇒ you're rebuilding — STOP.
>
> **Triple shape**: preconditions inside `⦃ ⦄` are `⌜ True ⌝`; side conditions
> (coefficient bounds) are regular hypotheses. Equality-form posts (§13.3). No
> inline computation in posts (§8.2) — wrap in named `Spec/Pure` defs.
>
> **R-factor discipline (§13.13)**: before proving any R-bearing equality,
> `#eval`/`#guard` the seam's factor on a computable proxy (the Rust spec or a
> small K-input). ⚠️ The upstream-libcrux F* bounds are HINTS — re-derive iot
> coefficient bounds empirically; do not copy them.
>
> **hax_mvcgen discipline** (§5.4.1–2): ONE call per Triple; unfold only
> composers without `@[spec]`; never unfold a function that has a `@[spec]`.
>
> **Banned tactics** (§9.1): no top-level `omega`/`linarith`/`nlinarith`, no
> `simp_all` without `done`, no `congr N≥2`, no `maxRecDepth` bump, no
> `native_decide` in a Triple, `maxHeartbeats ≤ 16M`. `omega` inside `have`
> blocks OK; `scalar_tac`/`bv_decide`/`grind`/`decide`/`fcongr` OK.
>
> **Axiom hygiene**: `#print axioms` = {propext, Classical.choice, Quot.sound}.
>
> **Touch only the current phase's file(s)**. `Extraction/*`, `Spec/Parameters`,
> `Spec/Montgomery` are read-only (the spec `Spec/Pure` may be refined ONLY in
> Phase 1 and ONLY with a `plausible`/`#eval` justification).
>
> **STOP** (§D.9): if a property is provably false (`plausible` counterexample,
> `#eval` mismatch, irreducible obstruction), STOP and report the concrete
> counterexample — do NOT weaken the post. A divergence is useful information.
>
> **LEDGER (mandatory, §13.12)**: end your report with one line:
> `LEDGER: <phase id> | tokens=<n> | tools=<n> | dur_s=<n> | result=<closed|repaired|failed|STOP|infra> | net_LOC=<±n> | sorry_delta=<±n> | axioms=<clean|custom>`

## Orchestrator loop (SKILL §13.10)

PROVER (`lean4:sorry-filler-deep`) → REVIEWER (`general-purpose` + `/lean4:review`,
the 10-point FC checklist) → decide: PASS (build + `#print axioms`, commit) /
PASS-WITH-NITS (orchestrator fixes ≤10 LOC) / CHANGES (dispatch
`lean4:proof-repair`, ≤2 attempts, else HALT with structured report).
**Append a ledger row after every dispatch and every REVIEWER pass** — before
any commit. Keystone (first proof of a pattern) bears the infra cost; reuse
proofs are 3–5× cheaper (size the budget accordingly).

## Hard rules carried from ML-KEM

- No-sorry-increase / no-statement-weakening on every PROVER return: verify
  sorry count (build-based, §9.7 — never `grep -c sorry`) and locked-statement
  byte-equality.
- Mathlib confined to `Util/` + `Spec/` barrier; above-barrier files add no new
  Mathlib imports.
- `set_option … in <theorem>` only (never inside a `by` block).
- Final step of the campaign: delete `Plan.lean`, write the tree `README.md`
  (mirror ml-kem's), record the trust boundary (any leaf axioms for matrix-level
  sampling, analogous to ML-KEM's A1/A2).
