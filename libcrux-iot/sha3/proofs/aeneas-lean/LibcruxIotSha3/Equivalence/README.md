# SHA-3 Keccak-f[1600] Impl ↔ Spec Equivalence (Lean 4 / Aeneas-Lean)

This directory contains the Lean 4 proof that the bit-interleaved
implementation of Keccak-f[1600] in `libcrux-iot/sha3/src/` computes
the same function as the Hacspec-style spec in `specs/sha3/src/`.

Both sides are auto-extracted to Lean 4 via the
[hax → aeneas → aeneas-lean](https://github.com/AeneasVerif/aeneas)
pipeline; we then prove their equivalence at the level of the
permutation Keccak-f[1600] under the `Std.Do.Triple` Hoare-logic
framework.

## What's being proven

At the Keccak level, both sides compute the standard FIPS-202
permutation Keccak-f[1600] on a 1600-bit state. The two sides differ
in *representation*:

- **Spec.** 25 lanes of `u64`, organized as `state[5*x + y] = A[x, y]`
  in row-major form. Each round is `ι ∘ χ ∘ π ∘ ρ ∘ θ` applied to the
  full 64-bit lanes. 24 rounds; round constants from FIPS-202.

- **Implementation.** 25 lanes, each split into a pair of 32-bit
  halves `(z0, z1)` in *bit-interleaved* form: `z0` holds the bits at
  even positions (0, 2, …, 62) and `z1` holds the bits at odd positions
  (1, 3, …, 63) of the 64-bit lane. This representation lets the impl
  replace 64-bit rotations (often unavailable on 32-bit targets like
  Cortex-M4) with at most two 32-bit rotations plus a half-swap on odd
  offsets. The impl also maintains scratch arrays `c[5]` and `d[5]` of
  interleaved 32-bit halves used by θ, and an in-progress round
  counter `i : usize`.

  Each round in the impl is split into 11 θ sub-functions
  (`theta_c_x{0..4}_z{0,1}` and `theta_d`), a `pi_rho_chi_1` (handles
  rows y=0,1 plus the ι constant XOR), and a `pi_rho_chi_2` (rows
  y=2,3,4). The π step is implemented as a *storage relabeling* — each
  round reads lanes from different physical positions — so after one
  round the canonical `5*x + y` mapping no longer holds. The
  relabeling has order 4 (`impl_perm⁴ = id`), so every 4 rounds the
  layout re-aligns with the spec. The full 24 rounds factor as 6
  bundles of 4 rounds each.

The bridge between the two representations is the function
`lift : KeccakState → Array u64 25` defined in `Lift.lean`:

```
(lift s)[i] = lift_lane_bv s.st[i].z0 s.st[i].z1
            = bitwise interleave of (z0, z1) into a u64
```

The **top-level equivalence theorem** (target: `Top.lean`) will read,
in informal form:

> For every initial state `s : KeccakState`, after running 24 rounds
> of the implementation, the lifted result equals the spec's 24-round
> Keccak-f[1600] applied to `lift s`:
>
>     keccakf1600 s = ok r_impl  →
>     keccak_f.keccakf1600 (lift s) = ok r_spec  →
>     r_spec = lift r_impl.

## Status (2026-05-21)

All files in this directory are complete with **0 sorries**.

| File | Role |
|---|---|
| `Lift.lean` | Interleaved-lane lifting (`lift_lane_bv`, `lift`, `lift_perm`, `impl_perm`, `impl_swap`, `impl_swap_k` 4-cycle) + bv_decide-closed algebra (25 `rot_N` + `lift_xor`/`lift_and`/`lift_not`/`lift_chi`/`lift_theta_apply`/`lift_td`/`lift_rot1`/`lift_xor5`). |
| `UScalarAC.lean` | Tier 1.5 local `Std.Associative`/`Std.Commutative` instances on `Std.UScalar.xor`/`and`/`or` (Aeneas surface fill). |
| `RcEquiv.lean` | `rc_equiv` for `i < 24` via `native_decide` (the only `native_decide` site in the tree). |
| `SpecChain.lean` | `spec_round_step` + `spec_chain` (`Nat.fold` wrapper) over the four `_unrolled` spec functions. |
| `I32LoopSpec.lean` | I32 iterator + `loop_range_spec_i32` (used by StructEquiv's 6-iteration loop spec). |
| `ThetaLiftDefs.lean` | 11 round-0 θ sub-fn `@[spec]`s + `theta_comp_spec_local` + `lift_theta_applied(_perm)` defs + reusable `theta_c_proof` macro. |
| `ThetaLift.lean` | Round-0 `theta_lift_spec` (algebraic close via `simp only [Std.UScalarTy.U64_numBits_eq, ← lift_xor, ← lift_td]`). |
| `ThetaLiftRound{1,2,3}.lean` | Round-k θ sub-fn `@[spec]`s + 25 `lta_perm_bv_*_k` input lemmas + `theta_lift_spec_k`. |
| `PrcLift.lean` | 10 round-0 πρχι sub-fn `@[spec]`s + `prc_y_zeta_no_rc_proof` macro + `prc_lift_spec` (round 0). |
| `PrcLiftRound{1,2,3}.lean` | Round-k πρχι sub-fn `@[spec]`s + 25 input lemmas + `prc_lift_spec_k`. |
| `StepSpecs.lean` | Round 1–3 step preservation specs (82 declarations via one `step_preserve_proof` macro). |
| `RoundEquiv.lean` | `round_k_equiv_spec` for k=0,1,2,3 + per-round i-increment lemmas + chain wrappers. |
| `Keccakf1600.lean` | `keccakf1600_post` / `keccakf1600_post_canonical` (the public post shapes). |
| `HacspecBridge.lean` | Bridge 1 — couples impl to hacspec top-level `keccak_f.keccak_f` via `createi_pure_spec`, 6 per-closure `[spec]` Triples (θ×3, ρ/π/χ), 4 function equalities `keccak_f.X = keccak_f.X_unrolled`, `spec_chain_hacspec_eq_spec_chain`, `Usize` iterator/loop specs, `keccak_f_loop_eq_spec_chain_hacspec`, and the top theorem `keccakf1600_equiv_hacspec`. |

```bash
grep -rn sorry libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Equivalence/
# (no output)
```

Build cost: `lake build` from the project root takes ~2 minutes from
clean; per-file `lake env lean LibcruxIotSha3/Equivalence/<file>.lean`
ranges from 1.8 s (`RcEquiv`) to 75 s (`StepSpecs`).

## Layout

```
LibcruxIotSha3/Equivalence/
├── Lift.lean              Bit-interleaved → u64 lifting (defs + bv_decide algebra)
├── UScalarAC.lean         Local Std.Associative/Commutative on Std.UScalar.xor/and/or
├── RcEquiv.lean           lift_lane_bv RC_INTERLEAVED_{0,1}[i] = ROUND_CONSTANTS[i]
├── SpecChain.lean         spec_round_step + spec_chain over _unrolled spec functions
├── I32LoopSpec.lean       I32 iterator + loop_range_spec_i32
├── ThetaLiftDefs.lean     Round-0 θ sub-fn @[spec]s + theta_comp_spec_local + lift_theta_applied(_perm)
├── ThetaLift.lean         Round-0 theta_lift_spec (spec-coupling algebraic close)
├── ThetaLiftRound1.lean   Round-1 θ analog
├── ThetaLiftRound2.lean   Round-2 θ analog
├── ThetaLiftRound3.lean   Round-3 θ analog
├── PrcLift.lean           Round-0 πρχι sub-fn @[spec]s + prc_lift_spec
├── PrcLiftRound1.lean     Round-1 πρχι analog
├── PrcLiftRound2.lean     Round-2 πρχι analog
├── PrcLiftRound3.lean     Round-3 πρχι analog
├── StepSpecs.lean         Preservation specs for rounds 1, 2, 3 (rounds 0 in Theta/PrcLift)
├── RoundEquiv.lean        round_k_equiv_spec for k=0..3 + i-increment + chain wrappers
├── Keccakf1600.lean       keccakf1600_post / keccakf1600_post_canonical
└── HacspecBridge.lean     Bridge 1: hacspec coupling + keccakf1600_equiv_hacspec
```

Each file uses the established Hax `Std.Do.Triple` idiom:

1. **Primitive `@[spec]` lemmas** for the low-level operations
   (`set_lane_value`, `get_with_zeta`, `lane_index`, `rotate_left_u32`,
   `set_with_zeta`).
2. **Per-sub-function `preserves_*` lemmas** via a tactic macro
   (`theta_sub_preserves_st_i_proof`, `prc_sub_preserves_proof`,
   `step_preserve_proof`) that unfolds and chains the primitives
   through `hax_mvcgen` + `grind`/`scalar_tac`.
3. **Composed top-level lemma** (`theta_comp_spec_local`,
   `pi_rho_chi_{1,2}_spec_local`) whose post-condition characterises
   the impl's new auxiliary cells (`r.d`) or guarantees the absence of
   changes (`r.st = s.st`, `r.i = s.i + 1`).

## Pipeline diagram

```
                                     +---------------------------+
   libcrux-iot/sha3/src/  ---------> | hax (cargo hax)           |
   (Rust + #[hax_lib::*])            +---------------------------+
                                                 |
                                                 v
                                     +---------------------------+
                                     | aeneas -core-models-lib   |
                                     +---------------------------+
                                                 |
                                                 v
                          LibcruxIotSha3/Extraction/Funs.lean
                                                 +
                          LibcruxIotSha3/Equivalence/*.lean  <--  this dir

   specs/sha3/src/        ---------> hax → aeneas → HacspecSha3/Extraction/Funs.lean
                                          (re-extracted at commit 6fff45b
                                           via SKIP_VERSION_CHECK=1 against
                                           aeneas b5c45e84 / charon v0.1.184)
```

## How to run the proofs

### Prerequisites

- Lean 4 toolchain `leanprover/lean4:v4.28.0-rc1`
  (pinned in `lean-toolchain`).
- Aeneas at commit `b5c45e84` if you intend to re-extract; not
  needed to *check* the existing `.lean` files.

### Quick check (single file)

From `libcrux-iot/sha3/proofs/aeneas-lean/`:

```bash
lake exe cache get                                    # one-time prime
lake build                                            # full tree
# or per-file (faster feedback):
lake env lean LibcruxIotSha3/Equivalence/<File>.lean
```

A clean `lake build` should exit 0 with at most cosmetic warnings
(unused-tactic linter on a few `(try trivial)` calls in
`StepSpecs.lean`).

### Sorry-hygiene check

```bash
grep -rn sorry libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Equivalence/
```

This must remain empty.

### Cross-spec regression (Rust)

Before any Lean iteration that depends on a re-extraction, run from
`libcrux-iot/sha3/`:

```bash
cargo test --lib cross_spec --tests
```

This catches lane-layout / round-constant / endianness mismatches at
the Rust level, before they propagate into Lean proof failures.

### Re-extraction (only if you edit the Rust source)

```bash
# Spec side:
cd specs/sha3/
SKIP_VERSION_CHECK=1 ./hax_aeneas.py

# Impl side:
cd libcrux-iot/sha3/
SKIP_VERSION_CHECK=1 ./hax_aeneas.py
```

`SKIP_VERSION_CHECK=1` is needed because the installed `cargo-hax` is
ahead of the `HAX_VERSION` pin in `hax_aeneas.py`; the aeneas binary
must report `aeneas b5c45e84`.

## Iteration tips

- Use the `lean-lsp-mcp` MCP server for sub-second feedback while
  editing — see `~/.claude/skills/lean-for-libcrux/SKILL.md`. `lake
  env lean <file>` is the right gate for individual file checks; full
  `lake build` is reserved for end-of-task validation.
- Mark `spread_to_even` and `lift_lane_bv` `@[local irreducible]` at
  the top of any file that does post-mvcgen reasoning — every `simp`
  call otherwise unfolds them into a six-step parallel-bit-deposit
  cascade × 25 lanes, blowing up term sizes by orders of magnitude.
- All "lift commutes with op" lemmas (second half of `Lift.lean`) close by
  `unfold lift_lane_bv spread_to_even; bv_decide` — the SAT solver
  dispatches them in seconds.
- For U32 equalities arising from post-mvcgen residuals, the standard
  chain is `apply Std.U32.bv_eq_imp_eq; simp_all [Std.UScalar.bv_xor]`
  to reduce to a closed BitVec equation, then either `rfl` or
  `bv_decide`.

## See also

- `../Extraction/Funs.lean` — the impl extraction (generated; do not
  hand-edit).
- `../../../specs/sha3/proofs/aeneas-lean/HacspecSha3/Extraction/Funs.lean`
  — the spec extraction (generated).
