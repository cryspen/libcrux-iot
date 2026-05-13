# Reproducing the SHA-3 equivalence proof state

If you want to inspect the proof tree + investigate the open
`theta_lift_spec` blocker described in
[`HAX_AENEAS_PITFALLS.md`](./HAX_AENEAS_PITFALLS.md), this is what you
need.

## TL;DR

```sh
git clone git@github.com:cryspen/libcrux-iot.git
cd libcrux-iot
git checkout alex/verification
cd libcrux-iot/sha3/proofs/aeneas-lean
lake exe cache get
lake build
```

Then `LibcruxIotSha3/Equivalence/ThetaLift.lean:585` is the one remaining
`sorry` — the load-bearing algebraic-fold step (section L6 of the
pitfalls doc).

## What you need

### Lean toolchain

- `leanprover/lean4:v4.28.0-rc1` (pinned in `lean-toolchain`).
- `lake` (ships with Lean).

### Repository pins

The lakefile/manifest pins are:

| Pin                              | Resolved commit                                              | GitHub URL                                                                                                | Public? |
| -------------------------------- | ------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------- | ------- |
| `cryspen/libcrux-iot`            | branch `alex/verification` (latest: `31de111` or newer)      | https://github.com/cryspen/libcrux-iot                                                                    | ✅      |
| `cryspen/rust-core-models`       | `b67ccf195ab8a10ecd0bed465a1539931418ac19`                   | https://github.com/cryspen/rust-core-models                                                               | ✅      |
| `cryspen/hax-evit` (the `Hax` lib) | `7b4bd97058e0fcbf9135b76297ca91942f2327a6`                 | https://github.com/cryspen/hax-evit  (private)                                                            | ❌      |
| `abentkamp/aeneas` (Lean backend) | `4e02d6d8e1421562e6ab4a9737fae159ba602d8b`                  | https://github.com/abentkamp/aeneas                                                                       | ✅      |
| `leanprover-community/batteries` | `cabbb5a025bfbbc50af9184ed2dfdde6ea4f53a7`                   | standard                                                                                                  | ✅      |
| `leanprover/lean4-cli`           | `28e0856d4424863a85b18f38868c5420c55f9bae`                   | standard                                                                                                  | ✅      |

**The `cryspen/hax-evit` repo is private** — `lake build` will fail at
the dependency-fetch step if you don't have GitHub read access to that
repo.  The commit IS pushed (it's on `origin/new-examples` in
`hax-evit`); the access control is the only barrier.

### Iteration workflow

`lake build` does a full re-check (30–120 s).  For authoring iteration,
use the Lean LSP — any of:

- **Standard editor integrations**: VS Code (`lean4` extension), Emacs
  (`lean4-mode`), Neovim (`lean.nvim`).  These give sub-second
  re-check.
- **Headless LSP via MCP**: `uvx lean-lsp-mcp` (used by the
  Claude-Code `lean4-skills` plugin / Cursor / similar).

Avoid relying on `lake env lean File.lean` for iteration — it
re-compiles dependencies each call (8–75 s).

### Optional: no aeneas binary needed for proof investigation

The `.lean` files (impl extraction `LibcruxIotSha3/Extraction/Funs.lean`,
spec extraction `HacspecSha3/Extraction/Funs.lean`, the equivalence
proofs themselves) are all committed.  You don't need to re-run the
hax → aeneas-lean extraction unless you want to modify the Rust source.

If you DO want to re-extract, you need:
- aeneas binary at commit `b5c45e84` (PR #969 of `AeneasVerif/aeneas`).
- cargo-hax at `ee467e6ac3...` (`hax-evit` HEAD or compatible).
- charon at `ed22146b1cd4d0b578006a58b3299d41ecbe0fd4`.
- macOS users: Homebrew `gmake` (system `make 3.81` is rejected).

See section T1 of `HAX_AENEAS_PITFALLS.md` for the install dance.

## How to investigate the `theta_lift_spec` blocker

The single `sorry` in `LibcruxIotSha3/Equivalence/ThetaLift.lean` is at
line 585.  The proof up to that point:

1. Applies `Triple.bind` to separate impl and spec sides.
2. Closes the impl side via `theta_comp_spec_local` (which gives the
   12-conjunct d-content postcondition).
3. Runs `hax_mvcgen` on the spec-side `theta_unrolled`, leaving a
   25-lane "Array literal = lift_theta_applied r_impl" residual.
4. Destructures the 12-conjunct, applies `Subtype.ext`, unfolds
   `lift_theta_applied`, substitutes d-cells.
5. Peels into 25 lane goals via `List.cons_eq_cons.mpr`.
6. Applies `Std.U64.bv_eq_imp_eq` to each, producing 25 BitVec
   equations.
7. `simp_all only [...]` (step a) collapses the spec-side chain +
   normalises `(N#usize).val → N`.
8. `simp only [lift_getElem_bv_0 ... lift_getElem_bv_24]` (step b)
   converts each `(↑(lift s))[N]!.bv` to
   `lift_lane_bv (s.st.val[N]!.val[0]!.bv) (s.st.val[N]!.val[1]!.bv)`.
9. **THE BLOCKER (L6)**: the final `simp only [← lift_xor, ← lift_td,
   ← lift_rot1]` should fold the LL-tower on the LHS into the single
   `lift_lane_bv` on the RHS.  It doesn't fire.  A standalone
   `lean_run_code` reproducer (no surrounding hypotheses) with the
   exact same surface goal closes via the same simp set.

The proof scaffolding (literal-list `lift_theta_applied`, 25
`lift_getElem_bv_N` helpers in the exact form
`((↑(lift s) : List Std.U64)[(N : Nat)]!).bv`, the 12-conjunct
destructure, the 25-way `congr 1` peel) is committed and verified to
land cleanly up to that one step.

A successful diagnosis of L6 would:
- Either confirm/refute the "reducibility-aware simp matcher" hypothesis,
- And/or provide a tactic recipe that DOES close the goal in the
  in-proof context.

## Open questions for external investigators

If you don't have access to `cryspen/hax-evit`, you can still
investigate L6 with a self-contained reproducer.  The key file is
[`LibcruxIotSha3/Equivalence/ThetaLift.lean`](./LibcruxIotSha3/Equivalence/ThetaLift.lean)
— the `theta_lift_spec` theorem at line 583, with the sorry at line
585 and the algebraic-close scaffold in step (b) at lines 670–679.

The standalone reproducer that DOES close (no Hax dependency) is:

```lean
import Std.Tactic.BVDecide

-- Inline lift_lane_bv and the lifting lemmas
def spread_to_even (x : BitVec 32) : BitVec 64 :=
  let x : BitVec 64 := x.zeroExtend 64
  let x := (x ||| (x <<< 16)) &&& 0x0000ffff0000ffff#64
  let x := (x ||| (x <<<  8)) &&& 0x00ff00ff00ff00ff#64
  let x := (x ||| (x <<<  4)) &&& 0x0f0f0f0f0f0f0f0f#64
  let x := (x ||| (x <<<  2)) &&& 0x3333333333333333#64
  let x := (x ||| (x <<<  1)) &&& 0x5555555555555555#64
  x

def lift_lane_bv (z0 z1 : BitVec 32) : BitVec 64 :=
  spread_to_even z0 ||| (spread_to_even z1 <<< 1)

theorem lift_xor (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) =
    lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

theorem lift_td (cL0 cL1 cR0 cR1 : BitVec 32) :
    lift_lane_bv (cL0 ^^^ cR1.rotateLeft 1) (cL1 ^^^ cR0) =
    lift_lane_bv cL0 cL1 ^^^ (lift_lane_bv cR0 cR1).rotateLeft 1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

attribute [local irreducible] spread_to_even lift_lane_bv

-- The reproducer goal (same shape as one lane of the actual proof)
example (a b c d e f : BitVec 32) (g h i j k l : BitVec 32) :
    lift_lane_bv a b ^^^ (lift_lane_bv c d ^^^ (lift_lane_bv e f).rotateLeft 1) =
    lift_lane_bv (a ^^^ (c ^^^ f.rotateLeft 1)) (b ^^^ (d ^^^ e)) := by
  simp only [← lift_xor, ← lift_td]  -- closes here, doesn't close in proof
```

The mystery: why does this `simp only` close the standalone goal but
not the in-proof goal of the same shape?
