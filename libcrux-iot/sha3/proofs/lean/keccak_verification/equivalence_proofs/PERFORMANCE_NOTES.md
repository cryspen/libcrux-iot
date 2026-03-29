# Performance Observations (Working Document)

Observations from spec_decomp optimization session. Not prescriptive — many approaches
are hypotheses that need further validation.

## What we measured

| Approach | Time | Memory | Outcome |
|----------|------|--------|---------|
| Monolithic spec_prc proof (3 stacked createi + 25-branch match) | 657s | 1.3GB | Kernel deep recursion in lake build |
| Compositional sub-lemmas (rho/pi/chi/iota_ofFn) + simp chain | 9.2s | 1.3GB | Passes |
| `rfl` on Vector.ofFn vs #v[...] (25 elements) | 648s | - | Kernel unfolds everything |
| `congr 1` on RustArray/Vector | 103s | - | Deep whnf |
| Match-free createi with usize_* lemmas | Fast (per-lemma) | Low | Passes |
| `unfold` compact def in downstream (Vector.ofFn form) | 448s/OOM | 9GB | Downstream breaks |
| `unfold` concrete def in downstream (let-binding form) | 471s | 1.8GB | Works (pre-existing slow) |

## Open questions

1. **Would `native_decide` close the bridge lemmas?** We never tried `native_decide` on
   `spec_prc_compact_eq_unrolled`. It might produce a small proof term.

2. **Is the 25-branch match inherently slow?** In rho_ofFn (which passes), we use match-free.
   But the theta Vector.ext closer uses a 25-branch match and works in LSP. The kernel depth
   issue may only arise when multiple matches stack.

3. **Can `bv_decide` handle USize64 arithmetic?** It didn't work on `.toNat` goals, but
   might work if we stay in BitVec representation throughout.

4. **Why does `Vector.ext` fail in context but work in isolation?** The `apply Vector.ext`
   failed after `apply congrArg` in the theta proof but worked in `lean_run_code`. The
   issue might be RustArray wrapping or proof term structure.

5. **Could a custom tactic systematize the usize arithmetic chain?** The current `have` +
   `rw [usize_toNat_*]` + `omega` chain is verbose. A tactic that automates:
   unfold checked ops → discharge overflow → distribute toNat → omega
   would simplify all createi proofs.

6. **Is loop unrolling (25 iterations) a fundamental cost?** theta_lift takes 471s even with
   the old concrete definition. Is this from the algebraic bridge (25 lanes × lift lemmas)?
   Could it be decomposed similarly?

7. **LSP vs lake build divergence**: simp_all closes different goals, rfl takes different time.
   Root cause unclear — could be stack size, kernel settings, or elaboration order.

## What works well

- **Compositional sub-lemmas**: 70x speedup for spec_decomp
- **`set_option profiler true`**: identified the exact 648s bottleneck
- **usize arithmetic lemmas**: eliminate case splits for checked arithmetic
- **`USize64.reduceToNat`**: reduces literal `.toNat` without manual `show`
- **Separate compact vs concrete definitions**: keeps both fast proofs and downstream compat

## What needs improvement

- Bridge lemmas (Vector.ofFn vs #v) still sorry'd
- theta_lift 471s — needs investigation
- USize64 arithmetic chain is verbose (10+ `have` per createi proof)
- No systematic way to handle `dite` bounds for array access
