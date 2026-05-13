# Pitfalls hit while writing equivalence proofs in hax → aeneas-lean → Hax Triple

Notes for the hax / aeneas-lean / Hax-tactics designers, collected from
proving 12-conjunct postconditions + spec-coupling Triple lemmas for the
SHA-3 θ / πρχι steps of `libcrux-iot/sha3` against the `hacspec_sha3`
spec.  Most of these cost hours of diagnostic time; some are still
unresolved.  The verification context:

- Rust impl `keccakf1600_round0_*` (interleaved-32 lanes, 11–13 sub-funcs
  per step) lifted through `cargo hax into aeneas-lean`.
- Spec `keccak_f.theta_unrolled` / `pi_unrolled` / `chi_unrolled` /
  `rho_unrolled` / `iota` (straight-line monadic Result form, 25-cell
  `Array Std.U64 25#usize`).
- Proofs in Hax Triple style: `⦃ pre ⌝ ⦄ m ⦃ ⇓ r => ⌜ post r ⌝ ⦄`,
  closed via `hax_mvcgen` + `@[spec]` chaining + post-mvcgen algebra.
- Tree: `libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Equivalence/`.

## A. Surface-syntax ≠ underlying term (the biggest time sink)

The Lean pretty-printer routinely inserts `↑` casts that hide which
underlying GetElem instance / coercion was actually picked.  Two
expressions that print identically may use **different** GetElem?
instances and therefore fail simp/rw unification.

### A.1  `↑(lift s)[↑N#usize]!.bv` has three valid elaborations

For `lift s : Std.Array Std.U64 25#usize`:

| As-typed                                                     | Underlying term                                                                                                                                  |
| ------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------ |
| `(↑(lift s))[↑0#usize]!.bv`                                  | `Aeneas.Std.instGetElem?ArrayUsizeLtNatValLengthValListEq` (Array+Usize) on `lift s` with index `0#usize`                                        |
| `((lift s).val[0]!).bv`                                      | `List.instGetElem?NatLtLength` (List+Nat) on `(lift s).val` with literal `0`                                                                     |
| `((↑(lift s) : List Std.U64)[(0 : Nat)]!).bv`                | Same as row 2 but elaborated via the explicit ascription                                                                                         |
| `(((↑(lift s) : List Std.U64))[(↑(0#usize) : Nat)]!).bv`     | List+Nat with index `(0#usize).val`                                                                                                              |

All four pretty-print as `(↑(lift s))[↑0#usize]!.bv`.  Writing a simp
lemma in one form and a goal in another fails to unify.  The diagnostic
requires `set_option pp.all true` which produces 200-line terms.

**Suggestion:**  the pp coercion arrows should disambiguate via a
distinctive marker (e.g. `↑ₐ` vs `↑ₗ`) or `pp.coercions.types` should be
on by default for `GetElem?` arguments in user-facing surface display.

### A.2  Bound-proof discrimination in `Std.Usize.ofNat N _`

`0#usize` desugars to `Aeneas.Std.Usize.ofNat 0 (proof : 0 ≤ ...)`.  Two
occurrences of `0#usize` in the same file can have proof-irrelevantly
equal but syntactically distinct bound proofs (e.g. one via
`of_decide_eq_true ... refl`, another via a different witness produced
by `hax_mvcgen`).  `rw` and `simp only` then refuse to unify.

**Suggestion:** mark the bound parameter of `Std.UScalar.ofNat` as
proof-irrelevant via `Decidable.rec`-style or add a `@[simp]`
canonicalisation lemma `Usize.ofNat_irrelevant` that rewrites any
bound-proof to a canonical one.

### A.3  `Subtype.val ≠ ↑` syntactically

`↑(lift s)` for `lift s : Std.Array Std.U64 25` elaborates to
`@Subtype.val (List Std.U64) (fun l => l.length = 25) (lift s)` which
is definitionally `(lift s).val`.  But:

- A lemma stated with `(lift s).val[0]!` has LHS pattern using
  `Subtype.val ... (lift s)`.
- The same access written as `↑(lift s)[0]!` may elaborate via the
  `Coe` instance, producing a different head symbol in some contexts.

These four hours of fight could have been avoided if there were a
single canonical pp form for "underlying list of a `Std.Array`".

## B. `(N#usize).val` does not reduce automatically

After `Array.index_usize_spec` (an `@[step]` lemma with postcondition
`x = v.val[i.val]!`), the index appears as `(N#usize).val` (Nat).  This
is definitionally `N` (the Nat literal) but `simp only` doesn't reduce
it.

I had to add 25 explicit rewrites to my simp set:

```lean
show ((0#usize : Std.Usize).val) = 0 from rfl,
show ((1#usize : Std.Usize).val) = 1 from rfl,
...
show ((24#usize : Std.Usize).val) = 24 from rfl
```

before my `lift_getElem_bv_N` helpers (with Nat-literal indices) could
fire.

**Suggestion:** add `@[simp] theorem Usize.val_ofNat_lit (n : Nat) (h) :
((Std.Usize.ofNat n h).val) = n := rfl` or a `simp norm_num` extension
that reduces these literal-index `.val` calls.

## C. Multiple GetElem instances on the same container

`Std.Array α n` has FOUR active `GetElem?` instances simultaneously:

1. `Array + Usize → α` (the "natural" indexing for Rust-style arrays)
2. `Array + Nat → α` (for proof convenience)
3. `List + Nat → α` (after `.val` projection)
4. `List + Usize → α` (after `.val` and via Usize coercion)

A spec function written by hand often uses (1) or (4); `hax_mvcgen`
+ `Array.index_usize_spec` produces (3) in residual goals.  Lemmas
written by hand often default to (3) but appear to be (1) due to pp
coercions (see A.1).

**Suggestion:** pick ONE canonical form for the impl/spec equivalence
proof surface — preferably (1) (Array + Usize) since that's what the
Rust source uses — and provide universal `@[simp]` rewrites that
canonicalise the others to it.

## D. `simp_all only` doesn't propagate conjunctions in hypotheses

After `hax_mvcgen` on `theta_unrolled`, the spec-side chain produces
~75 anonymous hypotheses like:

```
h✝ : ↑r✝ = ↑(r✝¹ ^^^ r✝²) ∧ r✝.bv = r✝¹.bv ^^^ r✝².bv
```

`simp_all only [...]` treats the whole conjunction as one hypothesis
and never splits it.  The `.bv = ...` part is the useful rewrite rule,
but it's stuck behind the `∧`.

`obtain ⟨_, h⟩ := h✝` doesn't work because the hypothesis is anonymous
and `simp_all` may already have rewritten earlier copies.

**Suggestion:** `hax_mvcgen` should split the postcondition conjunction
in each chain step into separate hypotheses, OR provide a `simp_all`
configuration that auto-splits And/Iff hypotheses.

## E. `Fin.foldr` / `List.ofFn` in `lift_theta_applied` blocked unfolding

Defining the 25-lane lifted array via `List.ofFn (fun i : Fin 25 => ...)`
seemed natural:

```lean
def lift_theta_applied (s : KeccakState) : Array U64 25#usize :=
  ⟨List.ofFn (fun i : Fin 25 => ⟨lift_lane_bv ...⟩), by simp⟩
```

But after `unfold lift_theta_applied`, the RHS is `(List.ofFn _)[k]!`
which simp couldn't unfold to a literal 25-element list — every
`List.ofFn` index involved `Fin.succ.succ.succ...` chains 25 deep that
exhausted `maxRecDepth = 2000`.

I had to rewrite as a literal `Array.make 25#usize [..., ..., ...]`
with 25 explicit entries.  Cost: ~150 lines of boilerplate.

**Suggestion:** `Array.make` should be the canonical "build an n-array
from a list" form, and the aeneas-lean tutorial should warn against
`List.ofFn` for proof-friendly definitions.

## F. `lift_lane_bv` irreducibility interferes with `simp` matching of forward lifting lemmas

`spread_to_even` and `lift_lane_bv` are marked `@[local irreducible]`
in `ThetaLift.lean` (to prevent the 6-step parallel-bit-deposit
expansion from blowing up).  This is **required** — without it term
sizes go from ~5000 nodes to ~100,000 nodes per goal, and `lake build`
goes from 4s to OOM.

But after step (a) `simp_all only [chain]` exposes both sides as
towers of `lift_lane_bv` calls, the forward direction simp lemmas
(`lift_xor`, `lift_xor5`, `lift_td`, `lift_rot1`) fail to fire even
though they SHOULD match by pure syntactic pattern matching:

- `lift_xor` pattern: `lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1)`
- Goal RHS: `lift_lane_bv (X ^^^ Y) (Z ^^^ W)` (concrete BV expressions)

In a **standalone reproducer** (no surrounding hypotheses) the same
simp call closes the goal.  In the actual proof context it doesn't —
even after extensive form-canonicalisation work.

**Hypothesis:** simp's matcher may be doing "reducibility-aware"
matching that gives up when the head symbol is irreducible AND the
goal has a different surface-tree-of-coercions than the lemma.  This
is the load-bearing unresolved blocker for `theta_lift_spec`.

**Suggestion:** document the exact reducibility-vs-matching interaction
in the Hax tactic guide, OR provide a `simp_norm` config that
canonicalises BitVec/UScalar expressions before pattern matching.

## G. `@[step]` vs `@[spec]` distinction

`Aeneas.Std.Array.index_usize_spec` is `@[step]`-tagged.  My
hand-written specs are `@[spec]`-tagged.  Both produce postconditions
for `hax_mvcgen` to chain through.  But:

- `@[step]` lemmas don't take a custom `Q` parameter — the post is fixed
  in the lemma statement.
- `@[spec]` lemmas take `{Q}` and an `hpost : ... → (Q.1 r).down`
  hypothesis that mvcgen instantiates.

The choice matters for compositionality.  I had to convert several
`@[step]` specs to `@[spec]` form to thread strengthened postconditions
through the πρχι chain.  The conversion pattern is mechanical:

```lean
-- @[step] form (rigid post):
theorem foo_spec : ⦃pre⦄ foo ⦃⇓ r => ⌜rigid_post r⌝⦄

-- @[spec] form (composable post):
theorem foo_spec {Q} (hpost : ∀ r, rigid_post r → (Q.1 r).down) :
    ⦃pre⦄ foo ⦃Q⦄
```

**Suggestion:** document this clearly in the Hax tactic guide, and
ideally provide a `derive_spec_from_step` macro.

## H. `hax_mvcgen` strips `rotateLeft` arg coercion inconsistently

After `hax_mvcgen` resolves a `core_models.num.U64.rotate_left x n`
call (which takes a `n : Std.U32`), the rotation amount appears in two
forms in the residual goals:

- On the spec side (via the `rotate_left_u64_spec` I wrote):
  `BitVec.rotateLeft x.bv ↑n#u32`
- On the impl side (via the `rot32` abbreviation):
  `BitVec.rotateLeft x.bv 1` (with the U32→Nat coercion already reduced
  by `rot32`'s `rfl`)

These are definitionally equal (`↑(1#u32) = 1`) but don't unify
syntactically.  Required adding a fifth `show ((1#u32 : Std.U32).val) =
1 from rfl` to the simp set.

**Suggestion:** `hax_mvcgen` could uniformly reduce `↑(N#u32) : Nat` to
`N` for literal `N` when resolving the `rotate_left` step.

## I. `Triple.bind` boilerplate for spec-impl separation

To prove `theta_lift_spec`, the proof structure has to be:

```lean
theorem theta_lift_spec ... := by
  apply Triple.bind
  case hx => exact theta_comp_spec_local s  -- impl side
  case hf =>
    intro r_impl
    unfold keccak_f.theta_unrolled
    hax_mvcgen
    all_goals try scalar_tac
    -- Algebraic close here
```

The `Triple.bind; case hx; case hf; intro` boilerplate is 5 lines that
appear in every spec-coupling proof.  A `triple_bind` macro that takes
the impl-side spec as its argument would simplify.

**Suggestion:** add a `triple_bind_spec impl_side_spec` tactic to Hax.

## J. `Array.make` discrimination from `⟨_, _⟩` constructor

`Std.Array.make n init hl := ⟨init, hl⟩`.  When unfolding
`lift_theta_applied` (which uses `Array.make`), the goal contains
`Array.make 25#usize [...] ⋯` on one side.  To match against the
Subtype constructor form `⟨List, length proof⟩`, I had to add
`Std.Array.make` to the simp set EVEN THOUGH it's an `abbrev`.

**Suggestion:** mark `Std.Array.make` as `@[reducible]` or add a `@[simp]`
unfolding lemma `Array.make_def : Array.make n init hl = ⟨init, hl⟩`.

## K. `set_with_zeta` post-condition requires `Array.set_val_eq` bridge

The `set_with_zeta` primitive produces an internal `Usize` for the
flat index `5*j + i`, which is structurally distinct from a
reconstructed `⟨5*j+i, _⟩#uscalar`.  The two are `.val`-equal but the
Aeneas `Array.set i v` discriminates by the Usize wrapper.

Solving this requires writing the postcondition at the underlying list
level via `Array.set_val_eq`:

```lean
r.st.val = s.st.val.set (5 * j.val + i.val) ((s.st.val[5 * j.val + i.val]!).set zeta v)
```

rather than the natural

```lean
r.st = s.st.set ⟨5 * j.val + i.val, _⟩ ((s.st.val[5 * j.val + i.val]!).set zeta v)
```

**Suggestion:** add a `@[simp]` lemma `Array.set_canonical_usize :
∀ (i : Usize), s.set i x = ⟨s.val.set i.val x, ...⟩` so mvcgen-generated
Usize indices and reconstructed Usize indices both reduce to the same
form.

## L. Re-extraction toolchain pin

`hax_aeneas.py` pins `AENEAS_VERSION = "b5c45e84"`, `HAX_VERSION =
"7b4bd97058..."`, but the released aeneas/hax versions don't always
include these commits.  Building aeneas from source requires:

- A dedicated opam switch (OCaml 5.2.1).
- 11 ocaml deps installed by name (no `opam install --deps-only`).
- Charon at the matching `charon-pin` commit.
- macOS users need `gmake` (Homebrew) because aeneas's Makefile
  rejects system `make 3.81`.

The `SKIP_VERSION_CHECK=1` escape hatch helps when a downstream
flag mismatch isn't actually breaking (e.g. when hax-evit HEAD
advances past the pinned commit but still produces compatible output).

**Suggestion:** ship a Docker image / nix flake with the pinned
toolchain so end users don't need to bisect commits and OCaml versions.

## M. `Hax/MissingLean.Std.Do.Triple.Basic` lemmas are underdocumented

The Triple entailment lemmas (`Triple.bind`, `Triple.pure`,
`Triple.of_entails_right`, etc.) are the workhorses for assembling
spec-impl coupling proofs but have only sketch docstrings.  Each took
30+ minutes of read-the-source to figure out applicability.

**Suggestion:** add worked examples in `Hax/MissingLean.Std.Do.Triple`
showing how to compose `Triple.bind` with both `@[spec]` and `@[step]`
postconditions.

## N. Test infrastructure

There's no equivalent of `cargo check --tests` for the aeneas-lean
proofs — `lake build` is all-or-nothing.  When iterating on a single
proof file, `lake env lean File.lean` is the closest, but each call
re-compiles dependencies, taking 8–75 s per check.

The `lean-lsp-mcp` server (via the `lean4-skills` plugin) gets this
down to <1s by reusing the LSP session, but is an external dep.

**Suggestion:** add a documented `lake env lean File.lean` wrapper that
caches dependencies (or directly recommend the `lean-lsp-mcp` /
language-server workflow in the aeneas-lean README).

## Specific simp lemmas that would have saved hours

A wishlist of `@[simp]` lemmas missing from `Aeneas.Std`:

1.  `Usize.val_ofNat_lit : (Std.Usize.ofNat n h).val = n` (when n is a
    literal Nat); same for `U32.val_ofNat_lit`, etc.
2.  `Array.val_eq_coe : (a : Array α n).val = ↑a` (canonicalise the
    coercion form).
3.  `Std.Array.make_eq : Array.make n init hl = ⟨init, hl⟩` (unfold the
    constructor abbrev).
4.  `Array.getElem!_Nat_eq_via_coe : (↑a : List α)[n]! = a.val[n]!`
    (bridge the two indexing forms).
5.  `UScalar.bv_xor`-style lemmas extended to handle `UScalar.val`
    propagation through `^^^`/`&&&`/`~~~` uniformly.
6.  `BitVec.rotateLeft_lit_nat : (x : BitVec _).rotateLeft (↑n#u32) =
    x.rotateLeft n.toNat` (or a `decide`-based simp norm).

If just (1) and (4) were in `Aeneas.Std`, the ThetaLift algebraic close
would have closed on the first attempt.

---

## Closing note

Stage 2 of the SHA-3 equivalence proof landed in 8 sessions × 1.5
days each; ~60% of that was diagnostic time on the surface-syntax /
underlying-term mismatches in sections A–C above.  The proof
**structure** (the 11 sub-function `@[spec]` lemmas, the 12-conjunct
`theta_comp_spec_local` post, the `lift_theta_applied` definition, the
25 `lift_getElem_bv_N` helpers, the impl-side preservation specs) was
straightforward to write once the form-matching issues were
understood.  The remaining `sorry` (the algebraic fold from LL-tower
to single LL) is one missing piece of simp-normalisation lore.

If hax-aeneas-lean is to become accessible to verification engineers
who aren't already deeply familiar with Lean 4's elaboration
internals, the surface-vs-underlying-term disambiguation (A–C) and the
`Aeneas.Std` simp-lemma wishlist above are the most impactful items to
address.
