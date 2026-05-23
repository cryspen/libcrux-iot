/-
  # ML-KEM (libcrux-iot) ↔ hacspec ML-KEM — verification campaign plan

  Goal: prove the libcrux-iot ML-KEM implementation in
  `libcrux-iot/ml-kem/src/` (Lean-extracted to
  `LibcruxIotMlKem/Extraction/Funs.lean` via `hax → aeneas → aeneas-lean`)
  computes the same KEM as the hacspec specification in `specs/ml-kem/src/`
  (FIPS-203 Algorithms 12–21), with panic-freedom under the stated
  preconditions, up to a top-level theorem per parameter variant
  (ML-KEM-512 / ML-KEM-768 / ML-KEM-1024).

  See also: `~/.claude/plans/iot-mlkem-fstar-proof-bodies-deep.md` for
  a per-lemma function-by-function analysis of the upstream F* tree
  (`~/libcrux-ml-kem-proofs/{libcrux-ml-kem,specs/ml-kem}/proofs/fstar/`)
  informing each sketch below. Cross-references in lemma sketches use
  the form `[F*-port: <upstream-module>.<lemma>]`; refer to that
  report's §2 for the upstream proof shape and §3 for the Commute /
  Bridges deep dives.

  This file is the campaign skeleton. Every typed signature in this
  file is either (a) a "decide"-trivial Montgomery bridge identity
  that fully closes, or (b) commented out behind a `/-` … `-/` block
  because the referenced impl symbol is not yet extracted (or extracts
  but doesn't compile against the current pins — see KNOWN BLOCKER
  below). Treat the sketch comment above each lemma as the proof
  plan, and close them leaf-to-root following the §13 methodology in
  `lean-for-libcrux`'s `SKILL.md`. **DO NOT execute proofs here**;
  create a sibling `Equivalence/<Topic>.lean` file per layer
  (mirroring the SHA-3 tree's `BitKeccak/` + `Equivalence/` +
  `Sponge/` decomposition) and move each lemma to its destination
  file as you close it.

  ## Architecture (mirroring SHA-3 §6.5 Campaign 1 + 2 + 3)

  ```
                          ┌──────────────────────┐
                          │ libcrux-iot impl     │
                          │ (Aeneas-Lean monad,  │
                          │  PortableVector,     │
                          │  Montgomery domain)  │
                          └──────────┬───────────┘
                                     │ Campaign 1: structural
                                     │ equivalence via mvcgen +
                                     │ §5.7 idioms (impl matches a
                                     │ pure-Lean intermediate spec
                                     │ in the same data shape)
                                     ▼
                          ┌──────────────────────┐
                          │ Intermediate pure-   │  (sibling
                          │ Lean spec            │   `BitMlKem/Spec.lean`
                          │  (Vector of I16,     │   to be created)
                          │   Montgomery domain) │
                          └──────────┬───────────┘
                                     │ Campaign 2: algebraic
                                     │ equivalence — Montgomery
                                     │ × R⁻¹ canonical-form bridge
                                     │ to the spec's `FieldElement
                                     │ ∈ [0,q)` representation.
                                     ▼
                          ┌──────────────────────┐
                          │ hacspec spec         │
                          │ (Polynomial =        │
                          │  [FieldElement; 256])│
                          │ (FIPS-203 verbatim)  │
                          └──────────────────────┘
                          ▲ Campaign 3: byte-level
                          │ keypair/encaps/decaps composition.
  ```

  Campaign 1 (impl ↔ intermediate) does most of the heavy lifting —
  the impl is in Montgomery domain, uses imperative loops with
  scratch vectors, and trafficks in `Aeneas.Std.Array Vector 16`
  instead of `[FieldElement; 256]`. The intermediate spec sidesteps
  the algebraic conversion. Campaign 2 then handles the algebraic
  pieces (Montgomery↔standard, NTT layer fusion, byte-level
  serialization equivalence) without `hax_mvcgen` overhead.

  **Critical architectural finding from the F* deep-review** (§3 of the
  deep-review): the upstream proof tree is structured around a
  `Hacspec_ml_kem.Commute.*` bridging layer (4234 LOC across
  `Chunk.fst`, `Bridges.fst`, `Serialize.fst`, `ModQ.fst`,
  `ProofUtils.fst`, `Parameters.Sizes.fst`) that maps almost 1-to-1
  to what Lean needs as a `BitMlKem/` subtree. The intermediate spec
  layer is THE load-bearing reuse from upstream; without it, the L3+
  impl↔hacspec equivalences have no clean shape to land on. See
  "Recommended Lean infrastructure" below for the 7-module backlog.

  ## Recommended directory layout (mirror of SHA-3 `BitKeccak/`)

  ```
  LibcruxIotMlKem/
    Plan.lean                  ← this file (campaign skeleton)
    Extraction/Funs.lean       ← hax→aeneas output (KNOWN BLOCKER)
    Util/
      NumericKeystones.lean    ← B.1–B.4 already here + 2 missing
      Montgomery.lean          ← Int.emod ↔ ZMod 3329 bridge
      ModQ.lean                ← opaque mod_q_eq + intro/reveal
      FieldElement.lean        ← FE type + i16_to_spec_fe / mont
      PortableVector.lean      ← elementwise_proof macro for L1
      BVDecide.lean            ← BitVec helpers for L5.4/L5.5
    BitMlKem/                  ← intermediate pure-Lean spec
      Spec.lean                ← MontPoly type + bit_<op> defs
      Commute.lean             ← per-vector / per-poly commute lemmas
      StateIso.lean            ← impl PolyRingElt ↔ BitMlKem.MontPoly
      AlgEquiv.lean            ← bit_* ↔ Spec algebraic equivalence
    Equivalence/
      L0_*.lean L1_*.lean ...  ← per-layer Triple closures
      HacspecBridge.lean       ← top-level (Campaign 3) coupling
  ```

  ## Phase 0 status (post-2026-05-22 — matrix-boundary extraction landed)

  Phase 0 originally listed three extraction gaps. As of commits
  `d6c0bca` / `993b381` / `047b07b` (peer session) plus `4b23f33` /
  `e978e3b` (S01), the gaps are resolved as follows.

  ### (a) Root file mis-import + Funs.lean compile ✅ LANDED

  - Root `LibcruxIotMlKem.lean` now imports `Plan` + `Extraction.Funs`
    + `Equivalence.L0_FieldArith` (commit `4b23f33`).
  - The `libcrux_secrets` Classify / Declassify /
    `Libcrux_secretsIntCastOps` constants that the older pin lacked
    are now provided by the vendored `LibcruxSecrets` Lean lib
    (commit `047b07b`, `vendored/libcrux-secrets/proofs/aeneas-lean/`).
    `Extraction/Missing.lean` retains only the few shims
    `LibcruxSecrets` doesn't cover (search for
    `PHASE0B-MISSING-PATCH` for the patch fence in Funs.lean).

  ### (b) Impl extraction — widened to matrix boundary ✅ LANDED

  `libcrux-iot/ml-kem/hax_aeneas.py` now extracts (commit `993b381`):
  `crate::vector::*`, `crate::ntt::*`, `crate::invert_ntt::*`,
  `crate::polynomial::*`, `crate::matrix::*`. This covers Plan
  Layers 0–3 (field arith → NTT/iNTT) + 6–7 (polynomial / matrix).
  The generated `Extraction/Funs.lean` is ~5525 LOC (~212 defs);
  some sampling functions also appear via transitive reachability
  from `ntt::ntt_binomially_sampled_ring_element` and
  `matrix::sample_matrix_entry`.

  **Pending — outside the matrix boundary** (the user is handling
  these in another session):

  - `ind_cpa.*` (K-PKE; Layer 8) — body present in Rust source, not
    yet extracted.
  - `ind_cca.*` (FO transform; Layer 9) — same.
  - `mlkem512::*`, `mlkem768::*`, `mlkem1024::*` (per-variant entry
    points; Layer 10) — same.
  - `types.*` (key / ciphertext newtype wrappers).
  - `hash_functions.*` (SHA-3 / SHAKE coupling; the aeneas-lean
    backend rejects `shake128_squeeze_*` for nested mutable borrows
    — marked `#[hax_lib::opaque]` and forwarded to charon via the
    `OPAQUE` list in `hax_aeneas.py`).
  - `constant_time_ops.*` (used by FO transform).
  - `sampling::sample_from_binomial_distribution` (top-level CBD
    sampler — Layer 4.3). Only `sample_from_xof` and
    `sample_from_uniform_distribution_next` are extracted today.
  - Top-level serialization: `serialize::serialize_uncompressed_ring_element`,
    `serialize::deserialize_to_uncompressed_ring_element`,
    `serialize::deserialize_ring_elements_reduced` (the per-poly
    `serialize::deserialize_to_reduced_ring_element` IS extracted).

  Per the peer's commit message, the full-crate extraction surfaces
  ~33 Lean errors across 7 stub categories (Hash trait,
  UnbufferedXofState, shake128_*, StepBy iterator, SharedAArray
  IntoIterator, Iter.next, plus several "overloaded" elaboration
  issues). Filed for follow-up; the matrix boundary is the current
  scope.

  ### (c) Hacspec aeneas-lean extraction ✅ LANDED IN FULL

  `specs/ml-kem/proofs/aeneas-lean/HacspecMlKem` (commit `d6c0bca`)
  is the Lean lib for the FIPS-203 spec. ~6677 LOC, ~250+ defs,
  covers the entire spec including `ind_cpa.*`, `ind_cca.*`, the
  full byte-level serialization stack, and Algorithm 6–21. Spec
  references in this Plan that read `Spec.foo` resolve to
  `hacspec_ml_kem.foo` in the generated names (the
  `hacspec_ml_kem.` prefix replaces `Spec.` from older Plan
  drafts).

  ## Triple skeleton naming — actual vs generated function names

  Some Triple skeletons below were written before the matrix-
  boundary extraction landed and reference names that don't exactly
  match the generated `Extraction/Funs.lean` defs:

  - **L4.3** (`sample_from_binomial_distribution_spec`) — correctly
    marked "extraction missing" since the symbol is outside the
    matrix boundary today.
  - **L6.2** lists `add_to_ring_element` as a 4th fused-add variant,
    but it does NOT exist in the impl Rust source — only
    `add_message_error_reduce`, `add_error_reduce`,
    `add_standard_error_reduce` do. The
    `hacspec_ml_kem.polynomial.add_to_ring_element` is a spec-only
    pure poly add used in `polynomial.rs`'s `cross_spec` tests.
    Treat L6.2 as a 3-lemma group.
  - **L6.3 Triple skeleton** is named `PolynomialRingElement_ntt_multiply_spec`
    and targets the symbol `polynomial.PolynomialRingElement.ntt_multiply`;
    the generated def is `polynomial.PolynomialRingElement.accumulating_ntt_multiply`.
    Use the generated name when opening the proof.
  - **L6.5 / L6.6 / L6.7** (`serialize_uncompressed_ring_element` /
    `deserialize_*_ring_element` / `deserialize_ring_elements_reduced`)
    — outside matrix boundary today. The per-poly
    `serialize.deserialize_to_reduced_ring_element` IS extracted and
    is a valid Triple target.

  Cross-reference any L1/L5/L6/L7 Triple's impl symbol against
  `Extraction/Funs.lean` before opening a proof; if the name
  diverges from what Plan says, prefer the actual generated name
  and update the skeleton.

  ## Layer summary

  - **Layer M** — Bridge / Mont infrastructure (`BitMlKem.Spec`,
    `BitMlKem.Commute`, `BitMlKem.StateIso`, `BitMlKem.AlgEquiv` +
    Util support). NOT a stack of @[spec] Triples — it's the pure
    Lean spec definitions, opaque predicates, and per-vector commute
    lemmas that every L0+ Triple post-condition references. Build
    this FIRST. See deep-review §3 + §5. Est. 600 LOC, 2–3 weeks.
  - **Layer 0** — Field arithmetic primitives (4 leaf @[spec]s).
  - **Layer 1** — `PortableVector` element-wise ops (~14 @[spec]s).
  - **Layer 2** — NTT layer butterfly steps (8 @[spec]s).
  - **Layer 3** — NTT / iNTT polynomial drivers (10 loop @[spec]s).
  - **Layer 4** — Sampling (XOF / rejection / CBD, 3 @[spec]s).
  - **Layer 5** — Compress / decompress / byte encode-decode (~16
    @[spec]s).
  - **Layer 6** — Polynomial / vector composites (~18 @[spec]s).
  - **Layer 7** — Matrix ops (5 @[spec]s).
  - **Layer 8** — K-PKE (IND-CPA) layer (5 @[spec]s).
  - **Layer 9** — IND-CCA (FO transform) — 5 @[spec]s.
  - **Layer 10** — Per-variant top theorems (15 = 3 variants × 5
    public API fns).

  Total: ~103 @[spec]s + ~50 Layer-M lemmas, ~15 top theorems.
-/

-- Lean imports. Phase 0 done — `Extraction.Funs` builds; this Plan
-- file is consumed by `LibcruxIotMlKem.lean` only for its `modq_eq`
-- export and the doc-comment sketches. The actual impl Triples are
-- being moved out into `Equivalence/L<layer>_*.lean` files as they
-- close (see e.g. `Equivalence/L0_FieldArith.lean`).
import Aeneas
import Hax
import LibcruxIotMlKem.Util.ModularArith
import LibcruxIotMlKem.Util.NumericKeystones

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Plan

open Aeneas Aeneas.Std Std.Do

/-! ## `modq_eq` — canonical modular-equality predicate

  Every L0–L9 Triple postcondition that asserts a congruence
  `a ≡ b (mod q)` (where `q = 3329`) uses this single named predicate.
  We define `modq_eq a b q` as `(a - b) % q = 0` (the subtraction-mod
  spelling rather than `a % q = b % q`) for two reasons:

  1. It composes additively (`modq_eq a b q ∧ modq_eq c d q → modq_eq
     (a + c) (b + d) q`) without any side conditions, matching the way
     `lemma_mod_add_distr` is invoked in the upstream F* proofs.
  2. The `(_ - _) % q = 0` shape is what `scalar_tac` / `bv_decide` can
     close directly on small numeric instances, so leaf lemmas avoid
     having to unfold a `ZMod` cast.

  Standard lemmas about `modq_eq` (`refl`, `symm`, `trans`, `add`, `mul`,
  `const_mul`, and the `ZMod q` bridge `modq_eq a b q ↔ (a : ZMod q) =
  (b : ZMod q)`) should be proved once in `Util.ModularArith` (see
  "Reusable infrastructure" Tier 1 below) and used selectively where
  Lean's automation needs the algebraic API.

  NOTE (low priority — future revisit): mathlib's `ring` tactic could in
  principle simplify many `modq_eq` proof obligations after a single
  `unfold modq_eq` + cast to `ZMod 3329`. In practice most of our
  L0–L4 sites close via concrete low-level arithmetic (`decide` on a
  Nat keystone like `(62209 * 3329) % 2^16 = 1`, `bv_decide` on a
  16-bit identity, or `scalar_tac +nonLin` on a quotient bound), so the
  named predicate plus a small fact base often suffices and `ring` is
  not on the critical path. Flag this for re-evaluation once L5/L6
  closes — the byte-pack / NTT-domain proofs there might benefit. -/
-- `def modq_eq` and its standard lemma surface (refl/symm/trans/add/sub/
-- const_mul/iff_zmod) moved to `LibcruxIotMlKem.Util.ModularArith`.
-- The qualified name is `libcrux_iot_ml_kem.Util.modq_eq`; references
-- in the lemma sketches below resolve via the `import` at the top of
-- this file.
export libcrux_iot_ml_kem.Util (modq_eq)

/-! ## How to read each lemma sketch

Each lemma below appears as:

```text
/- **L<layer>.<n> `<impl_fn_name>`** — <human summary>.

    Hax requires/ensures: <verbatim quote from upstream `src/<file>.rs:<line>`>

    ## Sketch
    <3-15 lines of proof strategy>

    ## Depends on
    - <other lemma names>

    ## Complexity tier
    <one of: mvcgen-trivial / scalar-tac-close / bv-decide-close /
     algebraic-close-required / needs-new-helper-tier /
     loop-induction>
-/
/- Triple skeleton (uncomment + finalize once Extraction.Funs resolves):
@[spec]
theorem <impl_fn_name>_spec <args> :
    ⦃ ⌜ <precondition mirroring upstream hax_requires> ⌝ ⦄
    libcrux_iot_ml_kem.<module>.<impl_fn_name> args
    ⦃ ⇓ r => ⌜ <postcondition anchored to spec> ⌝ ⦄ := by
  sorry
-/
```

The 4 typed bridge theorems at the bottom (B.1–B.4) do compile —
they're closed by `decide` over small `Nat` arithmetic.
-/

/-! ## Cross-cutting techniques

Six patterns recur across both the upstream F* proofs and the Lean
campaign. Commit each Lean idiom to muscle memory before opening any
L3+ file. (Deep-review §4 has the full discussion.)

1. **Opaque predicates with controlled reveal**. F* uses
   `[@@ "opaque_to_smt"]` on `mod_q_eq`, `intt_mont_form_lane`,
   `*_branch_post`, etc. to keep Z3's quantifier instantiation budget
   bounded. Lean equivalent: `attribute [local irreducible] foo`
   inside the consuming section (SKILL §5.7 Idiom 2). Bridge lemmas
   become `simp`-gated unfolders. Apply to: `ModQ.eq`,
   `intt_mont_form_lane`, per-step `bit_*` defs.

2. **Per-vector commute → per-poly assembly**. F* writes
   `Classical.forall_intro aux + Seq.lemma_eq_intro` (50+ instances
   in Chunk.fst). Lean equivalent: `Array.ext; intro j hj`, then
   per-lane case work. About 30% shorter than F*'s explicit aux.
   Every L6.x and L7.x driver Triple ends with this pattern.

3. **Layer-2 per-branch dispatch via `interval_cases`**. F* hand-rolls
   4 private layer-2 sub-lemmas (Bridges.fst:519, 555, 591, 627) for
   Z3 budget reasons. Lean's `interval_cases (i / 8)` (or `(i / 4)`,
   `(i % 4)`) gives the same case split inline — no need for separate
   private helpers. Net Lean L2 is shorter than F*.

4. **`--using_facts_from` hygiene via `simp only [<list>]`**. F* tunes
   `--z3rlimit` + `--ext context_pruning` + `--split_queries always`
   per block; Lean's analog is disciplined `simp only [<lemma list>]`
   plus `set_option maxHeartbeats N in` per theorem (cap 16M per
   SKILL §9.5).

5. **Ghost vars + `let_ghost`**. F* names intermediate algebraic
   witnesses via `let_ghost x = ...` so Z3 sees them as
   universally-known constants. Lean equivalent: `have x : T := ...`
   blocks introducing the witness before its use; for pure-Prop
   ghosts use `obtain ⟨..⟩ := ...` to destructure.

6. **`Tactics.GetBit.prove_bit_vector_equality'` ↔ `bv_decide`**. F*'s
   Meta-F* tactic for serialize/deserialize bit-position enumeration
   (Vector.Portable.Serialize.fst, 1835 LOC, 12 lemmas in 4-line
   invocations) has Lean's `bv_decide` as a direct, faster analog.
   Apply to every L5.4/L5.5 spec.
-/

/-! ## Reusable infrastructure (build BEFORE Triple campaign)

This section catalogues the proof infrastructure the campaign needs.
It is split into four **tiers** by *where the code should live*:

  - **Tier 1** — `libcrux-iot-utils/` (or analogous new Lean crate),
    shared across `libcrux-iot/{sha3, ml-kem, ml-dsa}` proof trees.
  - **Tier 2** — `abentkamp/aeneas` (upstream Aeneas Std library).
  - **Tier 3** — `cryspen/hax-evit` (upstream Hax Triple/mvcgen helpers).
  - **Tier 4** — Algorithm-specific reusables that stay per-algorithm
    but should follow a *parallel structure* across SHA-3 / ML-KEM /
    ML-DSA so a verifier can move between them without re-learning the
    naming conventions.

The deep-review (§5) identifies the per-algorithm helper modules whose
absence blocks every L3+ ML-KEM proof. Below each tier we name the
lemma surface, cite the current SHA-3 location (where the prototype
exists), enumerate ML-KEM Plan layers that depend on it, and label a
**verdict**: `[Lift verbatim]` / `[Refactor before lift]` /
`[Pattern-only]` (per-algo specifics differ; only the architecture
generalises).

### Tier 1 — iot-local reusable libraries

These should live in a new `libcrux-iot-utils/` crate. Once factored,
the three iot algorithms each `import LibcruxIotUtils.<Module>` rather
than re-deriving the helper.

- **`Util.ModularArith`** — `modq_eq` (defined above) + the standard
  lemma set. Concretely:
  ```lean
  @[simp] theorem modq_eq_refl  : modq_eq a a q
  theorem modq_eq_symm  : modq_eq a b q → modq_eq b a q
  theorem modq_eq_trans : modq_eq a b q → modq_eq b c q → modq_eq a c q
  theorem modq_eq_add   : modq_eq a b q → modq_eq c d q →
                          modq_eq (a + c) (b + d) q
  theorem modq_eq_sub   : modq_eq a b q → modq_eq c d q →
                          modq_eq (a - c) (b - d) q
  theorem modq_eq_const_mul : modq_eq a b q → modq_eq (k * a) (k * b) q
  theorem modq_eq_iff_zmod : modq_eq a b q ↔ (a : ZMod q) = b
  ```
  *Used by*: every L0–L3 ML-KEM lemma + likely all ML-DSA arithmetic
  (same `q = 8380417` style modular equality at the integer level).
  *Current SHA-3 location*: N/A — SHA-3 has no FE arithmetic; this is
  the first instance.
  *Verdict*: **Lift verbatim** once L0.3 closes (the lemma surface is
  algorithm-independent; only the modulus changes).

- **`Util.Montgomery`** — Montgomery-form bridges: `R = 2^16`, the
  per-algorithm `q`, the `mont_R_inv_q`, `mont_qinv_R`,
  `mont_reduce_int_form` helper (the L0.3 keystone — "given
  `(value - km) % 2^16 = 0`, the canonical Mont identity holds"),
  `to_standard_domain` lemmas. The 4 typed bridge theorems already at
  Plan.lean B.1–B.4 (`mont_R_inv_q`, `mont_1441_eq_inv128`,
  `mont_2285_eq_R_mod_q`, `mont_1353_eq_RR_mod_q`) move here, plus
  the 2 missing `mont_qinv_R`, `mont_128_169_512`.
  *Used by*: every L0/L2/L3/L6 ML-KEM lemma. ML-DSA has a different
  q = 8380417 but the same `R = 2^32` structure — file should be
  parameterized on `q, R` so the same lemmas serve both.
  *Current SHA-3 location*: N/A (SHA-3 has no Montgomery layer).
  *Verdict*: **Refactor before lift** — parameterize over `q, R`
  before factoring; ML-KEM's concrete-`q = 3329` instances stay in
  the ML-KEM tree as 1-line `def`s pointing at the generic.

- **`Util.BVDecide`** — common `bv_decide` macro patterns for U16/U32
  bit-vector identities used by serialize/compress hierarchies:
  rotation, masking, `get_n_least_significant_bits`, deinterleave,
  `BitVec.flatten` ↔ `int_t_array` shape lemmas. ML-KEM's
  `serialize_D` / `deserialize_D` (L5.4/L5.5) generate ~12 such
  obligations; SHA-3's theta-pi-chi pipeline has analogous bit-twiddle
  lemmas at every step.
  *Used by*: ML-KEM L0.1, L1.8, L1.9, all of L5; SHA-3 Theta/Rho/Chi.
  *Current SHA-3 location*:
  `libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/BitKeccak/StructEquiv.lean`
  and `Equivalence/Lift.lean` contain ~30 `bv_decide`-shaped
  patterns the ML-KEM port can mine.
  *Verdict*: **Pattern-only** — the *technique* (apply
  `Std.UN.bv_eq_imp_eq` then `bv_decide`) generalises; the concrete
  lemmas differ per bit-pattern. Factor the *helper tactic* + a small
  set of generic combinators (`BitVec.flatten`, slice extraction),
  but keep algorithm-specific bit identities in the algorithm tree.

- **`Util.LoopSpecs`** — Aeneas `loop_range_spec_usize`,
  `loop_range_spec_i32`, fold-form loop invariants. The "16-iter loop
  with per-element invariant" pattern (L1.x's elementwise proof
  macro) and the "K-loop with running bound" pattern (L7.x matrix
  ops) both ride on top of this.
  *Used by*: every L1.x, L3.x, L6.x, L7.x ML-KEM lemma; SHA-3
  Absorb/Squeeze blockwise loops.
  *Current SHA-3 location*:
  `libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Sponge/LoopSpecs.lean`
  — has both `loop_range_spec_usize` and a per-iter step-spec
  combinator. The 200 LOC there are ~90% reusable.
  *Verdict*: **Lift verbatim**. This is the single highest-ROI
  candidate to factor first — every Triple from L1 upward depends
  on it and the SHA-3 implementation is already battle-tested.

- **`Util.SliceSpecs`** — Aeneas Std bridges: `Slice.len`, `massert`,
  slice/array indexing over `Range`, U32/U64 LE byte conversions,
  `try_from`, `Result.unwrap`, `copy_from_slice`. Every L5 byte
  encode/decode + every L8/L9 byte concatenation routes through
  these.
  *Used by*: ML-KEM L5.x, L6.5–L6.7, all of L8, all of L9; SHA-3
  block I/O.
  *Current SHA-3 location*:
  `libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Sponge/SliceSpecs.lean`
  + `Sponge/Bytes.lean`. ~250 LOC total.
  *Verdict*: **Lift verbatim** — pure Aeneas-Std plumbing, zero
  algorithm-specific content. Should land *before* any L5 work
  starts.

- **`Util.CreateI`** — `createi_pure_spec` (the pure-closure-array-
  builder Triple) + `from_fn_pure_spec` (FnMut analog). Every "build a
  16-element array from a closure" in the impl extracts to a
  `createi` call; without this spec the Triple has nothing to land
  on.
  *Used by*: every ML-KEM polynomial / matrix / sample construction
  (L1.x output writes, L4 sampling array builds, L7.1 matrix
  population). SHA-3 uses it for block packing.
  *Current SHA-3 location*: split between
  `libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Equivalence/HacspecBridge.lean`
  (the `createi_pure_spec` shape) and
  `libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Sponge/XorBlockSpec.lean`
  (the `from_fn_pure_spec` FnMut variant).
  *Verdict*: **Refactor before lift** — the two definitions should
  be merged into one `Util.CreateI.lean` with consistent naming
  (current SHA-3 names are inconsistent across the two files).

- **`Util.NumericKeystones`** — the small set of `decide`-closed
  arithmetic identities each algorithm needs (ML-KEM's 6 modular
  keystones B.1–B.6, ML-DSA's analogous `q⁻¹ mod 2^32` keystone,
  SHA-3's `IOTAS[i]` literal table). One file per algorithm but the
  *pattern* — "list of `theorem foo : N1 % N2 = N3 := by decide`" —
  is universal.
  *Verdict*: **Pattern-only** — each algorithm has its own table; the
  factoring is the directory convention "always store keystones in
  `<Algo>/Util/NumericKeystones.lean`" rather than the lemmas.

- **`Util.ModQ`** (~100 LOC, 4 h) — opaque `mod_q_eq` predicate +
  intro/reveal/refl/trans/sym helpers wrapping `modq_eq`. Direct
  port of upstream `Hacspec_ml_kem.ModQ.fst` (57 LOC F*).
  *Verdict*: **Lift verbatim** once parameterised on `q` — the
  opaque/reveal API is identical across ML-KEM and ML-DSA.

- **`Util.FieldElement`** (~150 LOC, 1 day) — FE type +
  `i16_to_spec_fe` + `mont_i16_to_spec_fe` + the ~20 per-element
  `lemma_*_fe_commute_*` bridges from upstream Chunk.fst:36-180,
  closed via ZMod-cast + `ring`. **Pattern-only**: the bridge lemmas
  are algorithm-specific (ML-DSA uses `i32` lanes); only the
  architecture lifts.

- **`Util.PortableVector`** (~300 LOC, 2 days) — the
  `elementwise_proof` macro. Takes a per-element Triple + per-element
  post predicate, yields a 16-iter loop Triple. Each of L1.1–L1.10
  becomes a 5-line instantiation. **Refactor before lift** — the
  macro should be parameterized on lane count (ML-DSA's
  `Coefficients` arrays are 256 not 16).

The total upfront infra cost is ~3 weeks but unblocks the entire L3+
campaign. The single biggest insight from the deep-review (§6
scorecard): **do NOT attempt to prove impl ↔ hacspec equivalence
directly**. Build the per-algorithm `BitMlKem.Spec` +
`BitMlKem.Commute` first (Tier 4 below); every subsequent layer is
then a clean two-phase composition (Campaign 1: impl ↔ bit_*;
Campaign 2: bit_* ↔ hacspec).

### Tier 2 — Aeneas-upstream candidates

Lemmas that should arguably live in upstream Aeneas
(`abentkamp/aeneas`) rather than per-algorithm. From the F* deep-
review and the SHA-3 work, the following are PR-ready:

- **Generic `UScalar.bv_xor` / `bv_and` / `bv_or` + congruence
  lemmas.** The SHA-3 campaign filled these locally as
  `Equivalence/UScalarAC.lean` (`Std.Associative` /
  `Std.Commutative` instances on `UScalar.xor`, plus the
  `bv_eq_imp_val_eq`-style lifts that lower a BitVec identity to a
  UScalar identity). Flagged in `HAX_AENEAS_PITFALLS.md` L13(1) /
  L13(4).
  *Current local-fill*:
  `libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Equivalence/UScalarAC.lean`
  (~60 LOC).
  *Upstream signature*: ~`Aeneas.Std.UScalar.{N}.bv_xor : (x.xor y).bv = x.bv ^^^ y.bv`,
  symmetric for `and`, `or`. The `Std.Associative` / `Std.Commutative`
  instances follow.
  *PR-readiness*: **HIGH** — the proofs are 1-line `bv_decide` each;
  zero algorithm-specific content. SHA-3 has been using these for
  months with no churn.

- **`@[simp] Usize.val_ofNat_lit (n h) : (Usize.ofNat n h).val = n`**
  (`HAX_AENEAS_PITFALLS.md` L13(1)). Without this, every concrete
  literal `16#usize` is opaque to `simp`/`scalar_tac`.
  *Current local-fill*: scattered `decide`-closed unfold lemmas in
  every SHA-3 `Sponge/*.lean` file.
  *PR-readiness*: **HIGH** — one-line `rfl` proof.

- **`@[simp] Array.getElem!_Nat_eq_via_coe`** (PITFALLS L13(4)) —
  bridges `arr[i]!` between `Fin n` and `Nat` indexing so `simp` can
  rewrite freely. Currently the L1.x / L7.x ML-KEM Triple
  postconditions awkwardly carry `i : Fin K.val` instead of
  `i : Nat ∧ i < K.val` precisely because of this gap.
  *PR-readiness*: **HIGH** after a small design discussion (does it
  unify with mathlib `Fin.coe_lt`?).

- **`Array.set_val_eq`, `Array.make` simp lemmas** — also flagged in
  PITFALLS. ML-KEM's L6.5 byte-buffer writes need
  `(Std.Array.update arr i x).val[i]! = x` as `@[simp]`.
  *Current local-fill*: each SHA-3 ThetaLift file unfolds manually.
  *PR-readiness*: **MEDIUM** — straightforward but interacts with
  the existing `Array.update` simp set; needs a quick audit.

### Tier 3 — Hax-upstream candidates

Hax-specific (`cryspen/hax-evit`) Triple / mvcgen helpers worth
promoting. These are *not* algorithm-specific; they belong in
`hax-evit`'s Lean target library next to `hax_mvcgen`.

- **`triple_conj_post`, `triple_imp_intro`, `triple_weaken_precond`**
  — the three combinators every multi-clause Triple uses.
  `triple_conj_post` splits `⦃ pre ⦄ m ⦃ ⇓ r => P r ∧ Q r ⦄` into
  two sub-goals; `triple_imp_intro` discharges a hypothesis-shaped
  precondition into the goal's local context; `triple_weaken_precond`
  weakens a Triple precondition (the "I have a stronger pre than the
  spec asks for" pattern that shows up at every spec invocation
  site).
  *Current SHA-3 location*: triplicated in
  `libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Equivalence/RoundEquiv.lean`,
  `Sponge/Absorb.lean`, `Sponge/Squeeze.lean`. ~40 LOC of pure boiler-
  plate that should live once in hax-evit.
  *PR-readiness*: **HIGH** — the proofs are 5-line bind/return chains;
  the API is universal.

- **A `derive_spec_from_step` macro** (PITFALLS L7 wishlist). Given
  `@[step]` chained smaller `@[spec]` lemmas, derives a composite
  `@[spec]` over the larger function. Today verifiers hand-roll
  this composition every time.
  *PR-readiness*: **MEDIUM** — the macro design is straightforward
  but the `@[step]` ↔ `@[spec]` priority interaction is subtle (see
  `lean-for-libcrux` §5.7 on `@[spec high]` priority).

- **A `triple_bind_spec impl_side_spec` tactic** (PITFALLS L9). The
  bind boilerplate "given `impl_side_spec` for an inner call, weave
  it into the outer Triple goal" is currently 5 lines per spec-
  coupling proof, hand-typed at every L7/L8/L9 site. The tactic
  would compress this to one line and eliminate the most common
  manual error (forgetting to discharge the spec's precondition).
  *PR-readiness*: **MEDIUM-HIGH** — the SHA-3 Sponge campaign used
  this pattern ~60 times; the tactic is a clear win.

### Tier 4 — Algorithm-specific reusables (parallel structure)

These stay per-algorithm but should be **designed for parallel
structure** across SHA-3 / ML-KEM / ML-DSA so a verifier can move
between them without re-learning naming conventions.

- **`<Algo>.Spec` / `<Algo>.Commute` intermediate-spec pattern.**
  SHA-3 introduced this in Campaign 1 (§6.5):
    - `BitKeccak.Spec`        — pure-Lean intermediate spec
    - `BitKeccak.Commute`     — per-vector / per-poly commute lemmas
    - `BitKeccak.StateIso`    — impl ↔ MontPoly round-trip
    - `BitKeccak.AlgEquiv`    — bit_* ↔ Spec.* algebraic equivs
  ML-KEM uses the parallel naming (Layer M of this Plan):
    - `BitMlKem.Spec`
    - `BitMlKem.Commute`
    - `BitMlKem.StateIso`
    - `BitMlKem.AlgEquiv`
  ML-DSA when it starts should use `BitMlDsa.{Spec,Commute,StateIso,
  AlgEquiv}`. A verifier who knows one tree can navigate any of the
  three.

- **Per-algorithm `Equivalence/L<N>_*.lean` Triple closure files.**
  SHA-3 has `Equivalence/{ThetaLift, RoundEquiv, ...}.lean`; ML-KEM
  Plan §"Recommended directory layout" mandates `Equivalence/{L0_,
  L1_, L2_, ...}.lean`. The pattern: each layer file imports the
  Layer-M defs, opens the algorithm's `BitX.Spec` namespace,
  and closes ~5–20 `@[spec]` Triples via the §5.7 composition idiom.

- **Per-algorithm `Spec/` mirror.** Each algorithm should ship a
  `<Algo>Spec/` Lean library that is the hacspec-extracted target
  (the right-hand side of the equivalence). SHA-3 has
  `libcrux-iot/specs/sha3/proofs/aeneas-lean/`; ML-KEM needs
  `libcrux-iot/specs/ml-kem/proofs/aeneas-lean/` (BLOCKER (c)).
  ML-DSA will need its own.

The Tier 4 architectural observation: **once `Util.ModularArith` +
`Util.Montgomery` + `Util.LoopSpecs` + `Util.SliceSpecs` are
factored into a shared crate, each algorithm's per-algorithm reusable
collapses to ~20% of its current footprint**. The Plan estimates
2-3 weeks for Layer M (BitMlKem.{Spec,Commute,StateIso,AlgEquiv}); a
crate-factored version would cut that to ~1.5 weeks because the
generic plumbing already passes its tests in the SHA-3 tree.
-/

/-! ============================================================
    # LAYER M — Bridge / Mont infrastructure (BitMlKem.* + Util.*)

    **Status: NOT BUILT (as of 2026-05-23).** Plan exists at
    `~/.claude/plans/iot-mlkem-layer-M-architecture.md`. Estimated
    **2.5-3.5 wk, 6-8 sub-agent dispatches**, ~3650 LOC across 4 new
    files under `LibcruxIotMlKem/BitMlKem/` plus Util.* supporting
    additions. Direct port of upstream F* `Hacspec_ml_kem.{ModQ,
    Commute.*}.fst` (4234 LOC).

    NOT a sequence of @[spec] Triples. This is the pure Lean spec /
    predicate / commute-lemma layer that every L0+ post-condition
    references. The deep-review §3 walks the F* tree file by file.

    Concretely, fill in (in order):

    ## M.1 `BitMlKem/Spec.lean` — the intermediate spec (~830 LOC)

    Single-agent dispatch; type definitions + a handful of projection
    lemmas. Per the architecture plan §B:

    - `abbrev MontPoly := Vector (ZMod 3329) 256`
      (algebraic working type — `ring` in `ZMod 3329` collapses
       upstream's `lemma_mod_*_distr_*` chains; D1 decision needed).
    - `abbrev SpecPoly := Vector parameters.FieldElement 256`
      (hacspec interface type).
    - `def MontPoly.toSpecPoly`, `def SpecPoly.toMontPoly` (Vector.map
      coercions + round-trip lemmas).
    - `def i16_to_spec_fe_plain`, `def i16_to_spec_fe_mont` (per-lane
      plain / Mont-domain coercions).
    - `def to_spec_poly_plain`, `def to_spec_poly_mont`
      (`PolynomialRingElement → MontPoly`).
    - **34 `bit_<op>` defs** mirroring `HacspecMlKem`'s spec
      surface (M.1 enumeration in arch plan §B.3). Main groups:
        * `bit_add`, `bit_sub`, `bit_neg`, `bit_barrett_reduce`,
          `bit_to_unsigned_representative`, `bit_to_standard_domain`
          (scalar / poly-level FE ops)
        * `bit_mont_mul`, `bit_multiply_by_constant`,
          `bit_montgomery_multiply_by_constant`
        * `bit_ntt_layer_{1,2,3}`, `bit_ntt_layer_4_to_7`, `bit_ntt`
          (forward NTT family)
        * `bit_invert_ntt_layer_{1,2,3}`, `bit_invert_ntt_layer_4_to_7`,
          `bit_invert_ntt_montgomery` (inverse NTT family,
          mirrors `Spec.ntt_inverse_butterflies`)
        * `bit_butterfly`, `bit_inv_butterfly`,
          `bit_base_case_multiply_{even,odd}`
        * `bit_multiply_ntts`, `bit_ntt_multiply_chunk` (the N=16
          per-vector chunk used by L2.8) — distinct from
          `Spec.ntt_multiply_n` (see L2.8 note below)
        * `bit_compress`, `bit_decompress`, `bit_compress_message`,
          `bit_decompress_message`, `bit_byte_encode`,
          `bit_byte_decode`
        * `bit_add_to_ring_element`, `bit_subtract_reduce`,
          `bit_cond_subtract_3329`, `bit_ntt_layer_int_vec_step`,
          `bit_accumulating_ntt_multiply`
    - **Opaque algebraic predicates** (`@[irreducible]`):
      `bit_mont_form_lane` + chunk/poly wraps. Reveal/intro lemmas.
      The `bit_intt_mont_form_lane` predicate from earlier Plan
      drafts is NO LONGER NEEDED — L3.8 anchors directly against
      `Spec.ntt_inverse_butterflies` (see L3.8 [CORRECTED] note
      above), eliminating the opaque-predicate detour for the
      INTT side.

    ## M.2 `BitMlKem/Commute.lean` — per-vector / per-poly commute lemmas
    Mirrors upstream `commute/Chunk.fst` (2711 LOC) + forward parts
    of `commute/Bridges.fst` (1241 LOC). **~59 lemmas across 4
    blocks, ~1840 LOC total, 4-6 sub-agent dispatches.**

    - **Block A — Layer-0 scalar FE commutes** (~22 lemmas,
      **~280 LOC**, 1 agent). Each ~10 Lean lines via ZMod cast +
      `ring`. Covers add/sub/butterfly/mont_mul/barrett/inv_butterfly
      and the per-pair `base_case_mult_pair` family. [F*-port:
      `Commute.Chunk.lemma_{add,sub,butterfly,mont_mul,...}_fe_commute_*`]
    - **Block B — Chunk / per-vector commutes** (~14 lemmas,
      **~405 LOC**, 1 agent). Each ~30 Lean lines via `Vector.ext` +
      Block-A lane invocation. Covers add/sub/multiply-by-constant /
      montgomery-multiply / barrett / cond_subtract / compress /
      decompress at chunk granularity. [F*-port:
      `Commute.Chunk.lemma_{add,sub,...}_chunk_commutes_*`]
    - **Block C — Poly-level commutes** (~10 lemmas, **~325 LOC**,
      1 agent). Each ~25-50 lines. Includes the keystone
      `lemma_intt_mont_form_post` (Chunk.fst:1577 — F* takes 60+
      LOC with `lemma_mod_mul_distr_*` chains; Lean closes in ~15
      lines via `ZMod 3329` + `decide` keystones). Also covers
      `lemma_subtract_reduce_commute`, `lemma_to_standard_domain_finalize_fe`,
      `lemma_add_standard_error_reduce_commute`.
    - **Block D — Forward + reverse NTT-layer commutes** (~13
      lemmas, **~830 LOC**, 3 parallel agents). The heaviest block.
      Covers `lemma_ntt_layer_{1,2,3}_step_to_hacspec`,
      `lemma_inv_ntt_layer_{1,2,3}_step_to_hacspec`,
      `lemma_inv_ntt_layer_int_vec_step_reduce_to_hacspec`, plus the
      `ntt_layer_n_16_{2,4,8}_lane` helpers. **Includes
      `lemma_ntt_multiply_chunk_commutes` (D.13)** — `assume val`
      upstream (Chunk.fst:1311); Lean **must prove**, ~50 LOC via
      `Vector.ext` + Block-A `lemma_base_case_mult_pair_commute`
      (A.18).

    ## M.3 `BitMlKem/StateIso.lean` — impl ↔ MontPoly round-trip
    **~150 LOC, folds into the Block-A agent.** Three theorems:
    - `theorem to_spec_poly_mont_injective` (canonical version
      under `< 1665` bound; extended version under `< 3328`).
    - `theorem lift_id` (lift after canonical-unlift is identity
      on the impl side, given canonical-bounded coefficients).
    - Auxiliary round-trip lemmas (`zmodOfFE_feOfZMod_id`,
      `to_spec_poly_mont_of_zero`, `to_spec_poly_mont_set`).

    ## M.4 `BitMlKem/AlgEquiv.lean` — bit_* ↔ Spec.* algebraic equivs
    **~830 LOC, 2 parallel agents** (rfl-class easy cluster +
    NTT/INTT heavyweight cluster).

    The Campaign 2 closure. Each `bit_<op>` def from M.1 is shown
    equivalent (under `MontPoly ↔ SpecPoly` coercion) to the
    corresponding `Spec.<op>` from `HacspecMlKem` (via
    `Spec.<op>_pure` aliases stripping the `Result`-monadic
    wrapper, per Layer-M plan §F.2 option (b)). Uses the keystones
    B.1–B.4 (+ the two missing keystones above) plus `ring` in
    `ZMod 3329`. ~28 alg-equiv theorems; most reduce to 1-3 line
    `rfl`/`ring` after `Vector.ext`. Heavyweights are the NTT /
    INTT / multiply / add-error-reduce families.

    All of Layer M is `theorem`/`def`, not `@[spec]` Triples — no
    `hax_mvcgen` involvement. The output is the predicate vocabulary
    every L0+ Triple post references.

    ## HacspecMlKem lake-dep wiring (5-minute Phase-3 prerequisite)

    `HacspecMlKem` extraction **already exists** at
    `specs/ml-kem/proofs/aeneas-lean/HacspecMlKem/` (6677 LOC,
    lake-buildable). It is NOT currently a `require` of this impl
    tree's `lakefile.toml`. **First action of Phase 3 (Layer M
    build)** is the one-line lakefile addition:

    ```toml
    [[require]]
    name = "HacspecMlKem"
    path = "../../../../specs/ml-kem/proofs/aeneas-lean"
    ```

    Then M.1's `import HacspecMlKem.Extraction.Funs` resolves and
    every `bit_<op>` def in `BitMlKem/Spec.lean` can reference the
    hacspec spec target directly. Exposes — all as `Result`-monadic
    defs:
    - `Spec.ntt`, `Spec.ntt_inverse_butterflies`,
      `Spec.ntt_inverse` (the L3.8 anchor, the variant with
      terminal `· 128⁻¹`, lives here too — but L3.8 anchors against
      `ntt_inverse_butterflies` because that's what the impl does)
    - `Spec.multiply_ntts`, `Spec.ntt_multiply_n`
    - `Spec.lift_poly`, `Spec.lift_poly_mont`
    - `Spec.compress`, `Spec.decompress`
    - `Spec.byte_encode`, `Spec.byte_decode`
    - `Spec.subtract_reduce`, `Spec.add_to_ring_element`, etc.

    5-minute change. First action of Phase 3 (Layer M build),
    Wave 3.0 per the master plan.
-/

/-! ============================================================
    # LAYER 0 — Field-arithmetic primitives

    The arithmetic foundation. Each lemma is a closed bitvector
    identity provable by `bv_decide` after `apply Std.I16.bv_eq_imp_eq`
    / `apply Std.I32.bv_eq_imp_eq` (SHA-3 `LiftLemmas.lean` pattern).
    Spec anchor: result `≡` input · multiplier (mod 3329).

    Constants (from `vector/portable/arithmetic.rs` and
    `vector/traits.rs`):
    - FIELD_MODULUS = 3329
    - MONTGOMERY_SHIFT = 16, R = 2^16
    - R mod q = 2285, R⁻¹ mod q = 169, R² mod q = 1353
    - BARRETT_SHIFT = 26, BARRETT_R = 2^26
    - BARRETT_MULTIPLIER = 20159 = ⌊2^26 / 3329 + 1/2⌋
    - INVERSE_OF_MODULUS_MOD_MONTGOMERY_R = 62209 = -q⁻¹ mod R
-/

/- **L0.1 `vector.portable.arithmetic.get_n_least_significant_bits`** — masking primitive.
    [Upgrade status: post already equality-form, 0 LOC delta]

    Hax requires (`vector/portable/arithmetic.rs:26-32`): `n ≤ 16`.

    [F*-port: `Vector.Portable.Arithmetic.get_n_least_significant_bits`
     — upstream proof is a 20-line `calc` chain via `logand_mask_lemma`;
     Lean version compresses to a single `bv_decide` after `Std.U32.bv_eq_imp_eq`.]

    ## Sketch
    Trivial: `value & ((1 << n) - 1)` produces a value in `[0, 2^n)`.
    Close with `apply Std.U32.bv_eq_imp_eq; bv_decide`.

    ## Depends on
    - (leaf)

    ## Complexity tier
    bv-decide-close (~2 hours)
-/
/- Triple (extraction PRESENT — generated def is
   `libcrux_iot_ml_kem.vector.portable.arithmetic.get_n_least_significant_bits`
   in `Extraction/Funs.lean`):
@[spec]
theorem get_n_least_significant_bits_spec
    (n : Std.U8) (value : Std.U32) (hn : n.val ≤ 16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.get_n_least_significant_bits n value
    ⦃ ⇓ r => ⌜ r.val < 2 ^ n.val ∧ r.val = value.val % (2 ^ n.val) ⌝ ⦄ := by
  sorry
-/
-- L0.1 get_n_least_significant_bits_spec closed in Equivalence/L0_FieldArith.lean
-- (S03 commit 82ac1bf; staged `_eq_ok` + `interval_cases n.val <;> decide` mask;
-- 0 axioms beyond propext / Classical.choice / Quot.sound).

/- **L0.2 `vector.portable.arithmetic.barrett_reduce_element`** — signed Barrett reduction.
    [Upgrade status: needs +20 LOC corollary; M.1 def required]

    Hax pre (`vector/portable/arithmetic.rs:260`): `Spec.Utils.is_i16b 28296 value`,
    i.e. `value.val.natAbs ≤ 28296`.
    Hax post (`vector/portable/arithmetic.rs:261-262`):
    `Spec.Utils.is_i16b 3328 result ∧ result ≡ value (mod 3329)`,
    i.e. `result.val.natAbs ≤ 3328 ∧ (result.val - value.val) % 3329 = 0`.

    [F*-port: `Vector.Portable.Arithmetic.barrett_reduce_element`
     (lines 319–356, `--z3rlimit 150`). The F* proof is a 5-step `calc`
     using `lemma_mod_sub_distr` + `cancel_mul_mod` + 4 `assert` bounds
     on the quotient. Lean version: `hax_mvcgen` + ~2 `have` blocks
     using `Int.emod_sub_emod_cancel` + the closed-form quotient bound
     `barrett_quot_bound` (a fresh helper proved by `omega` after
     `interval_cases`). Est ~4 hours.]
    [F*-bound: Libcrux_ml_kem.Vector.Portable.Arithmetic.fsti `barrett_reduce_element`:
     pre `is_i16b 28296 value`, post `is_i16b 3328 result ∧ v r % 3329 = v value % 3329`.]

    ## Sketch
    Bound the quotient `q = (value · 20159 + 2^25) >>> 26` analytically.
    Show `result = value - q · 3329` differs from `value` by a multiple
    of 3329 (congruence is automatic). For the |result| ≤ q/2 bound,
    use `scalar_tac +nonLin` on the closed-form quotient.

    ## Depends on
    - (leaf), Util.Montgomery.barrett_quot_bound (new helper)

    ## Complexity tier
    scalar-tac-close (nonlinear) — ~4 hours
-/
/- Triple (extraction exists in Funs.lean but blocked by (a)):
@[spec]
theorem barrett_reduce_element_spec
    (value : Std.I16) (hb : value.val.natAbs ≤ 28296) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element value
    ⦃ ⇓ r => ⌜ modq_eq r.val value.val 3329
              ∧ r.val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/
-- L0.2 barrett_reduce_element_spec closed in Equivalence/L0_FieldArith.lean
-- (S03 commit f050fef; Int-level core via keystone 20159*3329 = 2^26 + 447,
-- 439 LOC, axiom-clean; flagged for follow-up golf to bv_decide form).

/- **L0.3 `vector.portable.arithmetic.montgomery_reduce_element`** — signed Montgomery reduction.
    [Upgrade status: needs +30 LOC corollary; M.1 def required]

    Hax pre (`vector/portable/arithmetic.rs:348`): `Spec.Utils.is_i32b (3328 * pow2 16) value`,
    i.e. `value.val.natAbs ≤ 3328 * 2^16`.
    Hax post (`vector/portable/arithmetic.rs:349-352`):
    `Spec.Utils.is_i16b (3328 + 1665) result ∧
     v result * pow2 16 ≡ v value (mod 3329)` (the Montgomery reduction identity).

    [F*-port: `Vector.Portable.Arithmetic.montgomery_reduce_element`
     (lines 416–544, `--z3rlimit 300`). The headline F* result. Two
     adjacent ~25-line `calc` chains: (1) `(value - k·q) % 2^16 = 0`
     via the `(62209 · 3329) % 2^16 = 1` keystone, (2)
     `value_high - c ≡ value · 169 (mod q)` via the `(2^16 · 169) % 3329 = 1`
     keystone. Lean version using ZMod 3329 + ZMod (2^16) casts: ~30
     lines. The whole thing is the deep-review §2's poster child for
     direct-port via Nat-keystone-with-`decide`. Est. 1 day.]

    ## Sketch
    Three steps reflect the Rust code: (i) `k = (value as i16) ·
    INVERSE_OF_MODULUS_MOD_MONTGOMERY_R` in i32; (ii) `c = (k as i16 ·
    FIELD_MODULUS) >> 16`; (iii) `value_high = value >> 16`; result
    is `value_high - c`. Prove congruence via the Montgomery identity
    `value - k·q · 2^{-16} ≡ value · R⁻¹ (mod q)` since `k ≡ -value/q
    (mod R)`. Bound via `|value_high| ≤ ⌈|value|/2^16⌉` + `|c| ≤ (q-1)/2`.

    ## Depends on
    - bridge `mont_R_inv_q` (B.1 below): `R · 169 ≡ 1 (mod q)`
    - new keystone `mont_qinv_R`: `(62209 · 3329) % 2^16 = 1` (add to Util.NumericKeystones)
    - new helper `Util.Montgomery.mont_reduce_int_form`

    ## Complexity tier
    needs-new-helper-tier (Util.Montgomery + Util.NumericKeystones) — ~30 lines Triple body, ~1 day total

    [F*-bound: Libcrux_ml_kem.Vector.Portable.Arithmetic.fsti `montgomery_reduce_element`:
     pre `is_i32b (3328 * pow2 16) value`, post `is_i16b (3328 + 1665) result ∧
     v result * pow2 16 % 3329 = v value % 3329`.]
-/
-- L0.3 montgomery_reduce_element_spec closed in Equivalence/L0_FieldArith.lean
-- (2026-05-22; campaign's first proof-bearing Triple; 0 axioms beyond
-- propext / Classical.choice / Quot.sound).

/- **L0.4 `vector.portable.arithmetic.montgomery_multiply_fe_by_fer`** — Montgomery multiply.
    [Upgrade status: needs +15 LOC corollary; depends on L0.3]

    Hax pre (`vector/portable/arithmetic.rs:464`): `Spec.Utils.is_i16b 1664 fer`,
    i.e. `fer.val.natAbs ≤ 1664`.
    Hax post (`vector/portable/arithmetic.rs:465-467`):
    `Spec.Utils.is_i16b 3328 result ∧
     v result * pow2 16 ≡ v fe * v fer (mod 3329)`
    (the Montgomery-multiply identity: result = fe·fer·R⁻¹ mod q).

    [F*-port: `Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer`
     (lines 549–555). Trivial F* composition (4 lines using
     `lemma_mul_i16b` + `montgomery_reduce_element`). Lean: a 4-line
     `@[spec]` body chaining L0.3. ~30 min once L0.3 is in.]

    ## Sketch
    Direct corollary of L0.3 applied to `product = fe · fer` (32-bit
    signed). Bound on product: `|fe|·|fer| ≤ 3328·3328 < 2^16·3328`.
    Hits the L0.3 precondition exactly.

    ## Depends on
    - L0.3 `montgomery_reduce_element_spec`

    ## Complexity tier
    mvcgen-trivial (~30 min)

    [F*-bound: Libcrux_ml_kem.Vector.Portable.Arithmetic.fsti `montgomery_multiply_fe_by_fer`:
     pre `is_i16b 1664 fer`, post `is_i16b 3328 result ∧
     v result * pow2 16 % 3329 = (v fe * v fer) % 3329`. Pre is asymmetric —
     only `fer` is bounded; `fe` can be any `i16`.]
-/
-- L0.4 montgomery_multiply_fe_by_fer_spec closed in Equivalence/L0_FieldArith.lean

/-! ============================================================
    # LAYER 1 — `PortableVector` element-wise ops

    Each function loops `for i in 0..16 { vec.elements[i] = f(...) }`.
    Uniform proof pattern: `mvcgen` unfolds the loop (Aeneas emits
    `loop_range_spec_usize`), per-element step calls the L0 spec for
    its `f`, the loop invariant is `∀ j < k, out[j] = f(in[j])`.

    The function list (from `vector/portable/arithmetic.rs`):
    `add, sub, negate, multiply_by_constant, bitwise_and_with_constant,
    shift_right, cond_subtract_3329, barrett_reduce,
    montgomery_multiply_by_constant, reducing_from_i32_array`. (The
    `compress` / `serialize` hierarchy is in Layer 5.)

    Organization tip for the closure file (e.g.
    `Equivalence/L1_VectorElementOps.lean`): write ONE proof macro
    `vector_elementwise_proof : <fn> <op-spec>` that takes the
    element-level `@[spec]` from L0 and produces the 16-element
    Triple. Then instantiate 10 times.

    [F*-port: all 10 are closed upstream in
     `Vector.Portable.Arithmetic.fst` lines 41–630 via a SINGLE
     fold_range pattern with a 2-conjunct invariant
     (`forall j < i. post j` / `forall j ≥ i. unchanged`). Lean's
     macro `IotMlKem.Util.PortableVector.elementwise_proof` factors
     this identically; each L1.x is a 5-line instantiation. Total
     L1 effort: ~2 days for the macro + 10 × 30 min.]

    All Layer-1 lemmas: extraction PRESENT as of the matrix-boundary
    extraction (commit `993b381`). The 10 underlying defs
    `vector.portable.arithmetic.{add, sub, negate, multiply_by_constant,
    bitwise_and_with_constant, shift_right, cond_subtract_3329,
    barrett_reduce, montgomery_multiply_by_constant,
    reducing_from_i32_array}` are in `Funs.lean`. Each Triple
    skeleton below labelled "extraction missing" should be re-read
    as "extraction PRESENT, Triple still to close".

    Each Triple skeleton below ports the upstream `traits.rs` `*_pre` /
    `*_post` predicate verbatim. `add_pre`/`sub_pre` are stated *on the
    elementwise sum/difference* (`is_intb (pow2 15 - 1) (v lhs[i] +
    v rhs[i])`) rather than separately on `lhs` / `rhs`, matching the
    upstream "callers establish the elementwise sum bound" idiom
    (traits.rs:633-646). The `*_post`s bundle the equation + the i16
    output bound under a single `forall` (traits.rs:648-663) to avoid
    splitting Z3's quantifier-instantiation budget.

    ## L1.1 `PortableVector.add` — pointwise wrapping_add.
    [Upgrade status: post already equality-form, 0 LOC delta]
    [F*-bound: traits.rs:640 `add_pre` + traits.rs:656 `add_post`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_add_spec
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Fin 16,
      ((lhs.elements[i].val + rhs.elements[i].val : Int).natAbs) ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.add lhs rhs
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                r.elements[i].val = lhs.elements[i].val + rhs.elements[i].val
              ∧ r.elements[i].val.natAbs ≤ 2^15 - 1 ⌝ ⦄ := by
  sorry
-/

/- ## L1.2 `PortableVector.sub` — pointwise wrapping_sub. Mirror of L1.1.
    [Upgrade status: post already equality-form, 0 LOC delta]
    [F*-bound: traits.rs:667 `sub_pre` + traits.rs:675 `sub_post` — same
     elementwise-difference-bound shape as L1.1.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_sub_spec
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Fin 16,
      ((lhs.elements[i].val - rhs.elements[i].val : Int).natAbs) ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.sub lhs rhs
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                r.elements[i].val = lhs.elements[i].val - rhs.elements[i].val
              ∧ r.elements[i].val.natAbs ≤ 2^15 - 1 ⌝ ⦄ := by
  sorry
-/

/- ## L1.3 `PortableVector.barrett_reduce` — each lane via L0.2.
    [Upgrade status: +10 LOC; depends on L0.2]
    Tier: loop-induction. Depends on L0.2.
    [F*-bound: traits.rs:763 `barrett_reduce_pre` (`is_i16b_array_opaque
     28296 vec`) + traits.rs:767 `barrett_reduce_post` (`is_i16b_array_opaque
     3328 result ∧ ∀ i, barrett_reduce_lane_post (vec[i]) (result[i])`).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_barrett_reduce_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 28296) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce vec
    ⦃ ⇓ r => ⌜ (∀ i : Fin 16, r.elements[i].val.natAbs ≤ 3328)
              ∧ (∀ i : Fin 16,
                  modq_eq r.elements[i].val vec.elements[i].val 3329) ⌝ ⦄ := by
  sorry
-/

/- ## L1.4 `PortableVector.montgomery_multiply_by_constant` — each lane via L0.4.
    [Upgrade status: needs +15 LOC; depends on L0.4 + M.2 Block A]
    Tier: loop-induction. Depends on L0.4.
    [F*-bound: traits.rs:781 `montgomery_multiply_by_constant_pre` (asymmetric:
     only `is_i16b 1664 c`, vec unconstrained — matches L0.4's pre asymmetry) +
     traits.rs:785 `montgomery_multiply_by_constant_post` (`is_i16b_array_opaque
     3328 result ∧ ∀ i, montgomery_multiply_lane_post (vec[i]) c (result[i])`).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_montgomery_multiply_by_constant_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16) (hc : c.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ (∀ i : Fin 16, r.elements[i].val.natAbs ≤ 3328)
              ∧ (∀ i : Fin 16,
                  modq_eq (r.elements[i].val * (2^16 : Int)) (vec.elements[i].val * c.val) 3329)
              ⌝ ⦄ := by
  sorry
-/

/- ## L1.5 `PortableVector.cond_subtract_3329` — per-element
    `if x ≥ 3329 then x - 3329 else x`.
    [Upgrade status: +10 LOC alias; full range + cong already proved]
    Tier: loop-induction.
    [F*-bound: traits.rs:743 `cond_subtract_3329_pre` (`is_i16b_array_opaque
     (pow2 12 - 1) vec`, i.e. `vec[i].val.natAbs ≤ 4095`) + traits.rs:747
     `cond_subtract_3329_post` (each lane: `v y = v x - 3329 ∨ v y = v x`
     ∧ `mod_q_eq (v y) (v x)`). Output bound implied: `v y ≤ pow2 12 - 1 - 3329
     = 766` on the subtract branch, `v y ≤ 4095` on the no-op branch.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_cond_subtract_3329_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 2^12 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329 vec
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                (r.elements[i].val = vec.elements[i].val - 3329 ∨
                 r.elements[i].val = vec.elements[i].val)
              ∧ modq_eq r.elements[i].val vec.elements[i].val 3329 ⌝ ⦄ := by
  sorry
-/

/- ## L1.6 `PortableVector.negate` — pointwise `wrapping_neg`.
    [Upgrade status: post already equality-form, 0 LOC delta]
    Tier: loop-induction.
    [F*-bound: traits.rs:684 `negate_pre` (`is_intb (pow2 15 - 1) (v vec[i])`,
     i.e. no `i16.MIN`) + traits.rs:691 `negate_post` (`v r = -v vec[i] ∧
     is_intb (pow2 15 - 1) (v r)`).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_negate_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.negate vec
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                r.elements[i].val = - vec.elements[i].val
              ∧ r.elements[i].val.natAbs ≤ 2^15 - 1 ⌝ ⦄ := by
  sorry
-/

/- ## L1.7 `PortableVector.multiply_by_constant` — pointwise
    `wrapping_mul(c)` (different from L1.4 — no Montgomery).
    [Upgrade status: post already equality-form, 0 LOC delta]
    Tier: loop-induction.
    [F*-bound: traits.rs:700 `multiply_by_constant_pre` (`is_intb (pow2 15 - 1)
     (v vec[i] * v c)`) + traits.rs:707 `multiply_by_constant_post`
     (`v r = v vec[i] * v c ∧ is_intb (pow2 15 - 1) (v r)`).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_multiply_by_constant_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hpre : ∀ i : Fin 16,
      (vec.elements[i].val * c.val : Int).natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                r.elements[i].val = vec.elements[i].val * c.val
              ∧ r.elements[i].val.natAbs ≤ 2^15 - 1 ⌝ ⦄ := by
  sorry
-/

/- ## L1.8 `PortableVector.bitwise_and_with_constant` — pointwise AND.
    [Upgrade status: post already equality-form (full bv eq), 0 LOC delta]
    Tier: loop-induction + bv_decide per element.
    [F*-bound: traits.rs:147 `bitwise_and_with_constant_constant_post`
     (`r = map_array (fun x => x &&& c) vec`). No precondition — the AND
     fits in i16 unconditionally. Note: no bound is propagated on `r`
     because callers track it via `Util.AndMask.lemma_and_mask_le` derived
     from `vector/portable/serialize.rs:23` (`v (x &&& y) ≤ v y` for non-neg).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_bitwise_and_with_constant_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant vec c
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                r.elements[i].bv = vec.elements[i].bv &&& c.bv ⌝ ⦄ := by
  sorry
-/

/- ## L1.9 `PortableVector.shift_right` — pointwise `>>` by const.
    [Upgrade status: post already equality-form (full bv eq), 0 LOC delta]
    Tier: loop-induction.
    [F*-bound: traits.rs:173-174 `shift_right` `requires SHIFT_BY ∈ [0, 16)`,
     `shift_right_post` (`r = map_array (fun x => x >>! shift_by) vec`).
     No output bound stated — caller derives `|r[i]| ≤ |vec[i]| >> SHIFT_BY`
     externally where needed.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_shift_right_spec
    (SHIFT_BY : Std.I32) (hs : 0 ≤ SHIFT_BY.val ∧ SHIFT_BY.val < 16)
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right SHIFT_BY vec
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                r.elements[i].bv = vec.elements[i].bv.sshiftRight SHIFT_BY.val.toNat ⌝ ⦄ := by
  sorry
-/

/- ## L1.10 `PortableVector.reducing_from_i32_array` — per-lane
    `montgomery_reduce_element` (L0.3) from a 16-element I32 slice.
    [Upgrade status: +15 LOC; depends on L0.3]
    Tier: loop-induction. Depends on L0.3.
    [F*-bound: hax-side pre `forall i. is_i32b (3328 * pow2 16) a[i]`
     (mirror of L0.3 pre, propagated per-lane), post bundles
     `forall i. is_i16b (3328 + 1665) r[i] ∧ v r[i] * pow2 16 ≡ v a[i] (mod 3329)`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_reducing_from_i32_array_spec
    (a : Aeneas.Std.Array Std.I32 16#usize)
    (hpre : ∀ i : Fin 16, a.val[i].val.natAbs ≤ 3328 * 2^16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array a
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                r.elements[i].val.natAbs ≤ 3328 + 1665
              ∧ modq_eq (r.elements[i].val * (2^16 : Int)) (a.val[i].val) 3329 ⌝ ⦄ := by
  sorry
-/

/-! ============================================================
    # LAYER 2 — NTT layer / butterfly steps

    The per-vector NTT step functions in `vector/portable/ntt.rs`:
    - `ntt_step` — single Cooley–Tukey butterfly (a, b) := (a + ζb, a - ζb)
       on i16 lanes
    - `ntt_layer_1_step, ntt_layer_2_step, ntt_layer_3_step` — bundled
      4-, 2-, 1-butterfly variants for the innermost NTT layers
    - `inv_ntt_step`, `inv_ntt_layer_{1,2,3}_step` — Gentleman–Sande
      inverse butterflies
    - `accumulating_ntt_multiply` (+ `_fill_cache`, `_use_cache`) —
      base-case multiplication in NTT domain (degree-2 polynomial mul
      mod (X² − ζ²)).

    Spec anchor: FIPS-203 Algorithm 9 (NTT) and Algorithm 12 (NTT⁻¹)
    base-case butterflies, written in the spec as `butterfly` /
    `inv_butterfly` (`specs/ml-kem/src/ntt.rs:197-243`).

    The "to_standard_domain" wrinkle: impl stays in Montgomery domain
    throughout NTT; the result of `ntt_at_layer_*` is `R ·
    canonical_NTT_coefficient mod q`. The spec stays in standard
    domain. Therefore the *element-wise* equivalence post here is
    "Montgomery-encoded result equals R · spec_result". See Layer 3
    for how this propagates through the loop driver.

    The Layer-2 Aeneas-extracted symbols DO exist in `Funs.lean`
    (lines 699..814), so these specs become real Triples first once
    blocker (a) is resolved.
-/

/- **L2.1 `vector.portable.ntt.ntt_step`** — single butterfly inside a
    PortableVector at indices (a_idx, b_idx) with the supplied ζ.
    [Upgrade status: +25 LOC; depends on M.2 Block A]

    Computes `t = montgomery_multiply(vec[b_idx], ζ)`, then
    `vec[b_idx] := vec[a_idx] - t`, `vec[a_idx] := vec[a_idx] + t`.

    Spec anchor: `Spec.butterfly (a, b, ζ) = (a + ζb, a - ζb) mod q`
    when all reads/writes are interpreted via `Spec.lift_field_mont`.

    [F*-port: `Vector.Portable.Ntt.ntt_step` (lines 16–103,
     `[@@ "opaque_to_smt"]`). F* uses two adjacent ~20-line calc
     chains for `a_plus_t` and `a_minus_t` via `lemma_mod_sub_distr` /
     `lemma_mod_add_distr`. Lean: `hax_mvcgen` + 1× L0.4 + 2×
     `Array.update_spec` + 2 `have` blocks using
     `Int.emod_sub_emod_cancel`. ~25 Lean lines, ~3 hours.]

    ## Sketch
    `unfold vector.portable.ntt.ntt_step; mvcgen`; the inner Montgomery
    multiply uses L0.4; then add / sub close by scalar_tac. The
    congruence post relates impl Montgomery-domain values to spec
    standard-domain values via the lift.

    ## Depends on
    - L0.4 `montgomery_multiply_fe_by_fer_spec`
    - BitMlKem.Commute Block-A `lemma_butterfly_fe_commute_plus/minus`

    ## Complexity tier
    mvcgen-trivial (~25 lines, ~3 hours)
-/
/- Triple (extraction blocked by (a)):
@[spec]
theorem ntt_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (a_idx b_idx : Std.Usize)
    (h_idx : a_idx.val < 16 ∧ b_idx.val < 16 ∧ a_idx.val ≠ b_idx.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_a : vec.elements[a_idx.val]!.val.natAbs ≤ 3 * 3328)
    (h_b : vec.elements[b_idx.val]!.val.natAbs ≤ 3 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta a_idx b_idx
    ⦃ ⇓ r => ⌜ (∀ k : Fin 16, k.val ≠ a_idx.val → k.val ≠ b_idx.val →
                  r.elements[k]! = vec.elements[k]!)
              ∧ r.elements[a_idx.val]!.val.natAbs ≤ 4 * 3328
              ∧ r.elements[b_idx.val]!.val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  sorry
-/
/- [F*-bound: vector/portable/ntt.rs:7-15 `ntt_step` pre: `v i < 16 ∧ v j < 16 ∧
   v i ≠ v j ∧ is_i16b 1664 zeta ∧ |vec[i]|, |vec[j]| ≤ 3·3328`, post:
   unchanged lanes + the two touched lanes are `≤ 4·3328`. (Inner butterfly
   pre is symmetric in both lanes because Montgomery-multiply absorbs one
   3328 → 3328 step and add/sub of two ≤3·3328 entries plus a ≤3328 lift
   yields the ≤4·3328 bound.)] -/

/- **L2.2 `vector.portable.ntt.ntt_layer_1_step`** — 4 butterflies on
    distinct (a, b, ζ) index pairs within one PortableVector at
    positions (0↔2, 1↔3, 4↔6, 5↔7) using ζ₀, ζ₀, ζ₁, ζ₁.
    [Upgrade status: +80 LOC; depends on L2.1 + M.2 Block B]

    [F*-port: `Vector.Portable.Ntt.ntt_layer_1_step` (lines 107–140).
     Upstream chains 8 `ntt_step` calls (actually 8 pairs in the
     deep-review reading) and closes via `reveal_opaque` on the trait
     post predicate `Spec.Utils.ntt_layer_1_butterfly_post`. Lean:
     chain 8× L2.1, then per-vector commute lemma from
     BitMlKem.Commute Block B. The deep-review §3.2 documents the
     `interval_cases (i / 8)` Lean trick that replaces the F* manual
     branch split (no need for 4 private helpers as in
     `Commute.Bridges`). ~4 h.]

    ## Sketch
    Unfold to 4 ntt_step calls; chain L2.1 four times.

    ## Depends on
    - L2.1
    - BitMlKem.Commute `lemma_ntt_layer_1_step_chunk_commutes`

    ## Complexity tier
    mvcgen-trivial (chains L2.1 × 4, ~4 hours)

    [F*-bound: vector/portable/ntt.rs:64-70 `ntt_layer_1_step` pre:
     `is_i16b 1664 zeta0..3 ∧ is_i16b_array (7*3328) vec.f_elements`, post:
     `is_i16b_array (8*3328) result.f_elements`. The chunked layer-1
     applies 4 butterflies, each adds one ≤3328 to the bound.]
-/
/- Triple skeleton (extraction blocked by (a)):
@[spec]
theorem ntt_layer_1_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (hz : zeta0.val.natAbs ≤ 1664 ∧ zeta1.val.natAbs ≤ 1664 ∧
          zeta2.val.natAbs ≤ 1664 ∧ zeta3.val.natAbs ≤ 1664)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 7 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, r.elements[i].val.natAbs ≤ 8 * 3328 ⌝ ⦄ := by
  sorry
-/

/- **L2.3 `ntt_layer_2_step`** — 2 butterflies. Depends on L2.1.
    [Upgrade status: +60 LOC; depends on L2.2]
    [F*-port: `Vector.Portable.Ntt.ntt_layer_2_step` lines 146–215;
     same shape as L2.2 with different index table.] ~3 hours.
    [F*-bound: vector/portable/ntt.rs:96-101 `ntt_layer_2_step` pre:
     `is_i16b 1664 zeta0,1 ∧ is_i16b_array (6*3328) vec`, post:
     `is_i16b_array (7*3328) result`.]
-/
/- Triple skeleton:
@[spec]
theorem ntt_layer_2_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 : Std.I16)
    (hz : zeta0.val.natAbs ≤ 1664 ∧ zeta1.val.natAbs ≤ 1664)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 6 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec zeta0 zeta1
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, r.elements[i].val.natAbs ≤ 7 * 3328 ⌝ ⦄ := by
  sorry
-/

/- **L2.4 `ntt_layer_3_step`** — 1 butterfly. Depends on L2.1.
    [Upgrade status: +40 LOC; depends on L2.2]
    [F*-port: ibid, same structure.] ~3 hours.
    [F*-bound: vector/portable/ntt.rs:120-124 `ntt_layer_3_step` pre:
     `is_i16b 1664 zeta ∧ is_i16b_array (5*3328) vec`, post:
     `is_i16b_array (6*3328) result`.]
-/
/- Triple skeleton:
@[spec]
theorem ntt_layer_3_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (hz : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 5 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec zeta
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, r.elements[i].val.natAbs ≤ 6 * 3328 ⌝ ⦄ := by
  sorry
-/

/- **L2.5 `inv_ntt_step`** — Gentleman–Sande inverse butterfly.
    Computes `(a, b) := (a + b, montgomery_multiply((a - b), ζ))`.
    Spec anchor: `Spec.inv_butterfly`. Mirror of L2.1. Depends on L0.4.
    [Upgrade status: +30 LOC; depends on L0.4 + M.2 Block A]
    [F*-port: `Vector.Portable.Ntt.inv_ntt_step` lines 221–280;
     forward uses `montgomery_multiply` on b then add/sub, inverse
     uses `barrett_reduce` on sum then `montgomery_multiply` on diff.]
    [F*-bound: vector/portable/ntt.rs:144-152 `inv_ntt_step` pre:
     `v i < 16 ∧ v j < 16 ∧ v i ≠ v j ∧ is_i16b 1664 zeta ∧
     is_i16b_array (4*3328) vec` (already-reduced lane bound on touched
     pair), post: `is_i16b_array (4*3328) result` (Gentleman–Sande sum
     barrett-reduces, mont-mult drops diff back).]
-/
/- Triple skeleton:
@[spec]
theorem inv_ntt_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (a_idx b_idx : Std.Usize)
    (h_idx : a_idx.val < 16 ∧ b_idx.val < 16 ∧ a_idx.val ≠ b_idx.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 4 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta a_idx b_idx
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, r.elements[i].val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  sorry
-/

/- **L2.6 `inv_ntt_layer_1_step`** — bundled 4 inverse butterflies.
    [Upgrade status: +80 LOC; depends on L2.5 + M.2 Block B]
    [F*-port: lines 285–360, mirror of L2.2.]
    [F*-bound: vector/portable/ntt.rs:189-194 `inv_ntt_layer_1_step` pre:
     `is_i16b 1664 zeta0..3 ∧ is_i16b_array 3328 vec`, post:
     `is_i16b_array (2*3328) result`.]
-/
/- Triple skeleton:
@[spec]
theorem inv_ntt_layer_1_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (hz : zeta0.val.natAbs ≤ 1664 ∧ zeta1.val.natAbs ≤ 1664 ∧
          zeta2.val.natAbs ≤ 1664 ∧ zeta3.val.natAbs ≤ 1664)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step
      vec zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, r.elements[i].val.natAbs ≤ 2 * 3328 ⌝ ⦄ := by
  sorry
-/

/- **L2.7 `inv_ntt_layer_2_step` / `inv_ntt_layer_3_step`** — analogous.
    [Upgrade status: +100 LOC; depends on L2.6]
    [F*-port: lines 365–430.]
    [F*-bound: vector/portable/ntt.rs:240-246 `inv_ntt_layer_2_step` pre:
     `is_i16b 1664 zeta0,1 ∧ is_i16b_array (2*3328) vec`, post:
     `is_i16b_array (4*3328) result`. Ditto for layer_3 with single zeta.]

    All [extraction exists, blocked by (a)]. Total L2.5–L2.7: ~6 hours.
-/
/- Triple skeletons:
@[spec]
theorem inv_ntt_layer_2_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 : Std.I16)
    (hz : zeta0.val.natAbs ≤ 1664 ∧ zeta1.val.natAbs ≤ 1664)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 2 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step vec zeta0 zeta1
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, r.elements[i].val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  sorry

@[spec]
theorem inv_ntt_layer_3_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (hz : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ i : Fin 16, vec.elements[i].val.natAbs ≤ 2 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step vec zeta
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, r.elements[i].val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  sorry
-/

/- **L2.8 `vector.portable.ntt.accumulating_ntt_multiply`** — base-case
    poly multiplication in NTT domain. The Rust impl computes a
    "running sum" of (a₀·b₀ + ζ²·a₁·b₁, a₀·b₁ + a₁·b₀) for each pair
    of coefficients (degree-2 polys mod X² − ζ²; FIPS-203 § 4.3.3,
    Algorithm 11). The accumulator is an `[I32; 256]` accumulator
    that gets folded via `montgomery_reduce_element` later. Three
    variants (with cache, fill cache, use cache) optimize the inner
    constant load.

    NOTE: `Spec.ntt_multiply_n` (ntt.rs:339-371) is generic over N to
    support BOTH N=256 (full `Spec.multiply_ntts`) AND N=16 (the
    impl's per-vector chunk). This is the spec being shaped to
    support impl decomposition. For L2.8 per-chunk, use a fresh
    M.1 def `bit_ntt_multiply_chunk`, NOT `Spec.ntt_multiply_n[N=16]`
    directly — the M.1 def lives on `MontPoly`-style data and
    composes cleanly with the rest of the bit-side spec; the
    equivalence between `bit_ntt_multiply_chunk` and the N=16
    instance of `Spec.ntt_multiply_n` lives in M.4 AlgEquiv.

    [F*-port: `Vector.Portable.Ntt.ntt_multiply_binomials` +
     `ntt_multiply` (lines 432–584; ~150 LOC F*). Each pair involves
     4× `montgomery_multiply` + 1× `montgomery_multiply` for the
     `a₁·b₁·ζ` term, with nested calc chains. The load-bearing helper
     is BitMlKem.Commute `lemma_base_case_mult_pair_commute`
     (upstream `Chunk.fst:587-625`). The trait-level
     `ntt_multiply_branch_post` is opaque (reveal_opaque trick at
     boundary). Lean: ~2 days including the commute side.]

    ## Sketch
    Per coefficient pair (0..16 vector lanes × 2 coeffs/lane):
    - mvcgen the inner pair loop
    - chain L0.4 (× 4 multiplies) + add + L0.3 (montgomery_reduce of
      the accumulator)
    - the spec post relates the resulting accumulator pair `(c₀, c₁)`
      to `Spec.ntt_multiply_base_case a b ζ`

    The cache variants are equivalent because the precomputed value
    is just `ζ² mod q` reused across calls; bridge via a `cache_eq`
    helper lemma.

    ## Depends on
    - L0.3, L0.4
    - new helper: `ntt_multiply_base_case_alg` (pure Lean spec of the
       degree-2 mul mod `X² − ζ²`)
    - BitMlKem.Commute `lemma_base_case_mult_pair_commute`

    ## Complexity tier
    needs-new-helper-tier (~2 days)

    [F*-bound: vector/portable/ntt.rs:339-345 `accumulating_ntt_multiply`
     pre: `v i < 8 ∧ is_i16b 1664 zeta ∧ is_i16b_array 3328 lhs.f_elements ∧
     is_i16b_array 3328 rhs.f_elements ∧ each accumulator lane within i32
     range`. Post: `accumulator[2i], accumulator[2i+1] ∈ [-2^31, 2^31)` and
     the two-lane formula equals the per-pair base-case mul mod (X²−ζ²).]
-/
/- Triple skeleton (extraction exists, blocked by (a)):
@[spec]
theorem accumulating_ntt_multiply_spec
    (i : Std.Usize) (hi : i.val < 8) (zeta : Std.I16) (hz : zeta.val.natAbs ≤ 1664)
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (acc : Aeneas.Std.Array Std.I32 16#usize)
    (hlhs : ∀ j : Fin 16, lhs.elements[j].val.natAbs ≤ 3328)
    (hrhs : ∀ j : Fin 16, rhs.elements[j].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply
      i zeta lhs rhs acc
    ⦃ ⇓ r => ⌜ -- per-pair accumulator stays within i32 (Montgomery-reducible later).
              True ⌝ ⦄ := by
  sorry
-/

/-! ============================================================
    # LAYER 3 — NTT / iNTT polynomial drivers

    The functions `ntt_at_layer_{1,2,3,4_plus,7}` and their inverse
    twins. Each iterates over the 16 vector lanes (and, for layer 4+,
    additionally over butterfly groups within a lane) calling the
    corresponding Layer-2 step. Plus the top-level
    `ntt_binomially_sampled_ring_element` and `ntt_vector_u` that
    string layers 7-1 together (a full 7-layer NTT).

    Hax annotations (`ml-kem/src/ntt.rs`):
    - `ntt_at_layer_1: requires *zeta_i == 63`,
      `ensures *future(zeta_i) == 127` (implicit), terminates
    - `ntt_at_layer_2: requires *zeta_i == 31`
    - `ntt_at_layer_3: requires *zeta_i == 15`
    - `ntt_at_layer_4_plus: requires layer ∈ [4,7] && *zeta_i ==
       (1 << (7 - layer)) - 1`
    - `ntt_binomially_sampled_ring_element: requires is_bounded_poly(3, re)`
    - `ntt_vector_u: requires is_bounded_poly(3328, re)`

    Both top-level NTTs end with `poly_barrett_reduce`, so the
    output is canonical-Montgomery (in `[-1665, 1665]`) at every
    coefficient.

    All Layer-3 NTT drivers ARE in `Funs.lean`. The iNTT half
    (`invert_ntt.*`) is not yet extracted.
-/

/- **L3.1 `ntt.ntt_at_layer_1`** — innermost NTT layer (loop of 16
    calls to `ntt_layer_1_step`). Increments `zeta_i` by 4 per
    iteration. Hax pre: `*zeta_i == 63`; post: `*future(zeta_i) == 127`.
    [Upgrade status: +80 LOC; depends on L2.2 + M.2 Block B/D]

    [F*-port: `Libcrux_ml_kem.Ntt.ntt_at_layer_1_` (lines 14–127,
     `--z3rlimit 800`, ~110 LOC). The architecturally critical
     pattern: F* uses `Classical.forall_intro aux + Seq.lemma_eq_intro`
     to lift the 16 per-vector posts to a per-poly equation via
     `Commute.Bridges.lemma_ntt_layer_1_step_to_hacspec`. Lean:
     `hax_mvcgen` driven loop with `loop_range_spec_usize`, then
     `Array.ext; intro i hi` + per-lane bridge from BitMlKem.Commute.
     Apply SKILL §5.7 Idiom 2 (`attribute [local irreducible]` on the
     bit_* lifts). Structural inspiration only — Lean rewrites the
     bridge from scratch, ~3 days per layer.]

    ## Sketch
    `apply Triple.of_entails_right + loop_range_spec_usize` with
    invariant `re.coefficients[k] = ntt_layer_1_applied
    (old_re.coefficients[k]) (zeta(64 + k*4), …, zeta(67 + k*4))
    ∧ zeta_i.val = 63 + (k+1) * 4 - 3` (mirror the
    `hax_lib::loop_invariant!` in the source). Per-iter:
    `Array.index_mut_usize_spec` + 4× `polynomial.zeta_spec` + L2.2.

    ## Depends on
    - L2.2 `ntt_layer_1_step_spec`
    - `polynomial.zeta_spec` (closes by `Array.index_usize_spec` on a
       128-element `@[irreducible]` table; the spec just exposes
       `r = zeta(i)` for `i < 128`)
    - BitMlKem.Spec `bit_ntt_layer_1`, `to_spec_poly_mont`
    - BitMlKem.Commute `ntt_layer_1_step_to_hacspec_lift`

    ## Complexity tier
    loop-induction (use §13.6 invariant-strengthening template) — ~3 days
-/
/- Triple (extraction exists, blocked by (a)):
@[spec]
theorem ntt_at_layer_1_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (bnd : Std.Usize)
    (h_zeta : zeta_i.val = 63)
    (h_bnd : bnd.val = 7 * 3328)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      (re.coefficients[i].elements[j].val.natAbs : Int) ≤ 7 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1 OpsInst zeta_i re bnd
    ⦃ ⇓ r => ⌜ r.1.val = 127
              ∧ (∀ i : Fin 16, ∀ j : Fin 16,
                  (r.2.coefficients[i].elements[j].val.natAbs : Int) ≤ 8 * 3328) ⌝ ⦄ := by
  sorry
-/
/- [F*-bound: ntt.rs:22-24 `ntt_at_layer_1` requires `is_bounded_poly (7*3328) re ∧
   *zeta_i == 63` (with `_initial_coefficient_bound == 7*3328`); ensures
   `is_bounded_poly (7*3328 + 3328) future(re)` and `*future(zeta_i) == 127`.
   Each layer-1 application bumps the per-coefficient bound by exactly 3328.] -/

/- **L3.2 `ntt.ntt_at_layer_2`** — same shape with zeta_i 31→63.
    [Upgrade status: +60 LOC; depends on L2.3 + M.2 Block B/D]
    **L3.3 `ntt.ntt_at_layer_3`** — same shape with zeta_i 15→31.
    [Upgrade status: +50 LOC; depends on L2.4 + M.2 Block B/D]
    Both ## Depends on L2.3/L2.4 + zeta_spec.
    [F*-port: `Libcrux_ml_kem.Ntt.ntt_at_layer_{2,3}_` (lines 132–336);
     structural duplication of L3.1.]
    ## Tier: loop-induction. ~2 days each.
    [F*-bound: ntt.rs:153-156 `ntt_at_layer_2` pre `is_bounded_poly (6*3328) re ∧
     *zeta_i == 31`, post `is_bounded_poly (7*3328) future(re)`.
     ntt.rs:266-268 `ntt_at_layer_3` pre `is_bounded_poly (5*3328) re ∧
     *zeta_i == 15`, post `is_bounded_poly (6*3328) future(re)`.]
-/
/- Triple skeletons:
@[spec]
theorem ntt_at_layer_2_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (bnd : Std.Usize)
    (h_zeta : zeta_i.val = 31) (h_bnd : bnd.val = 6 * 3328)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ 6 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2 OpsInst zeta_i re bnd
    ⦃ ⇓ r => ⌜ r.1.val = 63
              ∧ (∀ i : Fin 16, ∀ j : Fin 16,
                  r.2.coefficients[i].elements[j].val.natAbs ≤ 7 * 3328) ⌝ ⦄ := by
  sorry

@[spec]
theorem ntt_at_layer_3_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (bnd : Std.Usize)
    (h_zeta : zeta_i.val = 15) (h_bnd : bnd.val = 5 * 3328)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ 5 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3 OpsInst zeta_i re bnd
    ⦃ ⇓ r => ⌜ r.1.val = 31
              ∧ (∀ i : Fin 16, ∀ j : Fin 16,
                  r.2.coefficients[i].elements[j].val.natAbs ≤ 6 * 3328) ⌝ ⦄ := by
  sorry
-/

/- **L3.4 `ntt.ntt_at_layer_4_plus`** — generic outer NTT layer (the
    parameter `layer` is `∈ [4, 7]`; see Funs.lean line 396). Nested
    loop: outer over rounds, inner over `step_vec = (1 << layer) / 16`
    butterfly positions.
    [Upgrade status: +300 LOC; nested-loop invariant cascade;
     depends on L2.x + M.2 Block B/D]

    [F*-port: `Libcrux_ml_kem.Ntt.ntt_at_layer_4_plus` (lines
     363–477, ~115 LOC F*). The **largest single Triple in the
     campaign**, equivalent to SHA-3's `keccakf1600_loop`. Nested-loop
     invariant with strengthened post (§5.7 Idiom 3) including
     `r.zeta_i.val`. Lean: 100-150 lines, ~1.5 weeks. Structural
     inspiration only; the F* prenex `forall i, forall j, if` doesn't
     transfer cleanly to Triple-monadic form.]

    ## Sketch
    Two-level loop induction. Outer loop invariant: `zeta_i =
    (1 << (7 - layer)) - 1 + k` where `k` is the round counter.
    Inner loop invariant: butterflies have been applied to lanes
    `[a_offset, a_offset+j) × [b_offset, b_offset+j)`. Per-inner-iter:
    `ntt_layer_int_vec_step_spec` (a helper to write that uses L0.4
    + `Vector::add` / `Vector::sub` specs from L1.1 / L1.2).

    ## Depends on
    - new helper `ntt_layer_int_vec_step_spec` (the Aeneas-extracted
       function `ntt.ntt_layer_int_vec_step` is in Funs.lean line 290)
    - L0.4, L1.1, L1.2
    - BitMlKem.Commute layer-N forward bridge

    ## Complexity tier
    loop-induction (nested; expect 100-150 lines, ~1.5 weeks)

    [F*-bound: ntt.rs:385-396 `ntt_at_layer_4_plus` pre:
     `is_bounded_poly (_initial_coefficient_bound) re ∧
     _initial_coefficient_bound ≤ 5*3328 ∧
     *zeta_i == (1 << (7 - layer)) - 1 ∧ layer ∈ [4, 7]`,
     post: `is_bounded_poly (_initial_coefficient_bound + 3328) future(re) ∧
     *future(zeta_i) = old(*zeta_i) + (steps_per_round)`. Same per-call
     +3328 bound bump as L3.1–L3.3.]
-/
/- Triple skeleton:
@[spec]
theorem ntt_at_layer_4_plus_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (layer zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (bnd : Std.Usize)
    (h_layer : 4 ≤ layer.val ∧ layer.val ≤ 7)
    (h_zeta : zeta_i.val = (1 <<< (7 - layer.val)) - 1)
    (h_bnd : bnd.val ≤ 5 * 3328)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ bnd.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus OpsInst layer zeta_i re bnd
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.2.coefficients[i].elements[j].val.natAbs ≤ bnd.val + 3328 ⌝ ⦄ := by
  sorry
-/

/- **L3.5 `ntt.ntt_at_layer_7`** — outermost layer (no zeta_i).
    [Upgrade status: +80 LOC; depends on L1.7/1.1/1.2 + M.2 Block A]

    Uses `Vector::multiply_by_constant(-1600)` (the Montgomery
    encoding of ζ¹ = ζ_512 with a sign trick) and add/sub. No
    zeta_i — single fixed multiplier.

    [F*-port: `Libcrux_ml_kem.Ntt.ntt_at_layer_7_` (lines 478–566,
     ~90 LOC). Single loop with `Vector::multiply_by_constant` +
     `Vector::add` + `Vector::sub`. Bridge via Block-A
     `lemma_butterfly_fe_commute_plus/minus`. Lean: ~3 days
     structural-inspiration port.]

    ## Sketch
    Single-loop induction; per-iter:
    `Vector::multiply_by_constant` (L1.7) + `Vector::add` (L1.1) +
    `Vector::sub` (L1.2).

    ## Depends on
    - L1.7, L1.1, L1.2
    - BitMlKem.Commute Block-A butterfly commutes

    ## Complexity tier
    loop-induction (~3 days)

    [F*-bound: ntt.rs:473-474 `ntt_at_layer_7` pre: `is_bounded_poly 3 re`
     (binomially-sampled CBD bound, |x| ≤ η ≤ 3); post:
     `is_bounded_poly 4803 future(re)` (`= 3 + 4800 = 3 + |mont(zeta_7)|·k`,
     where mont(zeta_7) = -1600). The +4800 bump reflects the lone-multiplier
     layer with no barrett reduce at the end.]
-/
/- Triple skeleton:
@[spec]
theorem ntt_at_layer_7_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ 3) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_7 OpsInst re
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 4803 ⌝ ⦄ := by
  sorry
-/

/- **L3.6 `ntt.ntt_binomially_sampled_ring_element`** — full 7-layer
    NTT composed as `ntt_at_layer_7 → 4_plus(6) → 4_plus(5) →
    4_plus(4) → 3 → 2 → 1 → poly_barrett_reduce`. Spec anchor:
    `Spec.ntt(p)` on the spec polynomial `Spec.lift_poly_mont(p)`
    (Montgomery → standard-domain).

    [F*-port: `Libcrux_ml_kem.Ntt.ntt_binomially_sampled_ring_element`
     (Ntt.fst:567+, ~80 LOC). Pure composition; each step's post is
     the next step's pre. Lean: direct port (composition only) via
     7-step `hax_mvcgen` chain + Spec.ntt definition. ~3 days.]

    ## Sketch
    The bridge proof. Chain L3.1–L3.5 + a closing
    `poly_barrett_reduce` spec (L6.1). Each layer-step output is the
    input to the next.

    The Montgomery / standard-domain bridge: define
    `Spec.lift_poly_mont(p)` as `Spec.lift_poly(p) · pointwise R⁻¹
    (mod q)` where R = 2^16 mod q = 2285. Since spec uses
    standard-domain values throughout, and impl carries `R ·
    canonical_value mod q`, matching spec to impl needs a single
    `× R⁻¹` factor folded into the lift. This is precisely
    `BitMlKem.Spec.to_spec_poly_mont`.

    ## Depends on
    - L3.1, L3.2, L3.3, L3.4, L3.5
    - L6.1 `PolynomialRingElement.poly_barrett_reduce_spec`
    - `Spec.ntt`, `BitMlKem.Spec.to_spec_poly_mont`
    - bridge `mont_R_inv_q` (B.1)

    ## Complexity tier
    algebraic-close-required (Montgomery↔standard bridge) — ~3 days

    [F*-bound: ntt.rs:517-518 `ntt_binomially_sampled_ring_element` pre:
     `is_bounded_poly 3 re` (CBD η ≤ 3); post: `is_bounded_poly 3328
     future(re)` (final `poly_barrett_reduce` collapses the running
     7-layer bound down to canonical 3328).]
-/
/- Triple skeleton (Phase-1 BOUND-ONLY target):
@[spec]
theorem ntt_binomially_sampled_ring_element_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ 3) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element OpsInst re
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/
/- Triple skeleton (FUNCTIONAL-CORRECTNESS UPGRADE, Phase 5 target):
   Equality post anchored against `Spec.ntt` (NOT wrapped in
   `Spec.poly_barrett_reduce` — that's a no-op shim per the D9
   spec-shim audit; `Spec.lift_poly_mont` already canonicalizes).
@[spec]
theorem ntt_binomially_sampled_ring_element_spec_upgraded
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ 3) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element OpsInst re
    ⦃ ⇓ r => ⌜ Spec.ntt (Spec.lift_poly_mont re) = Spec.lift_poly_mont r
              ∧ ∀ i : Fin 16, ∀ j : Fin 16,
                  r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- **L3.7 `ntt.ntt_vector_u`** — same shape as L3.6 with different
    initial coefficient bound + initial zeta_i = 0 (skip layer 7).
    [F*-port: `Libcrux_ml_kem.Ntt.ntt_vector_u`, ~80 LOC F*; mirror
     of L3.6.] Tier: algebraic-close-required, ~3 days.
    [F*-bound: ntt.rs:560-561 `ntt_vector_u` pre: `is_bounded_poly 3328 re`
     (already-decompressed); post: `is_bounded_poly 3328 future(re)`
     (terminal barrett-reduce). Same +3328-per-layer ladder as L3.6
     but starting from a tighter initial bound.]
-/
/- Triple skeleton (Phase-1 BOUND-ONLY target):
@[spec]
theorem ntt_vector_u_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_vector_u OpsInst re
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/
/- Triple skeleton (FUNCTIONAL-CORRECTNESS UPGRADE, Phase 5 target):
   Equality post against `Spec.ntt` directly (no `Spec.poly_barrett_reduce`
   wrapper, per the D9 spec-shim audit).
@[spec]
theorem ntt_vector_u_spec_upgraded
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_vector_u OpsInst re
    ⦃ ⇓ r => ⌜ Spec.ntt (Spec.lift_poly_mont re) = Spec.lift_poly_mont r
              ∧ ∀ i : Fin 16, ∀ j : Fin 16,
                  r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- **L3.8 `invert_ntt_montgomery`** — full 7-layer iNTT.
    [CORRECTED 2026-05-23: was anchored against `Spec.ntt_inverse`,
     and bound post said `≤ 3328`. Both were bugs — see audit notes.]
    Spec anchor: `Spec.ntt_inverse_butterflies(p)`.

    L3.8 anchors against `Spec.ntt_inverse_butterflies`
    (specs/ml-kem/src/invert_ntt.rs:129-138), which is FIPS-203
    Alg 9 lines 3-8 *without* the terminal `· 128⁻¹`. This matches
    the impl's `invert_ntt_montgomery` exactly. The deferred
    `· 128⁻¹` factor lives in L6.2 / L6.4 where the
    `montgomery_multiply 1441 = R · (1/128 mod q)` step actually
    happens — NOT inside L3.8.

    Note: the `bit_intt_mont_form` opaque-predicate detour
    referenced by older Plan drafts is no longer needed and has
    been dropped — `Spec.ntt_inverse_butterflies` is a clean
    direct anchor.

    [F*-port: `Libcrux_ml_kem.Invert_ntt.fst` (~700 LOC). The
     impl's `invert_ntt_montgomery` does NOT apply the terminal
     `1/128` (that's deferred to L6.2 / L6.4). It also does NOT
     apply a terminal barrett reduce, so the K-scaled input bound
     survives plus a per-INTT-layer +3328 growth. The keystone
     bridge for L6.4's downstream finalize is
     `lemma_intt_mont_finalize_fe` (upstream Chunk.fst:1703) — port
     via ZMod 3329 cast in ~10 Lean lines, lives in M.2 Block C.
     ~4 days for L3.8 itself (bound-only post; functional post is
     a Phase-5 follow-up against `Spec.ntt_inverse_butterflies`).]
    Tier: algebraic-close-required (~4 days).
    [extraction PRESENT for invert_ntt.*: invert_ntt_at_layer_{1,2,3,4_plus},
     invert_ntt_montgomery, inv_ntt_layer_int_vec_step_reduce are in
     `Funs.lean` since commit `993b381`.]
    [F*-bound: invert_ntt.rs:660-665 `invert_ntt_montgomery` pre:
     `K ≤ 4 ∧ is_bounded_poly (K*3328) re` (poly-vector accumulated
     summand from K matrix products); post the impl alone gives
     `is_bounded_poly (K*3328 + 3328) future(re)` (impl performs
     no terminal barrett or 1/128 reduce, so K-scaled input bound
     survives + per-INTT-layer +3328 growth). The downstream
     L6.4 `subtract_reduce` is what collapses to 3328.]
-/
/- Triple skeleton [CORRECTED 2026-05-23: bound `≤ 3328` was wrong
   (no terminal barrett in the impl); spec anchor `Spec.ntt_inverse`
   was wrong (should be `Spec.ntt_inverse_butterflies`).]:
@[spec]
theorem invert_ntt_montgomery_spec
    {Vector : Type} (K : Std.Usize) (hK : K.val ≤ 4)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_pre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ K.val * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery OpsInst K re
    -- Bound is K*3328 + 3328 because the impl does NO terminal barrett
    -- or 1/128 reduce; the K-scaled input bound survives + the
    -- per-INTT-layer +3328 growth.
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ K.val * 3328 + 3328 ⌝ ⦄ := by
  sorry
-/

/-! ============================================================
    # LAYER 4 — Sampling

    Two distinct domains:
    1. **Rejection sampling** for matrix A (FIPS-203 Algorithm 6 /
       SampleNTT). `sample_from_xof + rej_sample` — picks 12-bit
       chunks from a Keccak XOF stream and keeps those `< 3329`.
    2. **CBD sampling** (centered binomial) for s, e, r, e1, e2
       (Algorithm 7 / SamplePolyCBD). PRF outputs bytes, each pair of
       2η bits becomes a coefficient in [-η, η].

    The XOF/PRF underneath both is SHA-3 (SHAKE128 / SHAKE256), which
    we **assume verified** at the `LibcruxIotSha3` boundary (the
    proven theorem `keccak.keccak_keccak_spec` couples it to the
    hacspec sponge).

    [F*-port status: **OUT OF SCOPE for direct port** (deep-review §2,
     Layer 4). Upstream files
     `Vector.Portable.Sampling.fst` (62 LOC, panic-free only) and
     `Sampling.fst` (556 LOC, panic-free only with multiple
     `admit () (* Panic freedom *)` at top level) provide NO FC
     content. The `rej_sample` body has only a loop invariant on
     length + value bounds; no spec equation. **Lean must write the
     FC spec relations from scratch**, including the SHA-3 sponge
     coupling. Est. 2–3 weeks for L4 (independent of any upstream
     proof work). Plan accordingly.]

    [extraction status, post-2026-05-22]:
    - L4.1 `vector.portable.sampling.rej_sample`: PRESENT.
    - L4.2 `sampling.sample_from_xof`: PRESENT (pulled in via
      `ntt::ntt_binomially_sampled_ring_element` transitive reachability).
    - L4.3 `sampling.sample_from_binomial_distribution`: MISSING
      (top-level CBD sampler; only `sample_from_uniform_distribution_next`
      and `sample_from_xof` come in via reachability — the CBD sampler
      is invoked from `ind_cpa::sample_vector_cbd_then_ntt` which is
      outside the current matrix boundary).

    ## L4.1 `vector.portable.sampling.rej_sample` — per-vector
    rejection sampling. Takes 24 bytes, returns up to 16 sampled
    coefficients + accepted count. Spec anchor:
    `Spec.rej_sample_step(bytes)`. 8-iter loop; per iter extract two
    12-bit candidates `d1, d2` from `(b₀ | b₁<<8 | b₂<<16)` via L0.1,
    accept if `< 3329`. Depends on L0.1, `Spec.rej_sample_step`.
    Tier: loop-induction.
    [F*-bound: vector/portable/sampling.rs:8-9 `rej_sample` pre:
     `a.len() == 24 ∧ result.len() == 16`, post: `future(result).len() ==
     result.len() ∧ res ≤ 16 ∧ ∀ j < res, 0 ≤ result[j] ∧ result[j] < 3329`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem rej_sample_spec
    (bytes : Aeneas.Std.Slice Std.U8) (out : Aeneas.Std.Slice Std.I16)
    (h_bytes : bytes.val.length = 24) (h_out : out.val.length = 16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.sampling.rej_sample bytes out
    ⦃ ⇓ r => ⌜ r.1.val ≤ 16
              ∧ r.2.val.length = 16
              ∧ ∀ j : Fin r.1.val.toNat, 0 ≤ r.2.val[j]!.val ∧ r.2.val[j]!.val < 3329 ⌝ ⦄ := by
  sorry
-/

/- ## L4.2 `sampling.sample_from_xof` — drives L4.1 over SHAKE128
    stream until 256 coefficients accepted. Spec anchor:
    `Spec.sample_ntt`. Couples to
    `LibcruxIotSha3.Sponge.Shake.shake128_spec` for the bytes.
    Tier: loop-induction + SHA-3 coupling.
    [F*-bound: PANIC-FREE-ONLY in upstream `Sampling.fst` (admits at
     `admit () (* Panic freedom *)`). FC bound = "each output
     polynomial is_bounded_poly 3328" is the Lean campaign's open
     obligation; we state the panic-free shape (Result is .ok) plus
     the per-coefficient bound 0 ≤ coeff < 3329 as our target post.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem sample_from_xof_spec
    {Vector : Type} (K : Std.Usize) (hK : K.val ≤ 4)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (seeds : Aeneas.Std.Array (Aeneas.Std.Array Std.U8 34#usize) K) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.sampling.sample_from_xof OpsInst seeds
    ⦃ ⇓ r => ⌜ ∀ k : Fin K.val,
                ∀ i : Fin 16, ∀ j : Fin 16,
                  0 ≤ r[k]!.coefficients[i].elements[j].val
                ∧ r[k]!.coefficients[i].elements[j].val ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- ## L4.3 `sampling.sample_poly_cbd` — centered binomial. Per byte:
    extract bits via shift+mask; centered sum in [-η, η]. Spec
    anchor: `Spec.sample_poly_cbd eta prf_output`.
    Tier: loop-induction.
    [F*-bound: sampling.rs:328-331 `sample_from_binomial_distribution`
     pre: `(ETA == 2 ∨ ETA == 3) ∧ randomness.len() == ETA * 64`;
     post: `is_bounded_poly 3 result ∧
     poly_to_spec result == Hacspec.Sampling.sample_poly_cbd ...`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem sample_from_binomial_distribution_spec
    {Vector : Type} (ETA : Std.Usize)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (randomness : Aeneas.Std.Slice Std.U8)
    (h_eta : ETA.val = 2 ∨ ETA.val = 3)
    (h_rnd : randomness.val.length = ETA.val * 64) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.sampling.sample_from_binomial_distribution OpsInst ETA randomness
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 3 ⌝ ⦄ := by
  sorry
-/

/-! ============================================================
    # LAYER 5 — Compress / Decompress / Byte-encode / Byte-decode

    The bit-packing layer that maps `[FieldElement; 256]` ↔ byte
    arrays. Each `serialize_D` packs 256 coefficients into 32·D bytes
    using D-bit fields; `deserialize_D` does the inverse.

    Spec anchor: `Spec.byte_encode<32·D, 256·D>` and
    `Spec.byte_decode` (`specs/ml-kem/src/serialize.rs:119, 200`).

    These are the LARGEST set of Triples (12 fns × {ser, deser} = 24,
    most non-trivial because of bit-shifting and packing). Each
    serialize_D is a single 16-iteration loop over PortableVector
    lanes that packs the lane's 16 elements into `D·2` bytes.

    Compress / decompress: `compress_d(fe, d) = ((fe · 2^d + q/2) / q)
    mod 2^d` (Algorithm 4); `decompress_d(fe, d) = (fe · q + 2^(d-1))
    / 2^d` (Algorithm 5). Closed via `scalar_tac +nonLin` + arithmetic
    inequality bounds.

    [F*-port status (deep-review §2, Layer 5):
     - **L5.1–L5.3** (`compress_*`, `decompress_*` in
       `Vector.Portable.Compress.fst`, 412 LOC): integer-level proofs
       are ✅ closed upstream (e.g. `compress_message_coefficient` has
       a 3-case split on `fe < 833`, `833 ≤ fe ≤ 2496`, `fe > 2496`).
       The vector-level wraps carry `admit (* Panic freedom *)` only;
       per-element FE-commute bridges in `Commute.Chunk.fst:1014+` are
       provable but stated with `= ()`. Lean ports the integer-level
       3-case splits via `decide` after `interval_cases`. **Direct
       port** at integer level, L1-macro wrap at vector level. ~3 days
       total for L5.1–L5.3.
     - **L5.4 / L5.5** (`serialize_D` / `deserialize_D` for
       D ∈ {1,4,5,10,11,12} in `Vector.Portable.Serialize.fst`, 1835
       LOC): ✅ proved upstream via the **Meta-F* tactic**
       `Tactics.GetBit.prove_bit_vector_equality'`, a bit-position
       enumeration tactic. Lean equivalent is **`bv_decide`** —
       SAT-based, same shape, **faster**. Each ser/deser is `apply
       Std.BitVec.eq_imp_eq; bv_decide` after a ~50-line support
       library `Util.BVDecide` translating `bit_vec_of_int_t_array`
       into Lean's `BitVec` flatten. Total L5.4+L5.5 effort: ~1 week
       for all 12 proofs.]

    [extraction status, post-2026-05-22]:
    - `vector.portable.compress.{compress_1, compress, decompress_ciphertext_coefficient,
      compress_message_coefficient, compress_ciphertext_coefficient}`: PRESENT.
    - `vector.portable.serialize.{serialize_d, deserialize_d}` for d ∈ {1,4,5,10,11,12}:
      PRESENT (12 def pairs).
    - `serialize.deserialize_to_reduced_ring_element` (the per-poly variant): PRESENT.
    - `serialize.{serialize_uncompressed_ring_element, deserialize_to_uncompressed_ring_element,
      deserialize_ring_elements_reduced}` (the vector-wide / uncompressed variants):
      MISSING (outside matrix boundary; called from ind_cpa).

    ## L5.1 `compress_1` — d=1 (1 bit per coefficient).
    Tier: bv-decide-close.
    [F*-bound: vector/portable/compress.rs:29 `compress_message_coefficient`
     pre: `fe < FIELD_MODULUS` (u16); post: `(833 ≤ v fe ≤ 2496) ⇒ v result == 1
     ∧ (v fe ≤ 832 ∨ v fe ≥ 2497) ⇒ v result == 0`. Plus
     vector/portable/compress.rs:187-196 `compress_1` (vector wrap):
     pre `∀ i, v vec[i] ≥ 0 ∧ v vec[i] < FIELD_MODULUS`, post per-lane.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_compress_1_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Fin 16, 0 ≤ vec.elements[i].val ∧ vec.elements[i].val < 3329) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.compress.compress_1 vec
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                (833 ≤ vec.elements[i].val ∧ vec.elements[i].val ≤ 2496 →
                  r.elements[i].val = 1)
              ∧ ((vec.elements[i].val ≤ 832 ∨ vec.elements[i].val ≥ 2497) →
                  r.elements[i].val = 0) ⌝ ⦄ := by
  sorry
-/

/- ## L5.2 `compress<D>` — generic D ∈ {4, 5, 10, 11}.
    Tier: scalar-tac-close (nonlinear).
    [F*-bound: vector/portable/compress.rs:239-256 `compress<D>` pre:
     `D ∈ {4, 5, 10, 11} ∧ ∀ i, 0 ≤ vec[i] < FIELD_MODULUS`, post:
     `∀ i, 0 ≤ result[i] < 2^D ∧
     v result[i] = compress_d (v vec[i]) D` (the integer-level Algo 4 formula).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_compress_spec
    (COEFFICIENT_BITS : Std.U8) (h_bits : COEFFICIENT_BITS.val ∈ ({4,5,10,11} : Finset _))
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Fin 16, 0 ≤ vec.elements[i].val ∧ vec.elements[i].val < 3329) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.compress.compress COEFFICIENT_BITS vec
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                0 ≤ r.elements[i].val ∧ r.elements[i].val < 2 ^ COEFFICIENT_BITS.val ⌝ ⦄ := by
  sorry
-/

/- ## L5.3 `decompress_ciphertext_coefficient<D>` — inverse of L5.2.
    Tier: scalar-tac-close.
    [F*-bound: vector/portable/compress.rs:305-315 `decompress_ciphertext_coefficient<D>`
     pre: `∀ i, 0 ≤ vec[i] < 2^D`, post: `∀ i, 0 ≤ result[i] < FIELD_MODULUS
     ∧ v result[i] = decompress_d (v vec[i]) D` (the Algo 5 inverse formula).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_decompress_ciphertext_coefficient_spec
    (COEFFICIENT_BITS : Std.U8) (h_bits : COEFFICIENT_BITS.val ∈ ({4,5,10,11} : Finset _))
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Fin 16, 0 ≤ vec.elements[i].val ∧
                          vec.elements[i].val < 2 ^ COEFFICIENT_BITS.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
      COEFFICIENT_BITS vec
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                0 ≤ r.elements[i].val ∧ r.elements[i].val < 3329 ⌝ ⦄ := by
  sorry
-/

/- ## L5.4 `serialize_D` for D ∈ {1, 4, 5, 10, 11, 12} — pack 16
    field elements of bit width D into D·2 bytes.
    Tier: bv-decide-close (one per D).
    [F*-bound: vector/portable/serialize.rs:57-58 `serialize_1` /
     206-207 `serialize_4` / 360-361 `serialize_5` / 506-507 `serialize_10` /
     663-664 `serialize_11` / 811-812 `serialize_12`. Each pre:
     `∀ i, Rust_primitives.bounded inputs[i] D` (i.e. 0 ≤ x < 2^D);
     each post: bit-vector flatten equality
     `bit_vec_of_int_t_array result 8 == bit_vec_of_int_t_array inputs D`.]
-/
/- Triple skeleton (extraction missing) — one per D, shape identical:
@[spec]
theorem PortableVector_serialize_D_spec
    (D : Nat) (h_D : D ∈ ({1,4,5,10,11,12} : Finset Nat))
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Fin 16, 0 ≤ vec.elements[i].val ∧ vec.elements[i].val < 2 ^ D) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.serialize.«serialize_D» vec
    ⦃ ⇓ r => ⌜ r.val.length = 2 * D
              -- ∧ BitVec.flatten r.val 8 = BitVec.flatten (vec.elements.map .val) D
              ⌝ ⦄ := by
  sorry
-/

/- ## L5.5 `deserialize_D` for D ∈ {1, 4, 5, 10, 11, 12} — inverse
    of L5.4. Tier: bv-decide-close.
    [F*-bound: serialize.rs:123 `deserialize_1` / 289 `deserialize_4` /
     435 `deserialize_5` / 586 `deserialize_10` / 742 `deserialize_11` /
     893 `deserialize_12`. Each pre: `bytes.len() == 2*D`; each post:
     `∀ i, 0 ≤ result[i] < 2^D` (the bit-vector inverse identity).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem PortableVector_deserialize_D_spec
    (D : Nat) (h_D : D ∈ ({1,4,5,10,11,12} : Finset Nat))
    (bytes : Aeneas.Std.Slice Std.U8) (h_len : bytes.val.length = 2 * D) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.serialize.«deserialize_D» bytes
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16,
                0 ≤ r.elements[i].val ∧ r.elements[i].val < 2 ^ D ⌝ ⦄ := by
  sorry
-/

/- ## L5.6 `byte_encode (byte_decode x) = x` — round-trip identity at
    D=12 (needed for `public_key_modulus_check`, FIPS-203 §7.2).
    Tier: bv-decide-close + new pure-Lean Roundtrip helper.
    [F*-bound: derived corollary of L5.4 + L5.5 at D=12; no separate
     upstream lemma — F* tactic `prove_bit_vector_equality'` discharges
     both directions in one call. Lean: bv_decide on the composed
     map after a round-trip rewrite.]
-/

/-! ============================================================
    # LAYER 6 — Polynomial / vector composites

    Per-poly operations that loop over the 16 vectors of a
    `PolynomialRingElement`. Each is one `for i in 0..16 { … }` over
    the L1.x / L5.x specs, with a uniform invariant.

    These bridge between vector-level (L1/L5) and ring-element-level
    (L7/L8) Triples. The intermediate spec is `Spec.Polynomial = [FE;
    256]` and the post is "each block of 16 elements at offset i*16
    in the spec poly equals the L1.x application to
    `re.coefficients[i]`".

    [extraction PRESENT for L6.1-L6.4]:
    `PolynomialRingElement.{poly_barrett_reduce, add_message_error_reduce,
     add_error_reduce, add_standard_error_reduce, accumulating_ntt_multiply
     (+ _use_cache, _fill_cache), subtract_reduce, reducing_from_i32_array,
     from_i16_array}` — all in `Funs.lean` since commit `993b381`.

    [extraction missing for L6.5-L6.7]: `serialize_uncompressed_ring_element`,
    `deserialize_to_uncompressed_ring_element`, `deserialize_ring_elements_reduced`
    — outside the matrix boundary (called from ind_cpa). The per-poly
    `serialize.deserialize_to_reduced_ring_element` IS extracted and
    is the L6.6-equivalent at the per-poly level.
-/

/- **L6.1 `PolynomialRingElement.poly_barrett_reduce`** — apply
    `Vector::barrett_reduce` to each of the 16 lanes.

    Spec anchor: `Spec.poly_barrett_reduce(p)`.

    [F*-port: `Libcrux_ml_kem.Polynomial.poly_barrett_reduce`
     (Polynomial.fst:373–434, ~60 LOC). Invokes
     `Commute.Chunk.lemma_poly_barrett_reduce_commute` (~40 lines) +
     `lemma_poly_barrett_reduce_id` (~15 lines, says `barrett_reduce`
     is identity on the FE polynomial). Lean: direct port via
     BitMlKem.Commute. ~3 days (the commute lemmas are the bulk).]

    ## Sketch
    16-iter loop with L1.3 per iter. Invariant: `∀ k < i,
    re.coefficients[k] is barrett-reduced`.

    ## Depends on
    - L1.3 `PortableVector_barrett_reduce_spec`
    - `Spec.poly_barrett_reduce`
    - BitMlKem.Commute `lemma_poly_barrett_reduce_commute`, `_id`

    ## Complexity tier
    loop-induction (~3 days)
-/
/- Triple (extraction exists, blocked by (a)):
@[spec]
theorem PolynomialRingElement_poly_barrett_reduce_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (hpre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ 28296) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce OpsInst re
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/
/- [F*-bound: polynomial.rs:504-505 `poly_barrett_reduce` pre:
   `is_bounded_poly 28296 self`, post: `is_bounded_poly 3328 future(self)`.
   Each lane independently barrett-reduces (L1.3); the upper 28296 bound
   is the worst-case prior to barrett.] -/

/- **L6.2 `PolynomialRingElement.{add_error_reduce,
    add_message_error_reduce, add_standard_error_reduce}`** — the
    three fused-add-reduce variants. Spec anchors are the
    corresponding spec `add_*` in
    `specs/ml-kem/src/polynomial.rs:19-91`.

    NOTE (2026-05-22): an earlier Plan draft also listed
    `add_to_ring_element`, but the impl Rust source
    (`libcrux-iot/ml-kem/src/polynomial.rs`) does NOT have such a
    method on `PolynomialRingElement`; the only `add_*` on the impl
    type are the three fused-reduce variants. The
    `hacspec_ml_kem.polynomial.add_to_ring_element` spec function
    IS in the generated `HacspecMlKem` and gets used by the spec-
    side composition lemmas, but there is no impl Triple to prove
    here. (Plan's original 4-conjunct F*-bound block at
    `polynomial.rs:442-444` cited an outdated upstream where the
    impl had that method; libcrux-iot's impl inlines it into the
    fused-reduce variants.)

    [F*-port: `Libcrux_ml_kem.Polynomial.{add_*}` (Polynomial.fst:
     303–369, 570–928). `add_standard_error_reduce` is the longest at
     ~80 LOC F*. The keystone is `lemma_to_standard_domain_finalize_fe`
     (Commute.Chunk.fst:2060) which uses `(1353 * 169) % 3329 = 2285`
     + one `lemma_mod_mul_distr_r`. Lean: design the
     `bit_mont_form_lane` opaque predicate in M.1 + thread it through
     the loop invariant. The closing commute lemma is
     `lemma_add_standard_error_reduce_commute` from Chunk.fst:2176
     (~50 lines upstream, ~30 lines Lean via `Array.ext`). ~5 days for
     all 4 variants total.]

    ## Sketch
    Per-iter: L1.4 (`montgomery_multiply_by_constant 1441`) + L1.1
    (`add` × 1 or 2) + L1.3 (`barrett_reduce`). The fixed multiplier
    1441 = R · (1/128 mod q) absorbs the inverse NTT normalization
    that was deferred earlier in the impl.

    ## Depends on
    - L1.1, L1.3, L1.4
    - bridge `mont_1441_eq_inv128` (B.2), `mont_2285_eq_R_mod_q` (B.3),
      `mont_1353_eq_RR_mod_q` (B.4)
    - BitMlKem.Spec `bit_mont_form_lane` (opaque predicate, M.1)
    - BitMlKem.Commute `lemma_add_standard_error_reduce_commute`,
      `lemma_to_standard_domain_finalize_fe`

    ## Complexity tier
    loop-induction + algebraic-close-required (~5 days for all 4)

    [F*-bound:
     - polynomial.rs:755-756 `add_message_error_reduce` pre:
       `is_bounded_poly 3328 self ∧ is_bounded_poly 3328 message`, post:
       `is_bounded_poly 3328 result`.
     - polynomial.rs:821-822 `add_error_reduce` pre:
       `is_bounded_poly 7 error`, post:
       `is_bounded_poly 3328 future(self)`. (Note the *low* error bound 7 —
       error is fresh CBD output, η ≤ 3, but the impl bounds it loosely.)
     - polynomial.rs:933-934 `add_standard_error_reduce` pre:
       `is_bounded_poly 3328 error`, post:
       `is_bounded_poly 3328 future(self)`. (Self is post-NTT t̂, bounded
       3328 by accumulated matrix mul.)]
-/
/- Triple skeletons (L6.2 — 3 variants; `add_to_ring_element` has no
   impl Triple; see note above):
@[spec]
theorem PolynomialRingElement_add_message_error_reduce_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (myself message error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_self : ∀ i : Fin 16, ∀ j : Fin 16,
      myself.coefficients[i].elements[j].val.natAbs ≤ 3328)
    (h_msg : ∀ i : Fin 16, ∀ j : Fin 16,
      message.coefficients[i].elements[j].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce
      OpsInst myself message error
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry

@[spec]
theorem PolynomialRingElement_add_error_reduce_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (myself error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_err : ∀ i : Fin 16, ∀ j : Fin 16,
      error.coefficients[i].elements[j].val.natAbs ≤ 7) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
      OpsInst myself error
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry

@[spec]
theorem PolynomialRingElement_add_standard_error_reduce_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (myself error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_err : ∀ i : Fin 16, ∀ j : Fin 16,
      error.coefficients[i].elements[j].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
      OpsInst myself error
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- **L6.3 `PolynomialRingElement.accumulating_ntt_multiply`** (+
    `_fill_cache` / `_use_cache`) — NTT-domain polynomial
    multiplication. 16-iter loop over `Vector::accumulating_ntt_multiply`
    (L2.8) with the per-pair zeta values from
    `ZETAS_TIMES_MONTGOMERY_R[64 + 4i + {0,1,2,3}]`.

    Spec anchor: `Spec.multiply_ntts(a, b)` (the N=256 instance of
    `Spec.ntt_multiply_n`).

    NOTE: `Spec.ntt_multiply_n` (ntt.rs:339-371) is generic over N to
    support BOTH N=256 (full `Spec.multiply_ntts`) AND N=16 (the
    impl's per-vector chunk). For L6.3 anchor against
    `Spec.multiply_ntts` directly (the N=256 instance) — NOT against
    `Spec.ntt_multiply_n` at generic N. The per-chunk decomposition
    is internal to the impl and exposed via M.1's
    `bit_ntt_multiply_chunk`, not via the N=16 instance.

    [F*-port: `Libcrux_ml_kem.Polynomial.ntt_multiply`
     (Polynomial.fst:853–915). **WARNING**: upstream's
     `lemma_ntt_multiply_chunk_commutes` (Chunk.fst:1311) is
     `assume val` — the per-vector bridge to `N.ntt_multiply_n` is
     ADMITTED upstream. Lean has to *prove* (not admit) this wrap:
     write it as a 30-line `Classical.forall_intro`-equivalent
     `Array.ext` over 16 lanes invoking the per-pair Lemma. The
     deeper `lemma_base_case_mult_even_mod_core` (Chunk.fst:352,
     `--z3rlimit 400`) IS proved upstream and ports. ~1 week
     including the wrap proof.]

    ## Sketch
    Per-iter L2.8; the accumulator slice indexing
    `accumulator[i*16..(i+1)*16]` matches lane i of the result;
    invariant chains the `Spec.ntt_multiply` block-by-block.

    ## Depends on
    - L2.8
    - `Spec.ntt_multiply`
    - BitMlKem.Commute per-vector ntt_multiply wrap (Lean must prove what F* admits)

    ## Complexity tier
    structural-inspiration + new-proof (~1 week)

    [F*-bound: polynomial.rs:1011-1012 `ntt_multiply` pre:
     `is_bounded_poly 3328 myself ∧ is_bounded_poly 3328 rhs`, post:
     `is_bounded_poly 3328 result`. WARNING: upstream's per-vector
     wrap is `assume val` (Chunk.fst:1311); Lean port must prove this
     wrap; FC bound itself is closed at the integer-pair level.]
-/
/- Triple skeleton (extraction PRESENT — generated def is
   `polynomial.PolynomialRingElement.accumulating_ntt_multiply`; note
   the Triple takes an external `accumulator : Slice Std.I32` and
   mutates it, so the spec must be in terms of the accumulator slice
   contents, not a fresh return value. Original draft below assumed a
   return-by-value shape — re-read `Funs.lean` around the generated
   def before opening the proof):
@[spec]
theorem PolynomialRingElement_accumulating_ntt_multiply_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (myself rhs : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_self : ∀ i : Fin 16, ∀ j : Fin 16,
      myself.coefficients[i].elements[j].val.natAbs ≤ 3328)
    (h_rhs : ∀ i : Fin 16, ∀ j : Fin 16,
      rhs.coefficients[i].elements[j].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply OpsInst myself rhs
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- **L6.4 `PolynomialRingElement.subtract_reduce`** — `b ← (1441·b −
    a)`-reduce. Spec: `Spec.subtract_reduce(a, b)`.
    [F*-port: `Libcrux_ml_kem.Polynomial.subtract_reduce`
     (Polynomial.fst:438–569). The most intricate Layer 6 upstream
     lemma — `--z3rlimit 800 --ext context_pruning --split_queries
     always`, ~130 LOC. Threads `intt_mont_form_chunk` (Chunk.fst:1683)
     through the loop invariant; assembles via
     `lemma_subtract_reduce_commute` (Chunk.fst:1893, ~50 lines).
     Keystone: `lemma_intt_mont_finalize_fe` (Chunk.fst:1703) using
     `(1441 * 169) % 3329 = 512`. Plan.lean bridge B.2 is exactly
     this. Lean: ~150 lines, ~1 week. Pattern matches L6.2 structure
     but for INTT-Mont track.]
    Tier: loop-induction + algebraic-close-required (~1 week).
    [F*-bound: polynomial.rs:1106-1107 `subtract_reduce` pre:
     `is_bounded_poly 3328 self ∧ is_bounded_poly 3328 message` (where
     `message` is the post-INTT impl input that's `bit_intt_mont_form`),
     post: `is_bounded_poly 3328 result` (`1441·b - a`-reduce collapses
     down to canonical 3328).]
-/
/- Triple skeleton:
@[spec]
theorem PolynomialRingElement_subtract_reduce_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (myself message : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_self : ∀ i : Fin 16, ∀ j : Fin 16,
      myself.coefficients[i].elements[j].val.natAbs ≤ 3328)
    (h_msg : ∀ i : Fin 16, ∀ j : Fin 16,
      message.coefficients[i].elements[j].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce
      OpsInst myself message
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                r.coefficients[i].elements[j].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- **L6.5 `serialize_uncompressed_ring_element`** /
    **`compress_then_serialize_message`** /
    **`compress_then_serialize_ring_element`** — the byte serializers
    at ring-element granularity. Each is a 16-iter loop:
    `to_unsigned_field_modulus → Vector::compress_D → Vector::serialize_D`.

    Per-iter: L5.2 (compress_D) + L5.4 (serialize_D). The byte buffer
    is written via `Std.Array.update` over `serialized[D·2*i..D·2*(i+1)]`
    slices; `Std.Array.set_val_eq` simp lemmas collapse. Depends on
    L5.2, L5.4 + new helper `to_unsigned_field_modulus_spec`. Tier:
    loop-induction + bv-decide-close per element.
    [F*-bound: serialize.rs:16-18 `serialize_uncompressed_ring_element`
     pre: `is_bounded_vector 3328 a` (each coefficient in canonical
     positive range), post: `∀ i, result[i] is the D=12 byte-encoded
     coefficient`. Plus serialize.rs:27-28 `compress_then_serialize_message`
     pre: `is_bounded_poly 3328 re`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem serialize_uncompressed_ring_element_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (hpre : ∀ i : Fin 16, ∀ j : Fin 16,
      re.coefficients[i].elements[j].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element OpsInst re
    ⦃ ⇓ r => ⌜ r.val.length = 384 ⌝ ⦄ := by
  sorry
-/

/- **L6.6 `deserialize_*_ring_element`** — inverse of L6.5. Same
    structure with L5.3 + L5.5 chained. Tier: loop-induction.
    [F*-bound: serialize.rs:515-518 `deserialize_to_uncompressed_ring_element`
     pre: `serialized.len() == 384`, post: `is_bounded_poly 4095 result`
     (= 2^12 - 1, the raw D=12 bit-decoded output before mod-q reduction).]
-/
/- Triple skeleton:
@[spec]
theorem deserialize_to_uncompressed_ring_element_spec
    {Vector : Type}
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (serialized : Aeneas.Std.Slice Std.U8) (h_len : serialized.val.length = 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element OpsInst serialized
    ⦃ ⇓ r => ⌜ ∀ i : Fin 16, ∀ j : Fin 16,
                0 ≤ r.coefficients[i].elements[j].val
              ∧ r.coefficients[i].elements[j].val ≤ 4095 ⌝ ⦄ := by
  sorry
-/

/- **L6.7 `deserialize_ring_elements_reduced`** — outer K-loop over
    L6.6. Used by `ind_cpa::serialize_public_key` and
    `validate_public_key`. Tier: loop-induction.
    [F*-bound: serialize.rs:559-562 `deserialize_ring_elements_reduced` pre:
     `K ≤ 4 ∧ public_key.len() == K * 384`, post:
     `∀ i < K, is_bounded_vector 4095 result[i]` (raw decode bound; mod-q
     reduction is performed outside this fn by the caller).]
-/
/- Triple skeleton:
@[spec]
theorem deserialize_ring_elements_reduced_spec
    {Vector : Type} (K : Std.Usize) (hK : K.val ≤ 4)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (public_key : Aeneas.Std.Slice Std.U8)
    (h_len : public_key.val.length = K.val * 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced OpsInst K public_key
    ⦃ ⇓ r => ⌜ ∀ k : Fin K.val, ∀ i : Fin 16, ∀ j : Fin 16,
                0 ≤ r[k]!.coefficients[i].elements[j].val
              ∧ r[k]!.coefficients[i].elements[j].val ≤ 4095 ⌝ ⦄ := by
  sorry
-/

/-! ============================================================
    # LAYER 7 — Matrix-level building blocks

    The matrix ops in `matrix.rs`. These accumulate
    `PolynomialRingElement` values via L6.3
    (`accumulating_ntt_multiply`) followed by L6.2
    (`add_*_error_reduce`). Spec anchors are the FIPS-203 linear
    algebra expressions.

    Per-fn hax annotations all require `K ≤ 4` and bounded inputs.

    [F*-port: `Libcrux_ml_kem.Matrix.fst` (533 LOC, all closed
     upstream). Each is a K-loop invariant `is_bounded_polynomial_vector
     K bound result[..i]`. **Caveat**: L7.1 (sample_matrix_A)
     transitively depends on the L4 admit; until Lean writes L4 FC
     from scratch, L7.1 is blocked. L7.2–L7.5 are direct ports
     (compose L6.3 + L6.2 / L6.4 + L3.8). Total: ~1 week for L7.2–L7.5
     + L7.1 ≈ 1 week once L4 closes.]

    [extraction PRESENT for `matrix.*`: sample_matrix_A, sample_matrix_entry,
     compute_vector_u, compute_ring_element_v, compute_message, compute_As_plus_e,
     entry — all in `Funs.lean` since commit `993b381`.]

    ## L7.1 `sample_matrix_A` — generates `K × K` Â via SHAKE128.
    Spec: `Spec.expand_a(rho, transpose)`. Nested 2-level loop K × K.
    Per-iter: L4.2 + `PolynomialRingElement::from_i16_array_spec`
    (new). Depends on L4.2. Tier: nested loop-induction.
    [F*-bound: matrix.rs:18-21 `sample_matrix_A` pre: `K ≤ 4`; post:
     `∀ i < K, ∀ j < K, is_bounded_poly 3328 future(A_transpose)[i][j]`.
     (Note: sample output is non-negative ≤ 3328, suitable for direct
     consumption by NTT layers.)]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem sample_matrix_A_spec
    {Vector : Type} (K : Std.Usize) (hK : K.val ≤ 4)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (A_transpose : Aeneas.Std.Array (Aeneas.Std.Array
                     (libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) K) K)
    (seed : Aeneas.Std.Array Std.U8 34#usize) (transpose : Bool) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.sample_matrix_A OpsInst A_transpose seed transpose
    ⦃ ⇓ r => ⌜ ∀ i : Fin K.val, ∀ j : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
                r[i]![j]!.coefficients[a].elements[b].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- ## L7.2 `compute_As_plus_e` — `t̂ = Â◦ŝ + ê`. K-loop over inner
    `accumulating_ntt_multiply` calls + outer
    `add_standard_error_reduce`. Depends on L6.3, L6.2. Tier:
    loop-induction.
    [F*-bound: matrix.rs:233-240 `compute_As_plus_e` pre: `K ≤ 4 ∧
     (∀ i < K, is_bounded_poly 3328 error_as_ntt[i] ∧ is_bounded_poly 3328
     s_as_ntt[i] ∧ ∀ j < K, is_bounded_poly 3328 matrix_A[i][j])`;
     post: `∀ i < K, is_bounded_poly 3328 future(t_as_ntt)[i]`.
     Inner loop invariant accumulates ≤ j*3328, outer
     `add_standard_error_reduce` collapses back to 3328.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem compute_As_plus_e_spec
    {Vector : Type} (K : Std.Usize) (hK : K.val ≤ 4)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (t_as_ntt matrix_A s_as_ntt error_as_ntt : Aeneas.Std.Array _ K)
    (h_s : ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      s_as_ntt[i]!.coefficients[a].elements[b].val.natAbs ≤ 3328)
    (h_e : ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      error_as_ntt[i]!.coefficients[a].elements[b].val.natAbs ≤ 3328)
    (h_A : ∀ i : Fin K.val, ∀ j : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      matrix_A[i]![j]!.coefficients[a].elements[b].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_As_plus_e OpsInst K t_as_ntt matrix_A s_as_ntt error_as_ntt
    ⦃ ⇓ r => ⌜ ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
                r[i]!.coefficients[a].elements[b].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- ## L7.3 `compute_vector_u` — `u = NTT⁻¹(Aᵀ◦r̂) + e₁`. Similar
    K-loop with inverse NTT and `add_error_reduce`. Depends on L6.3,
    L6.2, L3.8. Tier: loop-induction.
    [F*-bound: matrix.rs:183-190 `compute_vector_u` pre: `K ≤ 4 ∧
     ∀ i < K, is_bounded_poly 7 error_1[i] ∧ is_bounded_poly 3328 r_as_ntt[i] ∧
     ∀ j < K, is_bounded_poly 3328 a_as_ntt[i][j]`;
     post: `∀ i < K, is_bounded_poly 3328 result[i]`. The low `7` bound
     on error_1 reflects fresh CBD output (η ≤ 3, loosely bounded).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem compute_vector_u_spec
    {Vector : Type} (K : Std.Usize) (hK : K.val ≤ 4)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (a_as_ntt : Aeneas.Std.Array (Aeneas.Std.Array _ K) K)
    (r_as_ntt error_1 : Aeneas.Std.Array _ K)
    (h_e : ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      error_1[i]!.coefficients[a].elements[b].val.natAbs ≤ 7)
    (h_r : ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      r_as_ntt[i]!.coefficients[a].elements[b].val.natAbs ≤ 3328)
    (h_A : ∀ i : Fin K.val, ∀ j : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      a_as_ntt[i]![j]!.coefficients[a].elements[b].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u OpsInst K a_as_ntt r_as_ntt error_1
    ⦃ ⇓ r => ⌜ ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
                r[i]!.coefficients[a].elements[b].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- ## L7.4 `compute_ring_element_v` — `v = NTT⁻¹(t̂ᵀ◦r̂) + e₂ + m`.
    Depends on L6.3, L6.2 `add_message_error_reduce`, L3.8. Tier:
    loop-induction.
    [F*-bound: matrix.rs:151-158 `compute_ring_element_v` pre: `K ≤ 4 ∧
     is_bounded_poly 3328 message ∧ is_bounded_poly 3328 error_2 ∧
     ∀ i < K, is_bounded_poly 3328 t_as_ntt[i] ∧ is_bounded_poly 3328 r_as_ntt[i]`;
     post: `is_bounded_poly 3328 result`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem compute_ring_element_v_spec
    {Vector : Type} (K : Std.Usize) (hK : K.val ≤ 4)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (t_as_ntt r_as_ntt : Aeneas.Std.Array _ K)
    (error_2 message : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (h_msg : ∀ a : Fin 16, ∀ b : Fin 16,
      message.coefficients[a].elements[b].val.natAbs ≤ 3328)
    (h_e2 : ∀ a : Fin 16, ∀ b : Fin 16,
      error_2.coefficients[a].elements[b].val.natAbs ≤ 3328)
    (h_t : ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      t_as_ntt[i]!.coefficients[a].elements[b].val.natAbs ≤ 3328)
    (h_r : ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      r_as_ntt[i]!.coefficients[a].elements[b].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_ring_element_v OpsInst K t_as_ntt r_as_ntt error_2 message
    ⦃ ⇓ r => ⌜ ∀ a : Fin 16, ∀ b : Fin 16,
                r.coefficients[a].elements[b].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/- ## L7.5 `compute_message` — `m̂ = v − NTT⁻¹(sᵀ◦û)` (decrypt
    side). Depends on L6.3, L3.8, L6.4 `subtract_reduce`. Tier:
    loop-induction.
    [F*-bound: matrix.rs:119-125 `compute_message` pre: `K ≤ 4 ∧
     is_bounded_poly 4095 v ∧ ∀ i < K, is_bounded_poly 3328 secret_as_ntt[i] ∧
     is_bounded_poly 3328 u_as_ntt[i]`; post: `is_bounded_poly 3328 result`.
     (v is the raw decoded ciphertext element with 4095 = 2^12-1 bound,
     directly out of `deserialize_to_uncompressed_ring_element`.)]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem compute_message_spec
    {Vector : Type} (K : Std.Usize) (hK : K.val ≤ 4)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (v : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (secret_as_ntt u_as_ntt : Aeneas.Std.Array _ K)
    (h_v : ∀ a : Fin 16, ∀ b : Fin 16,
      0 ≤ v.coefficients[a].elements[b].val ∧
      v.coefficients[a].elements[b].val ≤ 4095)
    (h_s : ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      secret_as_ntt[i]!.coefficients[a].elements[b].val.natAbs ≤ 3328)
    (h_u : ∀ i : Fin K.val, ∀ a : Fin 16, ∀ b : Fin 16,
      u_as_ntt[i]!.coefficients[a].elements[b].val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_message OpsInst K v secret_as_ntt u_as_ntt
    ⦃ ⇓ r => ⌜ ∀ a : Fin 16, ∀ b : Fin 16,
                r.coefficients[a].elements[b].val.natAbs ≤ 3328 ⌝ ⦄ := by
  sorry
-/

/-! ============================================================
    # LAYER 8 — IND-CPA (K-PKE) core

    `ind_cpa.generate_keypair`, `encrypt`, `encrypt_c1`, `encrypt_c2`,
    `decrypt`, `decrypt_unpacked`. Each combines L4 (sampling), L7
    (matrix arithmetic), L3 (NTT/iNTT), L6 (poly ops), L5 (byte
    encoding) in the FIPS-203 K-PKE algorithm sequence.

    Spec anchor: `Spec.kpke_{keygen, encrypt, decrypt}` (Algorithms
    12, 13, 14).

    [F*-port status: **OUT OF SCOPE for direct proof port**
     (deep-review §2 Layer 8). Upstream `Ind_cpa.fst` (1329 LOC) has
     **18 `admit () (* Panic freedom *)` calls** at every top-level
     function. Upstream proves FC for the inner calls (Layers 6/7)
     but does **not** prove FC composition at L8. The only useful
     upstream artifact is the **architecture**: the 9-stage
     decomposition for `encrypt`, 5-stage for `decrypt`, etc., which
     this Plan already captures. **Lean must produce FC composition
     theorems from scratch**, ~2–3 weeks once L7 closes.]

    All [extraction missing].

    ## L8.1 `ind_cpa.generate_keypair_unpacked` — K-PKE.KeyGen
    (Algorithm 12). Sequence:
    1. `G(d) → (rho, sigma)`           (SHA3-512)
    2. `Â = SampleA(rho)`              (L7.1)
    3. `ŝ = NTT(SamplePolyCBD η₁(PRF(sigma, 0)))` × K
    4. `ê = NTT(SamplePolyCBD η₁(PRF(sigma, K)))` × K
    5. `t̂ = Â◦ŝ + ê`                  (L7.2)
    6. `ek = ByteEncode₁₂(t̂) || rho`  (L5.4)
    7. `dk = ByteEncode₁₂(ŝ)`         (L5.4)
    Depends on L7.1, L4.3, L3.6, L7.2, L5.4 + SHA-3 G/PRF.
    Tier: needs-new-helper-tier (multi-stage equation chain).
    [F*-bound: PANIC-FREE-ONLY in upstream `Ind_cpa.fst` (admits at
     `admit () (* Panic freedom *)`); FC bound is the Lean campaign's
     open obligation. Target post = hacspec-equivalence on (ek, dk) byte
     strings up to the L8.5 spec call. Pre cites:
     ind_cpa.rs:408-414 `generate_keypair` pre: `is_rank K ∧ PRIVATE_KEY_SIZE
     == cpa_private_key_size K ∧ PUBLIC_KEY_SIZE == cpa_public_key_size K ∧
     ETA1 == eta1 K ∧ ETA1_RANDOMNESS_SIZE == eta1_randomness_size K ∧
     key_generation_seed.len() == CPA_KEY_GENERATION_SEED_SIZE`. Hacspec
     post: `Spec.kpke_keygen K key_generation_seed = .ok (ek, dk) ⇒
     result.0 == dk ∧ result.1 == ek`.]
-/
/- Triple skeleton (extraction missing; output is .ok of byte tuple):
@[spec]
theorem ind_cpa_generate_keypair_spec
    {Vector Hasher : Type} (K ETA1 ETA1_RANDOMNESS_SIZE
      PRIVATE_KEY_SIZE PUBLIC_KEY_SIZE : Std.Usize)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (HashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher K)
    (key_generation_seed : Aeneas.Std.Slice Std.U8)
    (h_rank : K.val ∈ ({2,3,4} : Finset Nat))
    (h_eta1 : ETA1.val = if K.val = 2 then 3 else 2)
    (h_pksz : PUBLIC_KEY_SIZE.val = K.val * 384 + 32)
    (h_sksz : PRIVATE_KEY_SIZE.val = K.val * 384)
    (h_eta1sz : ETA1_RANDOMNESS_SIZE.val = ETA1.val * 64)
    (h_seed : key_generation_seed.val.length = 32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cpa.generate_keypair
      OpsInst HashInst K ETA1 ETA1_RANDOMNESS_SIZE PRIVATE_KEY_SIZE PUBLIC_KEY_SIZE
      key_generation_seed
    ⦃ ⇓ r => ⌜ -- Panic-freedom: result is .ok with conforming sizes; FC equivalence
              -- to `Spec.kpke_keygen K key_generation_seed` is the open obligation.
              r.1.val.length = PRIVATE_KEY_SIZE.val ∧ r.2.val.length = PUBLIC_KEY_SIZE.val ⌝ ⦄ := by
  sorry
-/

/- ## L8.2 `ind_cpa.encrypt` — K-PKE.Encrypt (Algorithm 13). 9 steps
    mixing L4.3, L3.6, L7.3, L7.4, L5.3, L6.5. Tier:
    needs-new-helper-tier.
    [F*-bound: PANIC-FREE-ONLY in upstream `Ind_cpa.fst`; FC bound is
     the Lean campaign's open obligation. Pre cites ind_cpa.rs:828-842
     `encrypt` pre: many const-generic conformance equations including
     `is_rank K ∧ ETA1 == eta1 K ∧ ETA2 == eta2 K ∧ public_key.len() ==
     cpa_public_key_size K ∧ randomness.len() == SHARED_SECRET_SIZE ∧
     CIPHERTEXT_SIZE == cpa_ciphertext_size K ∧ U_COMPRESSION_FACTOR ==
     vector_u_compression_factor K ∧ V_COMPRESSION_FACTOR ==
     vector_v_compression_factor K`. Hacspec post: `Spec.kpke_encrypt =
     .ok expected ⇒ result == expected`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem ind_cpa_encrypt_spec
    {Vector Hasher : Type} (K CIPHERTEXT_SIZE U_COMPRESSION_FACTOR
      V_COMPRESSION_FACTOR ETA1 ETA2 ETA1_RANDOMNESS_SIZE ETA2_RANDOMNESS_SIZE : Std.Usize)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (HashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher K)
    (public_key : Aeneas.Std.Slice Std.U8)
    (message : Aeneas.Std.Array Std.U8 32#usize)
    (randomness : Aeneas.Std.Slice Std.U8)
    (h_rank : K.val ∈ ({2,3,4} : Finset Nat))
    (h_pk : public_key.val.length = K.val * 384 + 32)
    (h_rnd : randomness.val.length = 32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cpa.encrypt OpsInst HashInst K
      CIPHERTEXT_SIZE U_COMPRESSION_FACTOR V_COMPRESSION_FACTOR
      ETA1 ETA2 ETA1_RANDOMNESS_SIZE ETA2_RANDOMNESS_SIZE
      public_key message randomness
    ⦃ ⇓ r => ⌜ r.val.length = CIPHERTEXT_SIZE.val ⌝ ⦄ := by
  sorry
-/

/- ## L8.3 / L8.4 `encrypt_c1` / `encrypt_c2` — split variants of
    L8.2. Direct corollaries via ciphertext-half projection.
    [F*-bound: PANIC-FREE-ONLY in upstream; same pre/post shape as L8.2
     restricted to one ciphertext half. Lean campaign treats these as
     restriction lemmas of L8.2, not separate top-level Triples.]
-/

/- ## L8.5 `ind_cpa.decrypt` — K-PKE.Decrypt (Algorithm 14). Chain
    L6.6 + L5.3 + L6.7 + L7.5 + L6.5 + L5.1. Tier:
    needs-new-helper-tier.
    [F*-bound: PANIC-FREE-ONLY in upstream `Ind_cpa.fst`; FC bound is
     the Lean campaign's open obligation. Pre: `is_rank K ∧
     CIPHERTEXT_SIZE == cpa_ciphertext_size K ∧ U_COMPRESSION_FACTOR ==
     vector_u_compression_factor K ∧ V_COMPRESSION_FACTOR ==
     vector_v_compression_factor K`. Target post: `result ==
     Spec.kpke_decrypt secret_key ciphertext`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem ind_cpa_decrypt_spec
    {Vector : Type} (K CIPHERTEXT_SIZE VECTOR_U_ENCODED_SIZE
      U_COMPRESSION_FACTOR V_COMPRESSION_FACTOR : Std.Usize)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (secret_key : Aeneas.Std.Slice Std.U8)
    (ciphertext : Aeneas.Std.Array Std.U8 CIPHERTEXT_SIZE)
    (h_rank : K.val ∈ ({2,3,4} : Finset Nat))
    (h_sk : secret_key.val.length = K.val * 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cpa.decrypt OpsInst K
      CIPHERTEXT_SIZE VECTOR_U_ENCODED_SIZE U_COMPRESSION_FACTOR V_COMPRESSION_FACTOR
      secret_key ciphertext
    ⦃ ⇓ r => ⌜ r.val.length = 32 ⌝ ⦄ := by
  sorry
-/

/-! ============================================================
    # LAYER 9 — IND-CCA (FO transform wrapping)

    The Fujisaki–Okamoto transform layer:
    `ind_cca.generate_keypair`, `encapsulate`, `decapsulate`,
    `validate_public_key`, `validate_private_key`.

    Spec anchor: `Spec.{mlkem_keygen, mlkem_encaps, mlkem_decaps,
    public_key_modulus_check}` (Algorithms 16/19/20/21).

    Compared to L8, this adds:
    - Public-key validation (`public_key_modulus_check`)
    - Hash bindings: H(ek), H(c), J (implicit rejection)
    - Re-encryption check in decapsulate

    [F*-port status: **OUT OF SCOPE for direct proof port** (deep-review
     §2 Layer 9). Upstream `Ind_cca.fst` (646 LOC) has the same
     panic-freedom-admit story as L8 (admits at lines 362, 452, 643).
     None of `validate_public_key`, `validate_private_key`,
     `generate_keypair`, `encapsulate`, `decapsulate` have FC posts
     upstream. **Lean writes FC composition from scratch**;
     `decapsulate` (L9.5) is the longest chain and the deep-review
     scorecard pegs the layer at ~3 weeks. Plan accordingly: this is
     the layer where the §13.8 sub-agent dispatch methodology pays
     off most.]

    All [extraction missing].

    ## L9.1 `ind_cca.validate_public_key` — verify ek byte string is a
    valid encoding (FIPS-203 §7.2 modulus check). Decode each 384-byte
    chunk via L6.7, re-encode via L5.4 (D=12), compare to original
    bytes. Close via per-chunk L5.6 round-trip identity. Depends on
    L6.7, L5.4, L5.6. Tier: loop-induction.
    [F*-bound: PANIC-FREE-ONLY in upstream `Ind_cca.fst` (admit at line
     362); FC bound is the Lean campaign's open obligation. Target post:
     `result == Spec.public_key_modulus_check K public_key`.
     Pre: `is_rank K ∧ public_key.len() == cpa_public_key_size K`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem ind_cca_validate_public_key_spec
    {Vector Hasher : Type} (K PUBLIC_KEY_SIZE T_AS_NTT_ENCODED_SIZE : Std.Usize)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (HashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher K)
    (public_key : Aeneas.Std.Array Std.U8 PUBLIC_KEY_SIZE)
    (h_rank : K.val ∈ ({2,3,4} : Finset Nat))
    (h_size : PUBLIC_KEY_SIZE.val = K.val * 384 + 32)
    (h_t : T_AS_NTT_ENCODED_SIZE.val = K.val * 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cca.validate_public_key
      OpsInst HashInst K PUBLIC_KEY_SIZE T_AS_NTT_ENCODED_SIZE public_key
    ⦃ ⇓ r => ⌜ r = True ∨ r = False ⌝ ⦄ := by
  sorry
-/

/- ## L9.2 `ind_cca.validate_private_key` — verify dk well-formed AND
    embedded H(ek) matches. Couples to
    `LibcruxIotSha3.Sponge.Shake.sha256_ema_spec`. Depends on L9.1.
    Tier: needs-new-helper-tier.
    [F*-bound: PANIC-FREE-ONLY in upstream; FC bound is the Lean
     campaign's open obligation. Target post: `result ==
     Spec.private_key_modulus_check K private_key`.]
-/

/- ## L9.3 `ind_cca.generate_keypair` — ML-KEM.KeyGen (Algorithm 19).
    Sequence:
    1. Split `randomness[64]` into `(d, z)` (32 bytes each)
    2. K-PKE.KeyGen(d) → (ek, ind_cpa_sk)  (L8.1)
    3. dk = ind_cpa_sk || ek || H(ek) || z (byte concatenation)
    4. Output (ek, dk)
    Depends on L8.1, sha256_ema_spec, `Spec.mlkem_keygen`. Tier:
    needs-new-helper-tier.
    [F*-bound: PANIC-FREE-ONLY in upstream `Ind_cca.fst` (admit at line
     452, `generate_keypair`); FC bound is the Lean campaign's open
     obligation. Pre cites ind_cca.rs:881-886: `is_rank K ∧
     ETA1_RANDOMNESS_SIZE == eta1_randomness_size K ∧ ETA1 == eta1 K ∧
     PUBLIC_KEY_SIZE == cpa_public_key_size K`. Target post: hacspec
     equivalence to `Spec.mlkem_keygen K randomness` on (ek, dk).]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem ind_cca_generate_keypair_spec
    {Vector Hasher : Type} (K ETA1 ETA1_RANDOMNESS_SIZE
      CPA_PRIVATE_KEY_SIZE PRIVATE_KEY_SIZE PUBLIC_KEY_SIZE : Std.Usize)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (HashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher K)
    (randomness : Aeneas.Std.Array Std.U8 64#usize)
    (h_rank : K.val ∈ ({2,3,4} : Finset Nat))
    (h_pksz : PUBLIC_KEY_SIZE.val = K.val * 384 + 32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cca.generate_keypair
      OpsInst HashInst K ETA1 ETA1_RANDOMNESS_SIZE
      CPA_PRIVATE_KEY_SIZE PRIVATE_KEY_SIZE PUBLIC_KEY_SIZE randomness
    ⦃ ⇓ r => ⌜ -- Panic-freedom: shape conformance; full Spec.mlkem_keygen
              -- equivalence is the open obligation.
              r.1.value.val.length = PUBLIC_KEY_SIZE.val ∧
              r.2.value.val.length = PRIVATE_KEY_SIZE.val ⌝ ⦄ := by
  sorry
-/

/- ## L9.4 `ind_cca.encapsulate` — ML-KEM.Encaps (Algorithm 20).
    Sequence:
    1. K̄ = G(m || H(ek)) → (K, r)  (SHA3-512)
    2. c = K-PKE.Encrypt(ek, m, r)  (L8.2)
    3. Output (c, K)
    Depends on L8.2, sha3_512_ema_spec, sha256_ema_spec,
    `Spec.mlkem_encaps`. Tier: needs-new-helper-tier.
    [F*-bound: PANIC-FREE-ONLY in upstream `Ind_cca.fst` (panic_free
     wrapper at line 939, `encapsulate`); FC bound is the Lean
     campaign's open obligation. Pre cites ind_cca.rs:939-953:
     `is_rank K ∧ ETA1 == eta1 K ∧ ETA2 == eta2 K ∧ CIPHERTEXT_SIZE ==
     cpa_ciphertext_size K ∧ ... ∧ is_bounded_polynomial_matrix 3328
     public_key.A ∧ is_bounded_polynomial_vector 3328
     public_key.t_as_ntt`. Target post: `(c, K) == Spec.mlkem_encaps ...`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem ind_cca_encapsulate_spec
    {Vector Hasher : Type} (K CIPHERTEXT_SIZE PUBLIC_KEY_SIZE
      T_AS_NTT_ENCODED_SIZE C1_SIZE C2_SIZE
      VECTOR_U_COMPRESSION_FACTOR VECTOR_V_COMPRESSION_FACTOR
      VECTOR_U_BLOCK_LEN ETA1 ETA1_RANDOMNESS_SIZE
      ETA2 ETA2_RANDOMNESS_SIZE : Std.Usize)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (HashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher K)
    (public_key : libcrux_iot_ml_kem.types.MlKemPublicKey PUBLIC_KEY_SIZE)
    (randomness : Aeneas.Std.Array Std.U8 32#usize)
    (h_rank : K.val ∈ ({2,3,4} : Finset Nat))
    -- The bounded-matrix / bounded-vector preconditions on public_key
    -- internals are upstream-tracked via `is_bounded_polynomial_*`;
    -- here they show up as Lean-side typeclass / explicit-argument hypotheses
    -- once the unpacked-public-key Triple lands.
    :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cca.encapsulate OpsInst HashInst K
      CIPHERTEXT_SIZE PUBLIC_KEY_SIZE T_AS_NTT_ENCODED_SIZE
      C1_SIZE C2_SIZE VECTOR_U_COMPRESSION_FACTOR VECTOR_V_COMPRESSION_FACTOR
      VECTOR_U_BLOCK_LEN ETA1 ETA1_RANDOMNESS_SIZE ETA2 ETA2_RANDOMNESS_SIZE
      public_key randomness
    ⦃ ⇓ r => ⌜ r.1.value.val.length = CIPHERTEXT_SIZE.val ∧ r.2.val.length = 32 ⌝ ⦄ := by
  sorry
-/

/- ## L9.5 `ind_cca.decapsulate` — ML-KEM.Decaps (Algorithm 21).
    Sequence:
    1. Extract (ind_cpa_sk, ek, H(ek), z) from dk
    2. m' = K-PKE.Decrypt(ind_cpa_sk, c) (L8.5)
    3. (K', r') = G(m' || H(ek)) (SHA3-512)
    4. c' = K-PKE.Encrypt(ek, m', r') (L8.2) — re-encryption check
    5. K̄ = J(z || c) (SHAKE256)
    6. Return `if c' == c then K' else K̄` (constant-time)
    Depends on L8.2, L8.5, sha3_512_ema_spec, shake256_spec,
    constant_time_ops, `Spec.mlkem_decaps`. Tier:
    needs-new-helper-tier (longest equation chain in the plan).
    [F*-bound: PANIC-FREE-ONLY in upstream `Ind_cca.fst` (admit at line
     643, `decapsulate`); FC bound is the Lean campaign's open
     obligation. Pre cites ind_cca.rs:1038-1056: a long bag of const-
     generic conformance equations PLUS
     `is_bounded_polynomial_vector 3328 secret_as_ntt ∧
     is_bounded_polynomial_matrix 3328 A ∧
     is_bounded_polynomial_vector 3328 t_as_ntt` on the key_pair internals.
     Target post: `result == Spec.mlkem_decaps key_pair ciphertext`.]
-/
/- Triple skeleton (extraction missing):
@[spec]
theorem ind_cca_decapsulate_spec
    {Vector Hasher : Type} (K CIPHERTEXT_SIZE PRIVATE_KEY_SIZE PUBLIC_KEY_SIZE
      T_AS_NTT_ENCODED_SIZE CPA_SECRET_KEY_SIZE C1_SIZE C2_SIZE C1_BLOCK_SIZE
      VECTOR_U_COMPRESSION_FACTOR VECTOR_V_COMPRESSION_FACTOR
      ETA1 ETA1_RANDOMNESS_SIZE ETA2 ETA2_RANDOMNESS_SIZE
      IMPLICIT_REJECTION_HASH_INPUT_SIZE : Std.Usize)
    (OpsInst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (HashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher K)
    (key_pair : libcrux_iot_ml_kem.types.MlKemKeyPair PRIVATE_KEY_SIZE PUBLIC_KEY_SIZE)
    (ciphertext : libcrux_iot_ml_kem.types.MlKemCiphertext CIPHERTEXT_SIZE)
    (h_rank : K.val ∈ ({2,3,4} : Finset Nat))
    :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cca.decapsulate OpsInst HashInst K
      CIPHERTEXT_SIZE PRIVATE_KEY_SIZE PUBLIC_KEY_SIZE T_AS_NTT_ENCODED_SIZE
      CPA_SECRET_KEY_SIZE C1_SIZE C2_SIZE C1_BLOCK_SIZE
      VECTOR_U_COMPRESSION_FACTOR VECTOR_V_COMPRESSION_FACTOR
      ETA1 ETA1_RANDOMNESS_SIZE ETA2 ETA2_RANDOMNESS_SIZE
      IMPLICIT_REJECTION_HASH_INPUT_SIZE
      key_pair ciphertext
    ⦃ ⇓ r => ⌜ r.val.length = 32 ⌝ ⦄ := by
  sorry
-/

/-! ============================================================
    # LAYER 10 — Per-variant top-level theorems

    The public API for each parameter set (RANK 2, 3, 4 → ML-KEM-512,
    768, 1024). Each is a thin specialization of the corresponding L9
    Triple with concrete const generics.

    The const generics flow:
    - mlkem512:  RANK=2, ETA1=3, ETA2=2, du=10, dv=4
    - mlkem768:  RANK=3, ETA1=2, ETA2=2, du=10, dv=4
    - mlkem1024: RANK=4, ETA1=2, ETA2=2, du=11, dv=5

    These instantiate the generic L9 specs at concrete values; each
    closes by `apply <L9 spec>; decide` (the const-generic
    preconditions are all `decide`-true at concrete values).

    [F*-port: `Libcrux_ml_kem.Mlkem{512,768,1024}.fst` — thin
     panic-free wrappers, no FC content. Trivial corollaries once L9
     has FC. The deep-review scorecard revises Plan.lean's 2–3 wk
     estimate down to **3–5 days** for all 15.]

    All [extraction missing].

    ## L10.1–L10.5 ML-KEM-768 — `{validate_public_key,
    validate_private_key, generate_key_pair, encapsulate,
    decapsulate}_equiv_hacspec`. Each ~5 lines once L9 closes.

    ## L10.6–L10.10 ML-KEM-512 — same 5 corollaries at RANK=2.

    ## L10.11–L10.15 ML-KEM-1024 — same 5 corollaries at RANK=4.

    ### Example shape (ML-KEM-768 generate_key_pair):

    ```
    /-- ML-KEM-768 KeyGen equivalence. Reflects FIPS-203 Algorithm 19. -/
    theorem mlkem768_generate_key_pair_equiv_hacspec
        (randomness : Std.Array Std.U8 64#usize) :
        ⦃ ⌜ True ⌝ ⦄
        libcrux_iot_ml_kem.mlkem768.generate_key_pair randomness
        ⦃ ⇓ kp => ⌜ ∃ ek_spec dk_spec,
                    Spec.mlkem_keygen 3 randomness = (ek_spec, dk_spec)
                    ∧ kp.public_key.value.val = ek_spec.val
                    ∧ kp.private_key.value.val = dk_spec.val ⌝ ⦄ := by
      apply ind_cca_generate_keypair_spec  -- L9.3 at K=3
      all_goals decide
    ```
-/

/-! ### Spec-side no-op shims — do not anchor posts against these

    Audited 2026-05-23. The following hacspec-side functions are
    syntactic mirrors of impl methods but contain no verification
    content (they reduce to identity over canonical FieldElement):

    - `Spec.polynomial.poly_barrett_reduce` (polynomial.rs:29-31).
      Body: `createi(|i| FieldElement::new(p[i].val % FIELD_MODULUS))`.
      Since `FieldElement::new` already canonicalizes via `% q`, this
      is `id` over canonical inputs.
    - `Spec.ntt.to_unsigned_field_modulus` (ntt.rs:11-13). Same pattern.

    Implication for upgraded posts: L3.6/3.7's terminal barrett step
    should NOT wrap in `Spec.poly_barrett_reduce`. The lift function
    `Spec.lift_poly_mont` already canonicalizes via `FieldElement::new`,
    so `lift ∘ impl_barrett_reduce = lift` over the bounded subset.
    Similarly, L5.x serialization should use direct `c.val < q` checks
    rather than `Spec.to_unsigned_field_modulus(...) = result`.

    Verifying `impl_op ≡ no-op-shim` proves nothing about
    correctness — it just proves the impl reduces.

    See ~/.claude/plans/iot-mlkem-functional-correctness-master.md
    §D9, §D10 for the full audit.
-/

/-! ============================================================
    # CRITICAL BRIDGE LEMMAS — Montgomery / data-layout divergences

    These are the lemmas where the impl's representation diverges
    most from the spec, and where the proof effort concentrates.
    Whoever closes the campaign should write these first, in this
    order:

    1. **`mont_R_inv_q`** (Layer 0 helper):  `2^16 · 169 ≡ 1 (mod 3329)`.
       A 1-line `decide` close, but referenced by every Montgomery-domain
       Triple. Without it, every L0.3+ spec post is opaque.

    2. **`Spec.lift_poly_mont`** (Layer 3 bridge): the single
       conversion that lets `ntt_binomially_sampled_ring_element_spec`
       (L3.6) be stated as `Spec.ntt(Spec.lift_poly_mont(re)) =
       Spec.lift_poly_mont(_r)`. The impl's output of `ntt_*` is in
       Montgomery domain (R · spec_value mod q); `Spec.lift_poly_mont`
       absorbs the R⁻¹. Compare to `polynomial::cross_spec::lift_poly`
       (no R⁻¹) which is correct for **standard-domain** poly stages
       like `add_to_ring_element`.

    3. **`mont_1441_eq_inv128`** (Layer 6 bridge):  `1441 · 128 · R⁻¹
       ≡ 1 (mod 3329)`. The magic constant in `add_error_reduce`'s
       `montgomery_multiply_by_constant 1441` step exactly cancels
       the deferred `1/128` factor from inverse NTT.

    4. **`mont_2285_eq_R_mod_q`** (Layer 5 / serialization bridge):
       `2285 ≡ 2^16 (mod 3329)`. Used in `to_unsigned_field_modulus`
       to convert Montgomery-encoded → canonical representative
       before serialization.

    5. **`mont_1353_eq_RR_mod_q`** (Layer 3/6 bridge):
       `1353 ≡ R² (mod 3329)`. The Rust function `to_standard_domain`
       is `montgomery_multiply(c, 1353)`; it lifts `x` to `R · x mod q`
       (since `x · R² · R⁻¹ = R · x`).

    All five close trivially (`decide` or `bv_decide` on small
    arithmetic), but their *existence* is what makes Campaign 2
    algebraic-close possible. **The four below DO compile** — they
    are the only fully-typed Lean content in this file pending
    extraction fixes.
-/

-- The four typed bridge theorems B.1–B.4 (`mont_R_inv_q`,
-- `mont_1441_eq_inv128`, `mont_2285_eq_R_mod_q`,
-- `mont_1353_eq_RR_mod_q`) and the two new keystones
-- (`mont_qinv_R`, `mont_128_169_512`) live in
-- `LibcruxIotMlKem.Util.NumericKeystones`. References in the lemma
-- sketches above (B.1–B.4 by short name) resolve via the `import` at
-- the top of this file plus the namespace `libcrux_iot_ml_kem.Util`.

/-! ============================================================
    # FUNCTIONAL-CORRECTNESS UPGRADE PATH

    **Status:** currently bound-only across L0-L3.5 (20 closed
    Triples; Campaign-3 commits `60d53ca` `719d98f` `f5e7400`
    `b95de0c` `ac77d55`). Functional-correctness upgrade plan
    drafted **2026-05-23** across four sub-plans (Layer M
    architecture, L3 spec functional-spec, existing-post upgrade
    delta, L2.8 plan) and synthesized in
    `~/.claude/plans/iot-mlkem-functional-correctness-master.md`.

    ## The five phases

    | Phase | Scope | Cost |
    | --- | --- | --- |
    | 1 | bnd-relax + L3.6/3.7 bound-only | ~2700 LOC, 4 dispatches, ~1 wk |
    | 2 | L2.8 bound-only (parallel with Phase 1) | ~3000 LOC, 2 dispatches, ~1 day |
    | 3 | Layer M scaffolding (BitMlKem.{Spec,Commute,StateIso,AlgEquiv}) | ~3650 LOC, 6-8 dispatches, 2.5-3.5 wk |
    | 4 | Existing-post upgrade pass (20 closed Triples → equality form) | ~1535 LOC, ~10 dispatches, ~1-1.5 wk |
    | 5 | Functional L3.6/3.7/3.8 + L6.3 (vs `Spec.ntt`, `Spec.ntt_inverse_butterflies`, `Spec.multiply_ntts`) | ~830 LOC, 3-4 dispatches, ~1 wk |

    **Total: ~12K LOC, ~25 dispatches, ~6-8 weeks calendar.**

    Recommended order: **A (serialized)** — Phase 1+2 → Phase 3 →
    Phase 4 → Phase 5. The L3.6/3.7 bound-only Phase-1 closures
    get upgraded in Phase 4; alternative interleavings are
    detailed in the master plan §3.

    ## User-blocking decisions (consolidated from sub-plans)

    The master plan §4 lists 8 load-bearing decisions D1-D8 plus
    D9-D11 from the spec-shim audit. Each has a recommendation:

    - **D1 — MontPoly representation.** A+B parallel types
      (`MontPoly := Vector (ZMod 3329) 256` + `SpecPoly := Vector
      parameters.FieldElement 256` with `Vector.map` coercions).
      Optimizes M.2 algebra; bridges at the L3 closure boundary
      are ~30 LOC.
    - **D2 — Phase ordering.** Option A (serialized).
    - **D3 — L3.8 anchor and bound.** Anchor against
      `Spec.ntt_inverse_butterflies`; bound post `≤ (K+1) · 3328`
      (was `≤ 3328` per old Plan.lean — corrected; see L3.8
      [CORRECTED 2026-05-23] note).
    - **D4 — L2.8 timing.** Run Phase 2 in parallel with Phase 1.
    - **D5 — L1 cosmetic alias scope.** Skip L1.1/1.2/1.6/1.7/1.8/1.9
      `_full` aliases (already equality-form natural).
    - **D6 — L0.2 `bv_decide` golf (campaign F1).** Defer to after
      Phase 4; the +20 LOC corollary is independent of golf state.
    - **D7 — M.2 dispatch granularity.** 5-6 agents (one per
      block; Block D split into 3 parallel agents).
    - **D8 — Lake dep wiring** (action item, not a decision).
      `HacspecMlKem` to `lakefile.toml`; 1-line; first action of
      Phase 3.0.
    - **D9 — Spec.poly_barrett_reduce is a no-op shim** (audit
      finding). L3.6/3.7's terminal barrett step should NOT wrap in
      `Spec.poly_barrett_reduce`. See spec-shim warning above.
    - **D10 — Spec.to_unsigned_field_modulus is a no-op shim.**
      Same audit; L5.x serialize should use direct `< q` checks.
    - **D11 — Spec.ntt_multiply_n is dual-purpose** (N=16 chunk and
      N=256 full). L6.3 anchors `Spec.multiply_ntts` (N=256);
      L2.8 uses fresh M.1 `bit_ntt_multiply_chunk`.

    ## Automation pilot

    P0 automation pilot in progress (bv_decide / grind feasibility
    on L0.x / L1.x leaf-tier Triples). Results may revise
    per-Triple LOC estimates downward by 15-25%.

    ## Pointer

    Master plan: `~/.claude/plans/iot-mlkem-functional-correctness-master.md`.
    Sub-plans:
      - `~/.claude/plans/iot-mlkem-layer-M-architecture.md` (52 KB)
      - `~/.claude/plans/iot-mlkem-L3-poly-NTT-functional-spec.md` (46 KB)
      - `~/.claude/plans/iot-mlkem-existing-post-upgrade-delta.md` (44 KB)
      - `~/.claude/plans/iot-mlkem-L2-8-accumulating-ntt-multiply.md` (42 KB)
-/

/-! ============================================================
    # PROOF ORDER FOR THE VERIFICATION ENGINEER

    Close lemmas in this order. Each unblocks the next.

    **Recommended first lemma** (per deep-review §6): the engineer
    should NOT start with L0.3. The deep-review's headline finding is
    that the **Layer-M BitMlKem infrastructure** must precede every
    L0+ Triple, otherwise the post-conditions have no clean shape to
    land on. The 3-phase ordering for the very first effort:

    (a) **BitMlKem.Spec scaffolding** (~2–3 wk before any Triple):
        Define `MontPoly`, `to_spec_poly_plain`, `to_spec_poly_mont`,
        `bit_<op>` intermediate functions, opaque algebraic predicates.
        No Triple lemmas in this phase — pure `def`/`theorem` content
        ported from upstream `Hacspec_ml_kem.{ModQ, Commute.*}.fst`.

    (b) **Phase-0 extraction unblock** (in parallel with (a) or after,
        see the KNOWN BLOCKER section above): bump rust-core-models
        pin, author `libcrux-iot/ml-kem/hax_aeneas.py`, generate
        `HacspecMlKem` lake lib. ~1–2 wk.

    (c) **L0.3 `montgomery_reduce_element_spec`** is the first @[spec]
        Triple (NOT the first work item). With Util.NumericKeystones
        (B.1–B.4 already done + 2 missing keystones) + Util.Montgomery
        in place, the Triple is ~30 lines via ZMod casting. The
        bridges `mont_R_inv_q` (B.1) and `mont_qinv_R` (new) are the
        load-bearing identities.

    Phase 0 (toolchain + extraction):
      - Bump the rust-core-models pin (or re-run hax extraction
        against the current pin) so `LibcruxIotMlKem.Extraction.Funs`
        compiles cleanly. This is BLOCKER (a) above.
      - Author `libcrux-iot/ml-kem/hax_aeneas.py` (mirroring the SHA-3
        one in `libcrux-iot/sha3/hax_aeneas.py`) so the full impl
        extracts to `LibcruxIotMlKem/Extraction/Funs.lean`. BLOCKER (b).
      - Generate `HacspecMlKem` Lean library via hax→aeneas on
        `specs/ml-kem/src/`. Add `HacspecMlKem` to the lakefile.
        BLOCKER (c).
      - Replace every `Spec.*` placeholder in this Plan with the real
        extraction name.
      - Fix the project root `LibcruxIotMlKem.lean` to import
        `LibcruxIotMlKem.Extraction.Funs` (currently imports
        `LibcruxIotSha3.Extraction.Funs` which is incorrect; the
        SHA-3 dep was a paste error).
      - Uncomment the `/- Triple … -/` blocks in this Plan; verify
        each parses against the now-resolved Extraction.Funs.

    Phase M (Layer M — Bridge / Mont infrastructure, deep-review §5):
      - `IotMlKem.Util.NumericKeystones`: add the 2 missing identities
        (`mont_qinv_R`, `mont_128_169_512`) alongside the 4 done B.x.
      - `IotMlKem.Util.Montgomery`: `mont_reduce_int_form` + bound
        helpers. The L0.3 keystone proof lives here.
      - `IotMlKem.Util.ModQ`: opaque `mod_q_eq` + intro/reveal/refl/trans/sym.
      - `IotMlKem.Util.FieldElement`: FE type + lifts +
        `lemma_*_fe_commute_*` Block-A bridges (~20 lemmas).
      - `IotMlKem.Util.PortableVector`: `elementwise_proof` macro.
      - `IotMlKem.Util.BVDecide`: BitVec ↔ I16/U8 array flatten support.
      - `IotMlKem.BitMlKem.Spec`: MontPoly, to_spec_poly_*, bit_<op>
        defs, opaque algebraic predicates (~400 LOC).
      - `IotMlKem.BitMlKem.Commute`: per-vector + per-poly commute
        lemmas (~600 LOC). The keystone `lemma_intt_mont_form_post`
        ports via ZMod 3329 cast in ~10 Lean lines.
      - `IotMlKem.BitMlKem.StateIso`: lift_id, injectivity (~50 LOC).
      - `IotMlKem.BitMlKem.AlgEquiv`: bit_* ↔ Spec.* (Campaign 2
        closure, ~300 LOC).

    Phase 1 (Layer 0):
      - Bridge lemmas B.1–B.4 (DONE in this Plan).
      - L0.1 `get_n_least_significant_bits_spec` (`bv_decide`).
      - L0.2 `barrett_reduce_element_spec` (`scalar_tac +nonLin`).
      - L0.3 `montgomery_reduce_element_spec` (uses B.1; one Nat
        congruence helper, then close).
      - L0.4 `montgomery_multiply_fe_by_fer_spec` (mvcgen + L0.3).

    Phase 2 (Layer 1):
      - Write a `vector_elementwise_proof` macro in
        `Equivalence/L1_VectorElementOps.lean`.
      - Instantiate L1.1, L1.2, L1.3, L1.4, L1.5 + L1.6..L1.10.

    Phase 3 (Layer 2):
      - L2.1 `ntt_step_spec` (mvcgen + L0.4).
      - L2.2, L2.3, L2.4 (chained from L2.1).
      - L2.5, L2.6, L2.7 (inverse butterflies).
      - L2.8 `accumulating_ntt_multiply_spec` (needs the pure-Lean
        helper for base-case mul mod X²−ζ²).

    Phase 4 (Layer 3):
      - L3.1, L3.2, L3.3 (single-loop induction).
      - L3.4 `ntt_at_layer_4_plus_spec` (nested loop; largest single
        Triple in the plan).
      - L3.5 `ntt_at_layer_7_spec`.
      - L3.6 `ntt_binomially_sampled_ring_element_spec` (the
        Montgomery↔standard bridge; introduces `Spec.lift_poly_mont`).
      - L3.7 `ntt_vector_u_spec`.
      - L3.8 `invert_ntt_montgomery_spec` (mirror; needs iNTT
        extraction first).

    Phase 5 (Layer 4):
      - L4.1 `rej_sample_spec`.
      - L4.2 `sample_from_xof_spec` (SHA-3 coupling — assumes
        `LibcruxIotSha3.Sponge.Shake.shake128_spec` available).
      - L4.3 `sample_poly_cbd_spec`.

    Phase 6 (Layer 5):
      - L5.4 `serialize_D_spec` × 6 (bv_decide).
      - L5.5 `deserialize_D_spec` × 6.
      - L5.6 round-trip identity.
      - L5.1, L5.2, L5.3 (compress / decompress).

    Phase 7 (Layer 6):
      - L6.1 `poly_barrett_reduce`.
      - L6.2 `add_*_reduce` family (uses B.2 for the 1441 constant).
      - L6.3 `accumulating_ntt_multiply` at poly level.
      - L6.4 `subtract_reduce`.
      - L6.5, L6.6.
      - L6.7 `deserialize_ring_elements_reduced`.

    Phase 8 (Layer 7):
      - L7.1 `sample_matrix_A`.
      - L7.2 `compute_As_plus_e`.
      - L7.3, L7.4, L7.5.

    Phase 9 (Layer 8):
      - L8.1 `ind_cpa.generate_keypair_unpacked`.
      - L8.2 `ind_cpa.encrypt`.
      - L8.3, L8.4 (corollaries of L8.2).
      - L8.5 `ind_cpa.decrypt`.

    Phase 10 (Layer 9):
      - L9.1 `validate_public_key`.
      - L9.2 `validate_private_key`.
      - L9.3 `generate_keypair`.
      - L9.4 `encapsulate`.
      - L9.5 `decapsulate` (longest chain; expect 3-4 sub-agent
        dispatches per §13.8).

    Phase 11 (Layer 10):
      - L10.x corollaries — should each be a 5-line apply + decide.
      - Final hygiene: `#print axioms <top theorem>` reports only
        `propext`, `Classical.choice`, `Quot.sound` (plus
        `Lean.ofReduceBool` / `Lean.trustCompiler` IF any `decide`
        crossed a `native_decide` boundary).

    Phase 12 (cleanup):
      - Delete `Plan.lean`.
      - Update `LibcruxIotMlKem.lean` root to re-export the per-variant
        top theorems.
      - Write `README.md` mirroring SHA-3's, listing all top
        theorems with line numbers.

    ## Estimated effort (revised per deep-review §6 scorecard)

    Original Plan baseline 12–17 wk is optimistic — it didn't budget
    the BitMlKem.Commute infrastructure layer, ModularArith / BVDecide
    helpers, or the FC-from-scratch work for Layers 4 / 8 / 9 that
    upstream admits.

    - Phase 0: 1-2 weeks (re-extraction).
    - **Phase M: 2-3 weeks** (NEW: BitMlKem.Spec + Commute infra; deep-review §5).
    - **+1 week** for ModularArith / Util.Montgomery / Util.BVDecide helpers
      (folded into Phase M).
    - Phase 1: 1 week (mostly L0.3 montgomery reduce; helpers in M).
    - Phase 2: 1 week (Layer 1 macro + 10 specs).
    - Phase 3: 2 weeks (Layer 2: 14 NTT step + layer steps).
    - Phase 4: 3-4 weeks (NTT polynomial drivers; L3.4 alone is ~1.5 wk).
    - **Phase 5: 2-3 weeks** (REVISED: L4 sampling FC from scratch —
      upstream has no FC content; +1 wk over Plan's original 1-2 wk).
    - Phase 6: 1.5 weeks (Layer 5: bv_decide closes ser/deser fast).
    - Phase 7: 2 weeks (poly ops; subtract_reduce + 4 add variants ≈ 1 wk).
    - Phase 8: 1 week (matrix ops; blocked on L4).
    - **Phase 9: 2-3 weeks** (REVISED: L8 IND-CPA FC composition from
      scratch — upstream is panic-free-admit-only; +1-2 wk).
    - **Phase 10: 3 weeks** (REVISED: L9 IND-CCA FC composition from
      scratch; decapsulate alone is huge; +1 wk).
    - Phase 11: **3-5 days** (REVISED: L10 corollaries are trivial
      once L9 has FC; deep-review §6 dropped 2-3 wk → days).
    - Phase 12 (cleanup): 1 week.

    **Total: 17–22 weeks** for a single engineer (deep-review §6).
    Breakdown of the 5-week revision over Plan's original 12–17 wk:
      +2 wk  BitMlKem.Spec + Commute infra
      +1 wk  ModularArith / BVDecide / Montgomery helpers
      +2-3 wk  L4 sampling FC from scratch
      +5-6 wk  L8 + L9 FC composition from scratch (no upstream FC)
      -3 wk  L10 corollaries (downward revision)
      ≈ +5 wk net upward revision.

    Parallelism opens up at Phase 4 (rounds 1-3 of NTT), Phase 6 (per-D
    serializers), and across the L1.x macro instantiations, where
    worktree-isolated dispatches (§11.2) can compress 2-3× per phase.
    L3.4, L6.4, L8.x, L9.5 remain on the critical path.
-/

end libcrux_iot_ml_kem.Plan
