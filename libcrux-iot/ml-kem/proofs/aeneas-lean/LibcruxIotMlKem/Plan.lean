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

  ## KNOWN BLOCKER (Phase 0 prerequisite) — Three extraction gaps

  ### (a) `LibcruxIotMlKem.Extraction.Funs` does not compile

  The auto-generated `Extraction/Funs.lean` references symbols that
  don't exist in the pinned `rust-core-models` rev `b67ccf1`:

  ```text
  Unknown constant `Aeneas.Std.I16.Insts.Libcrux_secretsIntCastOps.as_i32`
  Unknown constant `Aeneas.Std.I32.Insts.Libcrux_secretsIntCastOps.as_i16`
  Unknown identifier `libcrux_secrets.traits.Classify.Blanket.classify`
  Unknown identifier `core_models.num.I16.wrapping_neg`
  ```

  These are the `libcrux_secrets` classify/declassify shims that
  newer rust-core-models exports as Aeneas instances; the current
  pin predates them. To unblock:
  - Bump the rust-core-models pin in
    `.lake/packages/Hax/lakefile.toml` to a rev that has the
    Libcrux_secretsIntCastOps instances, OR
  - Re-run hax extraction against the current pin (this will
    produce a Funs.lean that uses only the constants the pin
    exports).

  Until then, the typed `import LibcruxIotMlKem.Extraction.Funs` at
  the top of `LibcruxIotMlKem.lean` doesn't resolve, and every Plan
  lemma that referenced `libcrux_iot_ml_kem.<symbol>` had to be
  commented out below.

  ### (b) Impl extraction is partial

  Even if (a) is fixed, the current `Extraction/Funs.lean` (~1063
  LOC, 52 top-level defs) covers ONLY the NTT / iNTT layer
  (`vector.portable.{arithmetic, ntt}`, `ntt.ntt_at_layer_*`,
  `ntt.ntt_binomially_sampled_ring_element`, `ntt.ntt_vector_u`,
  `polynomial.{zeta, PolynomialRingElement, poly_barrett_reduce}`,
  `vector.portable.ntt.accumulating_ntt_multiply*`). It does NOT
  contain:

  - `vector.portable.arithmetic.{add, sub, negate,
     multiply_by_constant, bitwise_and_with_constant, shift_right,
     cond_subtract_3329, barrett_reduce,
     montgomery_multiply_by_constant, get_n_least_significant_bits,
     reducing_from_i32_array}`
  - `vector.portable.{sampling, compress, serialize}.*`
  - `invert_ntt.*`
  - `sampling.*`, `matrix.*`, `serialize.*`, `compress.*`
  - `ind_cpa.*`, `ind_cca.*`, `mlkem{512,768,1024}.*`
  - `types.*` (key/ciphertext newtype wrappers)
  - `hash_functions.*`, `constant_time_ops.*`

  To trigger full extraction the verification engineer should author
  `libcrux-iot/ml-kem/hax_aeneas.py` (analogous to
  `libcrux-iot/sha3/hax_aeneas.py`) — mirroring the SHA-3 one and
  adjusting the bundle list to cover all ml-kem modules.

  ### (c) Hacspec aeneas-lean extraction missing

  The hacspec ML-KEM spec in `specs/ml-kem/src/` currently extracts
  only to F* (under `specs/ml-kem/proofs/fstar/extraction/`). There
  is no `specs/ml-kem/proofs/aeneas-lean/` analog yet. The SHA-3
  tree has both (`HacspecSha3` is a Lean lib used by the iot SHA-3
  proofs). **Before Campaign 2 can begin**, we need the
  `HacspecMlKem` Lean lib generated by running `hax → aeneas →
  aeneas-lean` against `specs/ml-kem/`.

  Until that exists, all spec references in this plan are
  pseudo-Lean references of the form `Spec.<fn>` in doc-comments.
  Campaign 1 work can start in parallel (it's impl-internal, no
  spec dependency, but is blocked on (a) and (b) first).

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

-- Lean imports. Note: the natural `import LibcruxIotMlKem.Extraction.Funs`
-- is currently impossible due to the KNOWN BLOCKER above. Once it is
-- fixed (Phase 0), replace the two imports below with that single
-- import.
import Aeneas
import Hax

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Plan

open Aeneas Aeneas.Std Std.Do

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

/-! ## Recommended Lean infrastructure (build BEFORE Triple campaign)

The deep-review (§5) identifies 7 helper modules whose absence blocks
every L3+ proof. Build these first; they are NOT optional. Citation:
`~/.claude/plans/iot-mlkem-fstar-proof-bodies-deep.md` §5.

- **`IotMlKem.Util.NumericKeystones`** (~30 LOC, 30 min). The 6 `decide`-
  closed numeric mod-q identities. **STATUS: 4/6 DONE in this Plan**
  (see B.1–B.4 below). Add the missing two: `mont_qinv_R`
  (`(62209 * 3329) % 2^16 = 1`) and `mont_128_169_512`
  (`(128 * 169 * 512) % 3329 = 1`).

- **`IotMlKem.Util.Montgomery`** (~200 LOC, 1 day). Int.emod ↔ ZMod
  3329 bridges. The key lemma is `mont_reduce_int_form` — given
  `(value - km) % 2^16 = 0`, the canonical Mont identity holds. Every
  L0 Triple closes by `apply mont_reduce_int_eq_id; scalar_tac`. See
  deep-review §2 (L0.3 entry) for the F* keystone proof shape.

- **`IotMlKem.Util.ModQ`** (~100 LOC, 4 h). Opaque `mod_q_eq` predicate
  + intro/reveal/refl/trans/sym helpers. Direct port of upstream
  `Hacspec_ml_kem.ModQ.fst` (57 LOC F*).

- **`IotMlKem.Util.FieldElement`** (~150 LOC, 1 day). FE type +
  `i16_to_spec_fe` + `mont_i16_to_spec_fe` + the ~20 per-element
  `lemma_*_fe_commute_*` bridges from upstream Chunk.fst:36-180,
  closed via ZMod-cast + `ring` (much shorter than F*'s manual
  `lemma_mod_mul_distr_*` chains).

- **`IotMlKem.Util.PortableVector`** (~300 LOC, 2 days). The
  `elementwise_proof` macro. Takes a per-element Triple + per-element
  post predicate, yields a 16-iter loop Triple. Each of L1.1–L1.10
  becomes a 5-line instantiation.

- **`IotMlKem.BitMlKem.Spec`** (~400 LOC, 1 week). The intermediate
  pure-Lean spec — analog of SHA-3's `BitKeccak/Spec.lean`. Defines
  `MontPoly`, `to_spec_poly_plain`, `to_spec_poly_mont`, and `bit_<op>`
  intermediate functions for each hacspec function. Plus the opaque
  algebraic predicates `bit_intt_mont_form`, `bit_mont_form`.

- **`IotMlKem.BitMlKem.Commute`** (~600 LOC, 2 weeks). Port of the
  entire upstream `commute/` tree (Chunk.fst 2711 LOC, Bridges.fst
  1241 LOC, Serialize.fst 202 LOC). Most lemmas port 1-to-1; ZMod
  simplification shortens Block A by ~40%, Array.ext shortens Block
  B by ~30%. See deep-review §3.2 for the Block A/B/C/D structure.

The total upfront infra cost is ~3 weeks but unblocks the entire L3+
campaign. The single biggest insight from the deep-review (§6
scorecard): **do NOT attempt to prove impl ↔ hacspec equivalence
directly**. Build BitMlKem.Spec + BitMlKem.Commute first; every
subsequent layer is then a clean two-phase composition (Campaign 1:
impl ↔ bit_*; Campaign 2: bit_* ↔ hacspec).
-/

/-! ============================================================
    # LAYER M — Bridge / Mont infrastructure (BitMlKem.* + Util.*)

    NOT a sequence of @[spec] Triples. This is the pure Lean spec /
    predicate / commute-lemma layer that every L0+ post-condition
    references. Build it FIRST. The bulk is direct port of upstream
    F* `Hacspec_ml_kem.{ModQ, Commute.*}.fst` (4234 LOC), which the
    deep-review §3 walks file by file.

    Concretely, fill in (in order):

    ## M.1 `BitMlKem/Spec.lean` — the intermediate spec
    - `def MontPoly := Vector FieldElement 256`
    - `def to_spec_poly_plain : PolynomialRingElement → MontPoly` (via
      `i16_to_spec_fe` per lane, 16 lanes × 16 elements)
    - `def to_spec_poly_mont : PolynomialRingElement → MontPoly` (via
      `mont_i16_to_spec_fe` per lane = `(v · 169) % 3329`)
    - `def bit_ntt_layer_1, bit_ntt_layer_2, ..., bit_invert_ntt_*`,
      `bit_poly_barrett_reduce`, `bit_subtract_reduce`, `bit_add_*`,
      etc. — written *as if implementing on the spec data shape*.
    - Opaque algebraic predicates: `bit_mont_form_lane`,
      `bit_intt_mont_form_lane`.

    ## M.2 `BitMlKem/Commute.lean` — per-vector / per-poly commute lemmas
    Mirrors upstream `commute/Chunk.fst` (2711 LOC) Block A–D:
    - **Block A** (Layer-0 scalar FE commutes, ~20 lemmas): each
      ~10 Lean lines via ZMod cast + `ring`. [F*-port:
      `Commute.Chunk.lemma_{add,sub,butterfly,mont_mul,...}_fe_commute_*`]
    - **Block B** (Chunk / per-vector commutes, ~14 lemmas): each
      ~30 Lean lines via `Array.ext` + Block-A lane invocation.
      [F*-port: `Commute.Chunk.lemma_{add,sub,...}_chunk_commutes_*`]
    - **Block C** (Poly-level commutes, ~7 lemmas): each ~30-50 lines.
      The keystone `lemma_intt_mont_form_post` (Chunk.fst:1577) ports
      via `ZMod 3329` casting in ~10 Lean lines vs F*'s 50.
    - **Block D** (Forward+reverse poly NTT layer commutes): ~6
      lemmas, each ~50 Lean lines. [F*-port: `Commute.Bridges.lemma_ntt_layer_{1,2,3}_step_to_hacspec`]

    ## M.3 `BitMlKem/StateIso.lean` — impl ↔ MontPoly round-trip
    - `theorem to_spec_poly_mont_injective` (well-defined on the
      bounded subset)
    - `theorem lift_id` (lift after unlift is identity on the impl
      side, modulo bounded coefficients)

    ## M.4 `BitMlKem/AlgEquiv.lean` — bit_* ↔ Spec.* algebraic equivs
    The Campaign 2 closure. Each `bit_<op>` def from M.1 is shown
    equivalent (under `to_spec_poly_plain`) to the corresponding
    `Spec.<op>` from hacspec. Uses the keystones B.1–B.4 (+ the two
    missing keystones above) plus `ring` in `ZMod 3329`.

    All of Layer M is `theorem`/`def`, not `@[spec]` Triples — no
    `hax_mvcgen` involvement. The output is the predicate vocabulary
    every L0+ Triple post references.
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
/- Triple (extraction missing for `get_n_least_significant_bits`):
@[spec]
theorem get_n_least_significant_bits_spec
    (n : Std.U8) (value : Std.U32) (hn : n.val ≤ 16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.get_n_least_significant_bits n value
    ⦃ ⇓ r => ⌜ r.val < 2 ^ n.val ∧ r.val = value.val % (2 ^ n.val) ⌝ ⦄ := by
  sorry
-/

/- **L0.2 `vector.portable.arithmetic.barrett_reduce_element`** — signed Barrett reduction.

    Hax post (`vector/portable/arithmetic.rs:111-130`):
    `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)` and
    `result ≡ value (mod FIELD_MODULUS)`.

    [F*-port: `Vector.Portable.Arithmetic.barrett_reduce_element`
     (lines 319–356, `--z3rlimit 150`). The F* proof is a 5-step `calc`
     using `lemma_mod_sub_distr` + `cancel_mul_mod` + 4 `assert` bounds
     on the quotient. Lean version: `hax_mvcgen` + ~2 `have` blocks
     using `Int.emod_sub_emod_cancel` + the closed-form quotient bound
     `barrett_quot_bound` (a fresh helper proved by `omega` after
     `interval_cases`). Est ~4 hours.]

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
theorem barrett_reduce_element_spec (value : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element value
    ⦃ ⇓ r => ⌜ (r.val - value.val) % 3329 = 0
              ∧ -1665 ≤ r.val ∧ r.val ≤ 1665 ⌝ ⦄ := by
  sorry
-/

/- **L0.3 `vector.portable.arithmetic.montgomery_reduce_element`** — signed Montgomery reduction.

    Hax post (`vector/portable/arithmetic.rs:143-169`):
    `o ≡ value · MONTGOMERY_R⁻¹ (mod FIELD_MODULUS)` and a bound.

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
-/
/- Triple (extraction exists in Funs.lean but blocked by (a)):
@[spec]
theorem montgomery_reduce_element_spec
    (value : Std.I32) (hb : value.val.natAbs ≤ 2^16 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_reduce_element value
    ⦃ ⇓ r => ⌜ (r.val * (2^16 : Int) - value.val) % 3329 = 0
              ∧ r.val.natAbs ≤ 3328 + 1665 ⌝ ⦄ := by
  sorry
-/

/- **L0.4 `vector.portable.arithmetic.montgomery_multiply_fe_by_fer`** — Montgomery multiply.

    Hax post (`vector/portable/arithmetic.rs:172-187`):
    `result ≡ fe · fer · R⁻¹ (mod q)`, i.e. `≡ x · y (mod q)` when
    `fer ≡ y · R (mod q)`.

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
-/
/- Triple (extraction exists in Funs.lean but blocked by (a)):
@[spec]
theorem montgomery_multiply_fe_by_fer_spec
    (fe : Std.I16) (fer : Std.I16)
    (hfe : fe.val.natAbs ≤ 3328) (hfer : fer.val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_fe_by_fer fe fer
    ⦃ ⇓ r => ⌜ (r.val * (2^16 : Int) - fe.val * fer.val) % 3329 = 0
              ∧ r.val.natAbs ≤ 3328 + 1665 ⌝ ⦄ := by
  sorry
-/

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

    All Layer-1 lemmas are [stub-only — extraction missing]: the
    underlying `vector.portable.arithmetic.{add, sub, …}` defs are
    not yet in `Funs.lean`.

    ## L1.1 `PortableVector.add` — pointwise wrapping_add. Spec post:
    `∀ i < 16, r.elements[i].val % 2^16 = (lhs[i].val + rhs[i].val) % 2^16`.
    Tier: loop-induction.

    ## L1.2 `PortableVector.sub` — pointwise wrapping_sub. Mirror of L1.1.

    ## L1.3 `PortableVector.barrett_reduce` — each lane via L0.2.
    Tier: loop-induction. Depends on L0.2.

    ## L1.4 `PortableVector.montgomery_multiply_by_constant` — each
    lane via L0.4 with the fer constant `c`. Pre: `|c| ≤ 3328`,
    `|vec[i]| ≤ 3328 ∀ i`. Tier: loop-induction. Depends on L0.4.

    ## L1.5 `PortableVector.cond_subtract_3329` — per-element
    `if x ≥ 3329 then x - 3329 else x`. Tier: loop-induction.

    ## L1.6 `PortableVector.negate` — pointwise `wrapping_neg`.
    Tier: loop-induction.

    ## L1.7 `PortableVector.multiply_by_constant` — pointwise
    `wrapping_mul(c)` (different from L1.4 — no Montgomery).
    Tier: loop-induction.

    ## L1.8 `PortableVector.bitwise_and_with_constant` — pointwise AND.
    Tier: loop-induction + bv_decide per element.

    ## L1.9 `PortableVector.shift_right` — pointwise `>>` by const.
    Tier: loop-induction.

    ## L1.10 `PortableVector.reducing_from_i32_array` — per-lane
    `montgomery_reduce_element` (L0.3) from a 16-element I32 slice.
    Tier: loop-induction. Depends on L0.3.
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
    (zeta : Std.I16) (a_idx b_idx : Std.Usize) :
    ⦃ ⌜ a_idx.val < 16 ∧ b_idx.val < 16 ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta a_idx b_idx
    ⦃ ⇓ _r => ⌜ True -- butterfly equivalence to Spec.lift_field_mont
              ⌝ ⦄ := by
  sorry
-/

/- **L2.2 `vector.portable.ntt.ntt_layer_1_step`** — 4 butterflies on
    distinct (a, b, ζ) index pairs within one PortableVector at
    positions (0↔2, 1↔3, 4↔6, 5↔7) using ζ₀, ζ₀, ζ₁, ζ₁.

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
-/

/- **L2.3 `ntt_layer_2_step`** — 2 butterflies. Depends on L2.1.
    [F*-port: `Vector.Portable.Ntt.ntt_layer_2_step` lines 146–215;
     same shape as L2.2 with different index table.] ~3 hours.

    **L2.4 `ntt_layer_3_step`** — 1 butterfly. Depends on L2.1.
    [F*-port: ibid, same structure.] ~3 hours.

    **L2.5 `inv_ntt_step`** — Gentleman–Sande inverse butterfly.
    Computes `(a, b) := (a + b, montgomery_multiply((a - b), ζ))`.
    Spec anchor: `Spec.inv_butterfly`. Mirror of L2.1. Depends on L0.4.
    [F*-port: `Vector.Portable.Ntt.inv_ntt_step` lines 221–280;
     forward uses `montgomery_multiply` on b then add/sub, inverse
     uses `barrett_reduce` on sum then `montgomery_multiply` on diff.]

    **L2.6 `inv_ntt_layer_1_step`** — bundled 4 inverse butterflies.
    [F*-port: lines 285–360, mirror of L2.2.]

    **L2.7 `inv_ntt_layer_2_step` / `inv_ntt_layer_3_step`** — analogous.
    [F*-port: lines 365–430.]

    All [extraction exists, blocked by (a)]. Total L2.5–L2.7: ~6 hours.
-/

/- **L2.8 `vector.portable.ntt.accumulating_ntt_multiply`** — base-case
    poly multiplication in NTT domain. The Rust impl computes a
    "running sum" of (a₀·b₀ + ζ²·a₁·b₁, a₀·b₁ + a₁·b₀) for each pair
    of coefficients (degree-2 polys mod X² − ζ²; FIPS-203 § 4.3.3,
    Algorithm 11). The accumulator is an `[I32; 256]` accumulator
    that gets folded via `montgomery_reduce_element` later. Three
    variants (with cache, fill cache, use cache) optimize the inner
    constant load.

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
    (h_zeta : zeta_i.val = 63) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1 OpsInst zeta_i re bnd
    ⦃ ⇓ r => ⌜ r.1.val = 127 ⌝ ⦄ := by
  sorry
-/

/- **L3.2 `ntt.ntt_at_layer_2`** — same shape with zeta_i 31→63.
    **L3.3 `ntt.ntt_at_layer_3`** — same shape with zeta_i 15→31.
    Both ## Depends on L2.3/L2.4 + zeta_spec.
    [F*-port: `Libcrux_ml_kem.Ntt.ntt_at_layer_{2,3}_` (lines 132–336);
     structural duplication of L3.1.]
    ## Tier: loop-induction. ~2 days each.
-/

/- **L3.4 `ntt.ntt_at_layer_4_plus`** — generic outer NTT layer (the
    parameter `layer` is `∈ [4, 7]`; see Funs.lean line 396). Nested
    loop: outer over rounds, inner over `step_vec = (1 << layer) / 16`
    butterfly positions.

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
-/

/- **L3.5 `ntt.ntt_at_layer_7`** — outermost layer (no zeta_i).

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
-/

/- **L3.7 `ntt.ntt_vector_u`** — same shape as L3.6 with different
    initial coefficient bound + initial zeta_i = 0 (skip layer 7).
    [F*-port: `Libcrux_ml_kem.Ntt.ntt_vector_u`, ~80 LOC F*; mirror
     of L3.6.] Tier: algebraic-close-required, ~3 days.

    **L3.8 `invert_ntt_montgomery`** — full 7-layer iNTT. Spec anchor:
    `Spec.ntt_inverse(p)`. Mirror of L3.6; final iNTT layer
    multiplies by `1441 = R · (1/128 mod q)` to absorb the 1/N
    normalization factor.
    [F*-port: `Libcrux_ml_kem.Invert_ntt.fst` (~700 LOC). **Critical
     difference**: the final inverse layer does NOT apply `1/128`;
     it's deferred to consumers (L6.2, L6.4) via the
     `montgomery_multiply 1441` step. Post must use the
     `bit_intt_mont_form` predicate (= "lane carries
     `R⁻¹ · 128 · spec_value mod q`"). The keystone bridge is
     `lemma_intt_mont_finalize_fe` from upstream Chunk.fst:1703 —
     port via ZMod 3329 cast in ~10 Lean lines. ~4 days incl. the
     opaque predicate design.]
    Tier: algebraic-close-required (~4 days).
    [extraction missing for invert_ntt.*]
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

    [extraction missing] None of L4.x is extracted.

    ## L4.1 `vector.portable.sampling.rej_sample` — per-vector
    rejection sampling. Takes 24 bytes, returns up to 16 sampled
    coefficients + accepted count. Spec anchor:
    `Spec.rej_sample_step(bytes)`. 8-iter loop; per iter extract two
    12-bit candidates `d1, d2` from `(b₀ | b₁<<8 | b₂<<16)` via L0.1,
    accept if `< 3329`. Depends on L0.1, `Spec.rej_sample_step`.
    Tier: loop-induction.

    ## L4.2 `sampling.sample_from_xof` — drives L4.1 over SHAKE128
    stream until 256 coefficients accepted. Spec anchor:
    `Spec.sample_ntt`. Couples to
    `LibcruxIotSha3.Sponge.Shake.shake128_spec` for the bytes.
    Tier: loop-induction + SHA-3 coupling.

    ## L4.3 `sampling.sample_poly_cbd` — centered binomial. Per byte:
    extract bits via shift+mask; centered sum in [-η, η]. Spec
    anchor: `Spec.sample_poly_cbd eta prf_output`.
    Tier: loop-induction.
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

    [extraction missing] None of L5.x is extracted.

    ## L5.1 `compress_1` — d=1 (1 bit per coefficient).
    Tier: bv-decide-close.

    ## L5.2 `compress<D>` — generic D ∈ {4, 5, 10, 11}.
    Tier: scalar-tac-close (nonlinear).

    ## L5.3 `decompress_ciphertext_coefficient<D>` — inverse of L5.2.
    Tier: scalar-tac-close.

    ## L5.4 `serialize_D` for D ∈ {1, 4, 5, 10, 11, 12} — pack 16
    field elements of bit width D into D·2 bytes.
    Tier: bv-decide-close (one per D).

    ## L5.5 `deserialize_D` for D ∈ {1, 4, 5, 10, 11, 12} — inverse
    of L5.4. Tier: bv-decide-close.

    ## L5.6 `byte_encode (byte_decode x) = x` — round-trip identity at
    D=12 (needed for `public_key_modulus_check`, FIPS-203 §7.2).
    Tier: bv-decide-close + new pure-Lean Roundtrip helper.
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

    The Layer-6 driver `PolynomialRingElement.poly_barrett_reduce` IS
    extracted (Funs.lean lines 483, 505, 519); the rest are
    [extraction missing].
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
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce OpsInst re
    ⦃ ⇓ _r => ⌜ True -- each lane is barrett-reduced
              ⌝ ⦄ := by
  sorry
-/

/- **L6.2 `PolynomialRingElement.{add_to_ring_element, add_error_reduce,
    add_message_error_reduce, add_standard_error_reduce}`** — the 4
    fused-add-reduce variants. Spec anchors are the corresponding
    `Spec.add_*` in `specs/ml-kem/src/polynomial.rs:19-91`.

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
-/

/- **L6.3 `PolynomialRingElement.accumulating_ntt_multiply`** (+
    `_fill_cache` / `_use_cache`) — NTT-domain polynomial
    multiplication. 16-iter loop over `Vector::accumulating_ntt_multiply`
    (L2.8) with the per-pair zeta values from
    `ZETAS_TIMES_MONTGOMERY_R[64 + 4i + {0,1,2,3}]`.

    Spec anchor: `Spec.ntt_multiply(a, b) = multiply_ntts(a, b)`
    (`specs/ml-kem/src/ntt.rs:359`).

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

    **L6.5 `serialize_uncompressed_ring_element`** /
    **`compress_then_serialize_message`** /
    **`compress_then_serialize_ring_element`** — the byte serializers
    at ring-element granularity. Each is a 16-iter loop:
    `to_unsigned_field_modulus → Vector::compress_D → Vector::serialize_D`.

    Per-iter: L5.2 (compress_D) + L5.4 (serialize_D). The byte buffer
    is written via `Std.Array.update` over `serialized[D·2*i..D·2*(i+1)]`
    slices; `Std.Array.set_val_eq` simp lemmas collapse. Depends on
    L5.2, L5.4 + new helper `to_unsigned_field_modulus_spec`. Tier:
    loop-induction + bv-decide-close per element.

    **L6.6 `deserialize_*_ring_element`** — inverse of L6.5. Same
    structure with L5.3 + L5.5 chained. Tier: loop-induction.

    **L6.7 `deserialize_ring_elements_reduced`** — outer K-loop over
    L6.6. Used by `ind_cpa::serialize_public_key` and
    `validate_public_key`. Tier: loop-induction.
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

    [extraction missing] None of `matrix.*` is in Funs.lean.

    ## L7.1 `sample_matrix_A` — generates `K × K` Â via SHAKE128.
    Spec: `Spec.expand_a(rho, transpose)`. Nested 2-level loop K × K.
    Per-iter: L4.2 + `PolynomialRingElement::from_i16_array_spec`
    (new). Depends on L4.2. Tier: nested loop-induction.

    ## L7.2 `compute_As_plus_e` — `t̂ = Â◦ŝ + ê`. K-loop over inner
    `accumulating_ntt_multiply` calls + outer
    `add_standard_error_reduce`. Depends on L6.3, L6.2. Tier:
    loop-induction.

    ## L7.3 `compute_vector_u` — `u = NTT⁻¹(Aᵀ◦r̂) + e₁`. Similar
    K-loop with inverse NTT and `add_error_reduce`. Depends on L6.3,
    L6.2, L3.8. Tier: loop-induction.

    ## L7.4 `compute_ring_element_v` — `v = NTT⁻¹(t̂ᵀ◦r̂) + e₂ + m`.
    Depends on L6.3, L6.2 `add_message_error_reduce`, L3.8. Tier:
    loop-induction.

    ## L7.5 `compute_message` — `m̂ = v − NTT⁻¹(sᵀ◦û)` (decrypt
    side). Depends on L6.3, L3.8, L6.4 `subtract_reduce`. Tier:
    loop-induction.
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

    ## L8.2 `ind_cpa.encrypt` — K-PKE.Encrypt (Algorithm 13). 9 steps
    mixing L4.3, L3.6, L7.3, L7.4, L5.3, L6.5. Tier:
    needs-new-helper-tier.

    ## L8.3 / L8.4 `encrypt_c1` / `encrypt_c2` — split variants of
    L8.2. Direct corollaries via ciphertext-half projection.

    ## L8.5 `ind_cpa.decrypt` — K-PKE.Decrypt (Algorithm 14). Chain
    L6.6 + L5.3 + L6.7 + L7.5 + L6.5 + L5.1. Tier:
    needs-new-helper-tier.
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

    ## L9.2 `ind_cca.validate_private_key` — verify dk well-formed AND
    embedded H(ek) matches. Couples to
    `LibcruxIotSha3.Sponge.Shake.sha256_ema_spec`. Depends on L9.1.
    Tier: needs-new-helper-tier.

    ## L9.3 `ind_cca.generate_keypair` — ML-KEM.KeyGen (Algorithm 19).
    Sequence:
    1. Split `randomness[64]` into `(d, z)` (32 bytes each)
    2. K-PKE.KeyGen(d) → (ek, ind_cpa_sk)  (L8.1)
    3. dk = ind_cpa_sk || ek || H(ek) || z (byte concatenation)
    4. Output (ek, dk)
    Depends on L8.1, sha256_ema_spec, `Spec.mlkem_keygen`. Tier:
    needs-new-helper-tier.

    ## L9.4 `ind_cca.encapsulate` — ML-KEM.Encaps (Algorithm 20).
    Sequence:
    1. K̄ = G(m || H(ek)) → (K, r)  (SHA3-512)
    2. c = K-PKE.Encrypt(ek, m, r)  (L8.2)
    3. Output (c, K)
    Depends on L8.2, sha3_512_ema_spec, sha256_ema_spec,
    `Spec.mlkem_encaps`. Tier: needs-new-helper-tier.

    ## L9.5 `ind_cca.decapsulate` — ML-KEM.Decaps (Algorithm 21).
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

/-- **B.1 `mont_R_inv_q`** — `R · 169 ≡ 1 (mod q)`. -/
theorem mont_R_inv_q : ((2^16 : Nat) * 169) % 3329 = 1 := by decide

/-- **B.2 `mont_1441_eq_inv128`** — `1441 · 128 ≡ R² (mod q)`. Combined
    with one Montgomery reduce (× R⁻¹), the net factor on the value
    after `montgomery_multiply(b, 1441)` is `R / 128 mod q`. This is
    exactly the "Montgomery-scale-by-1/128" used in `add_error_reduce`,
    `subtract_reduce`, etc. to absorb the deferred 1/N normalization
    of inverse NTT. -/
theorem mont_1441_eq_inv128 : (1441 * 128) % 3329 = (2^16 * 2^16) % 3329 := by decide

/-- **B.3 `mont_2285_eq_R_mod_q`** — `2285 ≡ 2^16 (mod q)`. -/
theorem mont_2285_eq_R_mod_q : 2285 = (2^16 : Nat) % 3329 := by decide

/-- **B.4 `mont_1353_eq_RR_mod_q`** — `1353 ≡ R² (mod q)`. -/
theorem mont_1353_eq_RR_mod_q : 1353 = (2^16 * 2^16) % 3329 := by decide

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
