# Hand-fixes applied to make `specs/ml-kem` extract cleanly to aeneas-Lean

This document inventories every workaround applied (in Rust source, in
`hax_aeneas.py`, and in `proofs/aeneas-lean/HacspecMlKem/Missing.lean`)
to take the hacspec ML-KEM spec from "243 Lean errors after first
extraction" to "0 errors". Each entry names the upstream component that
should eventually subsume it.

Sister doc on the impl side: `libcrux-iot/ml-kem/HAX_AENEAS_PATCHES.md`.

Toolchain pin at time of writing:

| Component | Pin |
|---|---|
| `cargo-hax` | hax-evit `7b4bd97058e0fcbf9135b76297ca91942f2327a6` (matched by the new-examples branch HEAD `ee467e6`; our `hax_aeneas.py` accepts either via `SKIP_VERSION_CHECK=1`) |
| `aeneas` | `b5c45e84` |
| `rust-core-models` (transitive via hax-evit) | `b67ccf195ab8a10ecd0bed465a1539931418ac19` |
| `lean-toolchain` | `leanprover/lean4:v4.28.0-rc1` |

A coordinated upgrade to v4.30.0-rc2 + newer rust-core-models was
attempted and reverted — see "Upstream blockers" §1 below.

---

## Part 1 — Rust source changes in `specs/ml-kem/src/`

### 1.1 Closure-body hoists for [aeneas#924](https://github.com/AeneasVerif/aeneas/issues/924)

Aeneas's interpreter cannot translate `core::array::from_fn`-style
closures whose bodies combine `if`/`else` with captured variables.
Symptom: extraction reports `[Error] Unimplemented` at
`interp/Interp.ml:550` and emits a `sorry`-bodied closure `.call`.

Fix: lift each closure body into a free function `fn ..._at(captures...,
i: usize) -> T`, so the remaining closure becomes a single
non-branching call `createi(|i| ..._at(captures..., i))`.

Sites:

| File | Function | Helper introduced |
|---|---|---|
| `invert_ntt.rs` | `ntt_inverse_layer` | `ntt_inverse_layer_zeta` |
| `invert_ntt.rs` | `ntt_inverse_layer_n` | `ntt_inverse_layer_n_at` |
| `ntt.rs` | `ntt_layer_n` | `ntt_layer_n_at` |
| `ntt.rs` | `ntt_multiply_n` | `ntt_multiply_n_at` |
| `matrix.rs` | `multiply_matrix_by_column` | `multiply_matrix_by_column_at` |
| `serialize.rs` | `bitvector_to_bounded_ints` | `bitvector_to_bounded_ints_at` |
| `serialize.rs` | `serialize_public_key` | `serialize_public_key_at` |

Each helper has a comment with the issue link.

**Upstream:** aeneas#924 — once the interpreter supports the if/else +
capture pattern, the hoists become dead weight.

### 1.2 Nested-loop early-return hoist for [aeneas#822](https://github.com/AeneasVerif/aeneas/issues/822)

Aeneas: "Returns inside of nested loops are not supported yet". Triggered
by the `?` operator (which desugars to `return Err(e)`) inside two
nested `for` loops.

Site: `matrix.rs::sample_matrix_A`. The inner `for j` loop was lifted
into a `sample_matrix_A_row` helper. Each function now has its `?` inside
at most one (non-nested) loop.

**Upstream:** aeneas#822 — early returns inside loops that can be
replaced with `break`. Once supported, the helper can fold back into
the body.

### 1.3 Parameter renames to avoid Lean dot-projection ambiguity

aeneas extracts unqualified call paths like `matrix.add_polynomials`,
which Lean's parser ambiguously interprets as either
`hacspec_ml_kem.matrix.add_polynomials` (the namespaced function) or a
field projection on a local variable named `matrix`. When the local
variable wins, Lean errors with "`Subtype.add_polynomials` does not
exist".

Sites: `matrix.rs` — `transpose` and `multiply_matrix_by_column` (and
its helper) had their `matrix: &Matrix<RANK>` parameter renamed to `m`.

**Upstream:** aeneas — emit fully qualified call paths
(`_root_.matrix.add_polynomials`) so local names cannot shadow.

### 1.4 `Debug` derive replaced with `#[cfg(all(not(hax), test))]` manual impls

The auto-derived `Debug` extracts to a `Core_modelsFmtDebug.fmt` def
calling `core::fmt::Formatter::debug_struct_field1_finish` and
`DebugStruct`'s chained builder methods, which aeneas's interpreter
cannot translate. Even when the body becomes `sorry`, the surrounding
trait instance literal uses `fmt :=` against the `dbg_fmt` field of
`core_models.fmt.Debug`, breaking the Lean build.

Sites:
- `parameters.rs::FieldElement` — `Debug` removed from derive list;
  manual impl gated on `#[cfg(all(not(hax), test))]`.
- `sampling.rs::BadRejectionSamplingRandomnessError` — same.

The cfg restricts to test builds so `cargo test --release` still
formats failure messages, but extraction never sees the impl.

**Upstream:** rust-core-models — model `core::fmt::Formatter` /
`DebugStruct` well enough that aeneas can translate
auto-derived Debug. Or aeneas — accept `derive(Debug)` and emit a stub.

### 1.5 All `#[hax_lib::fstar::*]` annotations removed

47 `fstar::options("--z3rlimit N")` lines + 1 `fstar::replace(...)`
block on `createi`. These are F*-extraction-only and irrelevant for
aeneas-Lean. Removed by user request to declutter the spec.

---

## Part 2 — Python patches in `hax_aeneas.py`

The script's responsibilities (in order):

### 2.1 Version pinning (lines 24–46)

`HAX_VERSION` / `AENEAS_VERSION` pins match `sha3/hax_aeneas.py` and
the lakefile `Hax` dep. `SKIP_VERSION_CHECK=1` env var bypasses for
ad-hoc runs against newer hax-evit binaries.

### 2.2 `Missing.lean` snapshot/restore guard (lines 28–37, 89–93)

Reads `HacspecMlKem/Missing.lean` before running `cargo hax`, restores
from snapshot after if changed. Belt-and-suspenders: current aeneas
doesn't touch this file (it's outside `Extraction/`), but a future
version could regenerate it and clobber our stubs.

### 2.3 Partial-extraction tolerance (lines 84–94)

Aeneas can return non-zero while still emitting a partial `Funs.lean`.
The script applies patches whenever the file exists; only aborts if
nothing was emitted.

### 2.4 Import patches (lines 96–105)

Inserts `import HacspecMlKem.Missing` and `open core_models` after
`import Aeneas`. The `HacspecMlKem.Missing` transitively imports
`HacspecSha3` for reuse of the slice/array index/copy stubs.

### 2.5 Three explicit-`>>=` rewrites for Lean bind-elaboration quirk

Symptom: Lean's elaborator rejects `do let X ← Y; Z(...X...)` with
"Application type mismatch" when `Z` returns `Result (Array T D)` and
`D` is a `Std.Usize` parameter (not a literal `#usize` value).

Why: `do let X ← Y; Z` desugars *before* type elaboration to a lambda
wrapped in an explicit pi-binder `(X : Tx) → Result (Array T D)`. The
unifier refuses to identify it with the non-dependent `Tx → Result ?β`
that `Bind.bind` requires, even though the two are definitionally equal
(D doesn't actually depend on X).

Empirically (eight annotation positions tested, see PR discussion),
**no type-annotation can fix this** — annotations apply post-desugar.
The only working fix is replacing `do let X ← Y; Z(X)` with
`Y >>= fun X => Z(X)`, which builds the lambda with the bind's
expected domain shape directly.

Sites patched:
- `sampling.sample_poly_cbd`: `bytes_to_bits ETA512 bytes >>= fun bits => parameters.createi 256 ... (eta, bits)`
- `serialize.byte_decode`: `byte_decode_generic ... >>= fun decoded => parameters.createi 256 ... decoded`
- `serialize.compress_then_serialize_message`: whole-def rewrite to use `>>=`

**Upstream:**
- Lean — improve bind elaboration to unify `(x : α) → β` with `α → β`
  when `β` doesn't depend on `x`.
- Or aeneas — emit `>>= fun` rather than `do let ←` for these patterns.

### 2.6 `maxRecDepth 1000` for `ntt.ZETAS`

The 128-element initializer trips the default `maxRecDepth = 512`.
Python-inserts `set_option maxRecDepth 1000 in` before the def.
Mirrors the sha3-impl script's treatment of `RC_INTERLEAVED_*`.

**Upstream:** rust-core-models / aeneas — autoinsert the option for
large literal initializers.

### 2.7 Block-comment of panic-path `fmt.Arguments.new` blocks

Newer hax-evit emits `core_models.fmt.rt.Argument.new_display` with two
arguments (Display instance + value), but the lake-pinned rust-core-models
`b67ccf1` defines it with one. These calls only appear in panic-path
formatting (followed by `fail panic`), so block-commenting them away is
safe. Mirrors the sha3-impl script.

**Upstream:** rust-core-models — bump definition to match hax-evit's
emission. Or hax-evit — emit the 1-arg form against older
rust-core-models.

### 2.8 Field-name fixups in trait-impl literals

Three patterns, each anchored to the auto-derive literal shape so they
don't catch unrelated text:

| Patch | What it does |
|---|---|
| Drop `ne := …` line | `core_models.cmp.PartialEq` struct has only `eq`; the auto-derived `Eq` adds a `ne` field that doesn't exist |
| Drop `assert_receiver_is_total_eq := …` line | `core_models.cmp.Eq` struct has only `PartialEqInst`; auto-derive adds a non-existent field |
| Rename `fmt := …` → `dbg_fmt := …` | `core_models.fmt.Debug` field is `dbg_fmt`, not `fmt` (mirror of sha3-impl `hax_aeneas.py`) |

**Upstream:** rust-core-models — add `ne` to `cmp.PartialEq`,
`assert_receiver_is_total_eq` to `cmp.Eq`, rename `dbg_fmt` to `fmt` (or
vice versa, whichever conventions hax-evit emits).

---

## Part 3 — Hand-written stubs in `HacspecMlKem/Missing.lean`

`Missing.lean` `import`s `HacspecSha3` to reuse common stubs (slice/array
SliceIndex for `Range`/`RangeFrom`, `Slice.copy_from_slice`,
`Result.unwrap`, `TryFromSliceError.Debug`). Beyond that, an
"UPSTREAM-TO-rust-core-models" section adds 20 ml-kem-specific stubs:

| Group | Stub | Reason |
|---|---|---|
| Slice indexing | `RangeToUsize` SliceIndex | only `Range` / `RangeFrom` exist in `HacspecSha3.Missing`; ml-kem also uses `RangeTo` |
| Slice indexing | `RangeFull` SliceIndex | ditto, for `&s[..]` syntax |
| `?` operator | `Result.Try::branch` | parses `result?` into ControlFlow |
| `?` operator | `Result.Try::from_residual` | re-wraps residual via `From` |
| Slice ops | `Slice.split_at` | thin wrapper over `Aeneas.Std.core.slice.Slice.split_at` |
| Slice→Array | `SharedAArray.…TryFromSliceError.try_from` | thin wrapper over `Aeneas.Std.core.array.TryFromSharedArraySlice.try_from` |
| Chunked iteration | `Slice.chunks_exact` | **`sorry`-bodied**: rust-core-models declares `slice.Slice T := T` (a phantom alias), so `ChunksExact.elements : Slice T = T` and we cannot construct a meaningful value from a real slice. Only blocks `ind_cca.public_key_modulus_check`. |
| Chunked iteration | `ChunksExact.…Iterator.next` | no-op terminator stub (same root cause) |
| Comparisons | `Bool.PartialEq` | `HacspecSha3.Missing` has integer instances but not `Bool` |
| Comparisons | `U16.PartialOrd`, `U16.Ord` | spec uses `<` on U16 |
| Iteration | `I32.RangeStep` | for `for i in 0..n : i32` loops; mirror of `StepUsize` in `FunsPrologue` |
| Formatting (panic paths) | `Usize.FmtDisplay`, `Shared0T.FmtDebug`, `U16.FmtDebug`, `fmt.Arguments.new`, `Formatter.{write_str,debug_struct_field1_finish}` | no-op formatting; only reached in panic paths |
| Array ops | `array.Array.as_slice` | trivial cast |
| Slice comparison | `Slice.PartialEq` | always-true stub (only consumer in panic path) |
| Slice comparison | `Shared1A.…PartialEq.ne` | forwarder over Slice.PartialEq |

**Upstream:** all of the above to `rust-core-models`. The phantom-aliased
`slice.Slice T := T` is the most blocking — it makes `ChunksExact`
semantically unusable.

---

## Upstream blockers (priority order)

### 1. hax-evit Lean library is pinned behind its Rust binary

hax-evit's `hax-lib/proof-libs/aeneas-lean/lakefile.toml` (every
relevant branch we checked: `main`, `new-examples`, `aeneas`, etc.)
pins:
- `rust-core-models = b67ccf1` (old)
- `aeneas = 4e02d6d8` (old)
- `lean-toolchain = v4.28.0-rc1`

But the hax-evit *Rust* binary at `ee467e6` emits extraction conventions
that match **newer** rust-core-models (e.g., `RangeTo` SliceIndex,
`fmt.rt.Argument.new_display` with 2-arg signature, `cmp.PartialEq` with
`ne` field). This mismatch is the root cause of most §2.7 and §2.8
patches.

A coordinated upgrade to `rust-core-models main (67c9e02)` + `aeneas main
(60ad1071)` + `lean-toolchain v4.30.0-rc2` was attempted. It failed
because newer rust-core-models is a wholesale refactor (different
layout `CoreModels/{Core,Alloc,Command}.lean`, different symbol paths
like `marker.Copy`, `fmt.Debug`, `ops.range.Range` moved or gone) that
the hax-evit binary doesn't yet know how to emit against. Reverted.

The proper fix is to bump hax-evit's Lean lakefile to match its binary's
conventions, which requires upstream coordination across hax-evit +
rust-core-models + aeneas.

### 2. Aeneas issues open

- [aeneas#924](https://github.com/AeneasVerif/aeneas/issues/924) —
  Extraction fails for closure with if-then-else and variable capture.
  *Blocks: §1.1 (7 hoists).*
- [aeneas#822](https://github.com/AeneasVerif/aeneas/issues/822) —
  Support for early returns inside loops that can be replaced with
  breaks. *Blocks: §1.2 (nested-loop hoist in `sample_matrix_A`).*

### 3. Lean bind-elaboration quirk

`do let X ← Y; Z(X)` produces an explicit-pi-binder lambda when Z's
return type involves a const-generic-indexed `Array`. The `>>=`
rewrite (§2.5) avoids it, but a proper Lean-elaborator fix or aeneas
emission-style change would let us drop the rewrites.

### 4. `slice.Slice T := T` in rust-core-models

This phantom alias breaks any structure that holds a `Slice T`. We
worked around for `ChunksExact` by `sorry`-ing the constructor, but it
prevents real iteration-based proofs. Would benefit from a proper slice
model upstream.

---

## Maintenance notes

- `Missing.lean` is **hand-written**; the script's snapshot/restore
  guard (§2.2) prevents accidental clobbering. If you need to extend it,
  add to the UPSTREAM-TO-rust-core-models section and update the table
  in Part 3 of this doc.
- The 8 hoists in Part 1 (§1.1 + §1.2) each have a comment in the Rust
  source linking the aeneas issue. Search for `aeneas/issues/924` /
  `aeneas/issues/822` to find them.
- The Python patches (§2.5–2.8) match exact extracted-text patterns. If
  hax-evit's emission changes, the regexes/string-matches will need
  updating. Each patch in `hax_aeneas.py` carries a `# <site>` comment
  identifying the function it targets.
- To run extraction from a clean state:
  ```bash
  cd specs/ml-kem
  SKIP_VERSION_CHECK=1 ./hax_aeneas.py
  cd proofs/aeneas-lean && lake build
  ```
  expected end state: 244 defs, 0 sorries, 0 errors.
