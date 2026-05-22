# Hand-fixes applied to make `libcrux-iot/ml-kem` extract cleanly to aeneas-Lean

This document inventories every workaround applied (in
`hax_aeneas.py` and in
`proofs/aeneas-lean/LibcruxIotMlKem/Extraction/Missing.lean`) to keep
the libcrux-iot ML-KEM impl extracting against the pinned hax-evit +
rust-core-models graph. No Rust source changes are currently needed
on the impl side (the user has not asked for them, and the extraction
boundary is intentionally narrow — see `START_FROM` below).

Sister doc on the spec side:
`specs/ml-kem/HAX_AENEAS_PATCHES.md` (significantly larger — most
hand-fixes live there, since the spec uses richer Rust idioms).

Toolchain pin at time of writing:

| Component | Pin |
|---|---|
| `cargo-hax` | hax-evit `7b4bd97058e0fcbf9135b76297ca91942f2327a6` (in practice we run with the new-examples branch HEAD `ee467e6`; `SKIP_VERSION_CHECK=1` accepts the drift) |
| `aeneas` | `b5c45e84` |
| `rust-core-models` | `b67ccf195ab8a10ecd0bed465a1539931418ac19` (transitive via hax-evit lakefile) |
| `lean-toolchain` | `leanprover/lean4:v4.28.0-rc1` |

---

## Part 1 — Rust source changes

**None.** Unlike the spec side (which has 8 closure-body hoists for
[aeneas#924](https://github.com/AeneasVerif/aeneas/issues/924), a
nested-loop hoist for
[aeneas#822](https://github.com/AeneasVerif/aeneas/issues/822), and
parameter renames), the libcrux-iot impl source is shaped to avoid
these aeneas limitations from the start — the impl already uses
explicit `for` loops with index variables instead of
`array::from_fn(closure)` patterns.

---

## Part 2 — Python patches in `hax_aeneas.py`

The script mirrors `sha3/hax_aeneas.py` with two notable differences,
both flagged with code comments.

### 2.1 Version pinning (lines 41–53)

Matches the sha3-impl script's pins. `SKIP_VERSION_CHECK=1` env var
bypasses for ad-hoc runs with newer hax-evit binaries.

### 2.2 `START_FROM` extraction-boundary control (lines 30–40)

```python
START_FROM = [
    "crate::ntt::*",
    "crate::vector::portable::ntt::*",
]
```

These become `--start-from crate::path::*` flags passed to
`charon-args`. Each entry adds a Charon translation root; any item not
transitively reachable from at least one root is excluded from
extraction.

Today's two roots cover only the NTT slice (52 defs). To widen, append
entries — `Plan.lean`'s "KNOWN BLOCKER (b)" maps Layer 1–10 to specific
paths. For "extract everything", append the three `mlkem{512,768,1024}::*`
paths.

This is purely a **boundary** control, not a workaround for a hax/aeneas
bug. Documented here so re-extraction is reproducible.

### 2.3 `Missing.lean` snapshot/restore guard (lines 55–67, 92–96)

Reads `LibcruxIotMlKem/Extraction/Missing.lean` before running
`cargo hax`, restores from snapshot after if changed. **Important
here** (unlike the spec side): the impl Missing.lean lives *inside*
the `Extraction/` directory that aeneas writes to. Current aeneas
reports it as "unchanged file" in its output, suggesting it tracks the
file. A future version could regenerate it and clobber our hand-written
stubs.

### 2.4 `RUSTFLAGS=--cfg charon` deliberately NOT set (lines 70–78)

The sha3-impl script sets this flag, but doing so for ml-kem extraction
trips a pre-existing cfg-mismatch bug in `libcrux-iot/sha3/src/lib.rs`:

- `sha3/src/state.rs:10` — `KeccakState` skips `derive(Debug)` under
  `not(any(eurydice, charon))`.
- `sha3/src/lib.rs:319` — `UnbufferedXofState` (which contains a
  `KeccakState`) only skips `Debug` under `not(eurydice)`, NOT `charon`.

Under `--cfg charon`, `KeccakState` drops Debug but `UnbufferedXofState`
still derives Debug → compile error.

`ml-kem/Cargo.toml` enables `libcrux-iot-sha3/unbuffered-xof`, so we
hit this when extracting ml-kem (which transitively builds sha3 with
the unbuffered-xof feature on). Standalone sha3 extraction doesn't
trip it because `unbuffered-xof` isn't a sha3 default feature.

We worked around by not setting `--cfg charon` (ml-kem source has no
`#[cfg(charon)]` items, so the cfg has no effect on ml-kem extraction
quality). If ml-kem ever needs charon-gated annotations of its own,
restore the `RUSTFLAGS` line **and** fix sha3's cfg gate.

**Upstream (sha3 source):** make `sha3/src/lib.rs:319` match
`sha3/src/state.rs:10`:
```rust
-    #[cfg_attr(not(eurydice), derive(Debug))]
+    #[cfg_attr(not(any(eurydice, charon)), derive(Debug))]
```

### 2.5 Import patches (lines 98–117)

Inserts `import CoreModels`, `open core_models`, and `import
LibcruxIotMlKem.Extraction.Missing` after `import Aeneas`. Wraps the
inserted import in a `BEGIN/END PHASE0B-MISSING-PATCH` comment block
that's grep-able and self-documenting.

---

## Part 3 — Hand-written stubs in `Extraction/Missing.lean`

Five symbols dangling under the current rust-core-models pin
`b67ccf1`, plus three abbrev wrappers for hax-evit `ee467e6`'s more
aggressive name-qualification.

### 3.1 Original `libcrux_secrets` shims (5 defs)

The libcrux_secrets crate provides classify/declassify shims that
newer rust-core-models exports as Aeneas instances; the current pin
predates them. Symbols stubbed:

| Symbol | What it does |
|---|---|
| `Aeneas.Std.I16.Insts.Libcrux_secretsIntCastOps.as_i32` | I16 → I32 sign-extend (via `IScalar.cast .I32`) |
| `Aeneas.Std.I32.Insts.Libcrux_secretsIntCastOps.as_i16` | I32 → I16 truncate (via `IScalar.cast .I16`) |
| `Aeneas.Std.U32.Insts.Libcrux_secretsIntCastOps.as_i32` | U32 → I32 zero-extend (via `UScalar.hcast .I32`) |
| `libcrux_secrets.traits.Classify.Blanket.classify` | polymorphic id → Result wrapper |
| `core_models.num.I16.wrapping_neg` | I16 → I16 wrapping negation (via `wrapping_sub_i16 0 x`) |

### 3.2 Newer-hax-evit name-qualification abbrevs (3 abbrevs)

Newer hax-evit (post-`7b4bd97`) emits cast ops with the
`libcrux_secrets.` prefix rather than letting them resolve to
`Aeneas.Std.…` via `open Aeneas.Std`:

```lean
abbrev libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 :=
  Aeneas.Std.I16.Insts.Libcrux_secretsIntCastOps.as_i32
-- … similarly for I32→I16 and U32→I32
```

The abbrevs forward to the Aeneas.Std-namespaced defs above. Using
`abbrev` (not `def`) keeps definitional equality so the existing simp
lemma set in `Equivalence/L0_FieldArith.lean` (which references
`Aeneas.Std.I16.Insts.…` directly) still fires on the new form.

**Upstream:**
- Move `libcrux_secrets` IntCastOps shims into rust-core-models so
  newer pins expose them natively — replaces §3.1.
- Either: stabilize hax-evit's name-qualification across versions, or
  have aeneas always emit the fully-qualified form — replaces §3.2.

---

## Upstream blockers (priority order)

### 1. hax-evit Lean library is pinned behind its Rust binary

Same root cause as documented in the spec-side
`HAX_AENEAS_PATCHES.md` "Upstream blockers" §1. The binary at
`ee467e6` emits conventions matching newer pins; the pinned Lean
graph hasn't caught up. The coordinated v4.30 bump attempted on the
spec side surfaced rust-core-models's major refactor and was reverted.

### 2. sha3 cfg-mismatch bug (referenced from §2.4 above)

The one-line fix in `sha3/src/lib.rs:319` would let us re-enable
`--cfg charon` for ml-kem extraction without breaking the sha3 dep
build. Low-risk PR.

### 3. rust-core-models version drift

The 3 abbrevs in §3.2 are workarounds for hax-evit's evolving
extraction conventions. A pin bump (once §1 is resolved) makes them
unnecessary.

---

## Maintenance notes

- `LibcruxIotMlKem/Extraction/Missing.lean` is **hand-written**; the
  script's snapshot/restore guard (§2.3) prevents accidental
  clobbering. If you add stubs, document them in §3.
- To widen the extraction boundary beyond NTT, append to `START_FROM`
  (§2.2). See `Plan.lean`'s "KNOWN BLOCKER (b)" for the Layer 1–10
  mapping.
- To run extraction from a clean state:
  ```bash
  cd libcrux-iot/ml-kem
  SKIP_VERSION_CHECK=1 ./hax_aeneas.py
  cd proofs/aeneas-lean && lake build
  ```
  expected end state: 52 defs, 0 errors (with the current NTT-only
  boundary).
- New extraction-time symbols can surface as you widen the boundary.
  Each new "Unknown identifier" gets a stub in `Missing.lean` (§3 in
  this doc gets a new row); each new mis-extracted literal might need
  a Python patch in `hax_aeneas.py` (mirror the spec-side `fmt`-rename
  / `ne`-drop patches if applicable).
