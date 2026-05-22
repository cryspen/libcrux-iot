#!/usr/bin/env python3
"""One-shot extraction driver for hacspec ML-KEM → aeneas-Lean.

Mirrors `specs/sha3/hax_aeneas.py`. Extracts the *entire* spec crate
(no `--start-from` boundary, unlike the impl extraction in
`libcrux-iot/ml-kem/hax_aeneas.py`) and patches the generated
`HacspecMlKem/Extraction/Funs.lean` to import `HacspecMlKem.Missing`
and to apply known mis-extraction workarounds.
"""

import os
import re
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "7b4bd97058e0fcbf9135b76297ca91942f2327a6"
AENEAS_VERSION = "b5c45e84"


def check_version(cmd: list[str], expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        if os.environ.get("SKIP_VERSION_CHECK") == "1":
            print(f"warning: version mismatch for {cmd[0]} (expected {expected!r}); continuing because SKIP_VERSION_CHECK=1", file=sys.stderr)
            return
        print(f"Version mismatch for {cmd[0]}: expected {expected!r} in output:\n{output}", file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], HAX_VERSION)
check_version(["aeneas", "-version"], AENEAS_VERSION)

# Snapshot any hand-written files that aeneas might overwrite.
# `HacspecMlKem/Missing.lean` lives one level up from `Extraction/`
# and aeneas doesn't currently touch it, but we belt-and-suspender
# guard anyway in case future hax-evit/aeneas versions widen the set
# of files they manage.
HAND_WRITTEN_GUARDED = [
    Path("proofs/aeneas-lean/HacspecMlKem/Missing.lean"),
]
guarded_snapshots = {p: p.read_bytes() for p in HAND_WRITTEN_GUARDED if p.exists()}

# NOTE: sha3 spec sets `RUSTFLAGS=--cfg charon` because
# `specs/sha3/src/lib.rs` has `cfg_attr(charon, feature(register_tool))`.
# ml-kem spec source has no `cfg(charon)` items, so we omit the flag
# here. The hacspec_sha3 dep is built without the cfg too; that's fine
# because the cfg_attr only enables a (currently unused) nightly
# feature gate. Restore RUSTFLAGS if ml-kem spec ever gains
# charon-gated annotations.
result = subprocess.run(
    ["cargo", "hax", "into", "aeneas-lean"],
    env=os.environ.copy(),
    capture_output=True,
    text=True,
)

_ANSI = re.compile(r'\x1b\[[0-9;]*[a-zA-Z]')
def should_suppress(line: str) -> bool:
    plain = _ANSI.sub('', line)
    return plain.startswith("warning: hax: aeneas version mismatch:") or plain.startswith("warning: hax: charon version mismatch:")

for line in result.stdout.splitlines():
    if not should_suppress(line):
        print(line)
for line in result.stderr.splitlines():
    if not should_suppress(line):
        print(line, file=sys.stderr)

funs_lean = Path("proofs/aeneas-lean/HacspecMlKem/Extraction/Funs.lean")

# Aeneas can return non-zero while still emitting a partial `Funs.lean`
# (today: 9 errors stemming from closures inside `array::from_fn` and a
# nested-return in `matrix::sample_matrix_A`). Apply the import patch
# whenever the file exists; only abort if extraction produced nothing
# at all.
if not funs_lean.exists():
    sys.exit(result.returncode if result.returncode != 0 else 1)
if result.returncode != 0:
    print(
        f"warning: hax/aeneas exited with code {result.returncode}; "
        f"applying patches to partial {funs_lean}.",
        file=sys.stderr,
    )
# Restore any hand-written files aeneas may have clobbered.
for p, snapshot in guarded_snapshots.items():
    if not p.exists() or p.read_bytes() != snapshot:
        print(f"warning: restoring hand-written {p} from snapshot", file=sys.stderr)
        p.write_bytes(snapshot)

content = funs_lean.read_text()

# Pull in our hand-written stubs (`HacspecMlKem.Missing`) and open
# `core_models` so the qualified `core_models.…` references resolve.
content = re.sub(
    r"import Aeneas",
    "import Aeneas\nimport HacspecMlKem.Missing\nopen core_models",
    content,
    count=1,
)

# `ntt.ZETAS` is a 128-element initializer that trips the default
# `maxRecDepth = 512` when elaborated. Bump to 1000 just for that def
# (mirrors the sha3 impl script's treatment of `RC_INTERLEAVED_*`).
content = content.replace(
    "/-- [hacspec_ml_kem::ntt::ZETAS]",
    "set_option maxRecDepth 1000 in\n/-- [hacspec_ml_kem::ntt::ZETAS]",
    1,
)

# Newer hax-evit emits `fmt::rt::Argument::new_display` with two
# arguments (the `Display` instance + the value), but the
# rust-core-models lake pin `b67ccf1` defines it with one. The blocks
# below appear only in panic-path formatting (`fail panic` follows
# them), so we block-comment them away. Same pattern as the sha3 impl
# script's treatment of the `Argument.new_display` mis-extraction.
PANIC_FMT_BLOCK_RX = re.compile(
    r"    let a ←\n"
    r"      core_models\.fmt\.rt\.Argument\.new_display\n"
    r"        core_models\.Usize\.Insts\.Core_modelsFmtDisplay [a-zA-Z_0-9]+\n"
    r"    let _ ←\n"
    r"      core_models\.fmt\.Arguments\.new\n"
    r"        \(Array\.make [0-9]+#usize \[\n"
    r"(?:[^\]]+\n)+"
    r"          \]\) \(Array\.make [0-9]+#usize \[ a \]\)"
)
def _comment_panic_fmt(m: 're.Match[str]') -> str:
    return "/-\n" + m.group(0) + "\n-/"
content = PANIC_FMT_BLOCK_RX.sub(_comment_panic_fmt, content)

# Field-name mismatches between hax-evit ee467e6's emission and the
# rust-core-models b67ccf1 trait structs. Each pattern below shows up
# in auto-generated trait-impl literals; we drop or rename the
# offending field.

# `cmp.PartialEq` has only `eq` — drop the synthesised `ne` field.
content = re.sub(
    r"\n  ne := [^\n]+(?=\n})",
    "",
    content,
)

# `cmp.Eq` has only `PartialEqInst` — drop the synthesised
# `assert_receiver_is_total_eq` field.
content = re.sub(
    r"\n  assert_receiver_is_total_eq :=\n    [^\n]+(?=\n})",
    "",
    content,
)

# Three sites trip Lean's bind elaboration: a `do let X ← Y; Z(... X
# ...)` where `Z` returns `Result (Array T D)` with `D` a const-generic.
# Lean infers the continuation lambda as `(X : T) → Result (Array T D)`
# (an explicit pi-binder that looks dependent even though `D` doesn't
# depend on `X`) and fails to unify with the expected non-dependent
# `T → Result ?β`. Replacing the final `let ← ; expr` with an explicit
# `>>= fun X => expr` dodges the `do`-desugar that introduces the
# explicit pi-binder.

# Site 1 — `sampling.sample_poly_cbd`:
content = content.replace(
    "  let bits ← serialize.bytes_to_bits ETA512 bytes\n"
    "  parameters.createi 256#usize\n"
    "    (sampling.sample_poly_cbd.closure.Insts.Core_modelsOpsFunctionFnTupleUsizeFieldElement\n"
    "    ETA64 ETA512) (eta, bits)",
    "  serialize.bytes_to_bits ETA512 bytes >>= fun bits =>\n"
    "  parameters.createi 256#usize\n"
    "    (sampling.sample_poly_cbd.closure.Insts.Core_modelsOpsFunctionFnTupleUsizeFieldElement\n"
    "    ETA64 ETA512) (eta, bits)",
    1,
)

# Site 2 — `serialize.byte_decode`:
content = content.replace(
    "  let decoded ← serialize.byte_decode_generic 32#usize 256#usize D256 b d\n"
    "  parameters.createi 256#usize\n"
    "    (serialize.byte_decode.closure.Insts.Core_modelsOpsFunctionFnTupleUsizeFieldElement\n"
    "    D32 D256) decoded",
    "  serialize.byte_decode_generic 32#usize 256#usize D256 b d >>= fun decoded =>\n"
    "  parameters.createi 256#usize\n"
    "    (serialize.byte_decode.closure.Insts.Core_modelsOpsFunctionFnTupleUsizeFieldElement\n"
    "    D32 D256) decoded",
    1,
)

# Site 3 — `serialize.compress_then_serialize_message` (single-bind def;
# rewrite the entire `:= do` body to use explicit `>>=`):
content = content.replace(
    "def serialize.compress_then_serialize_message\n"
    "  (re : Array parameters.FieldElement 256#usize) :\n"
    "  Result (Array Std.U8 32#usize)\n"
    "  := do\n"
    "  let a ← compress.compress re 1#usize\n"
    "  serialize.byte_encode 32#usize 256#usize a 1#usize",
    "def serialize.compress_then_serialize_message\n"
    "  (re : Array parameters.FieldElement 256#usize) :\n"
    "  Result (Array Std.U8 32#usize) :=\n"
    "  compress.compress re 1#usize >>= fun a =>\n"
    "  serialize.byte_encode 32#usize 256#usize a 1#usize",
    1,
)

# `fmt.Debug` field is named `dbg_fmt`, not `fmt` (mirror of the
# sha3-impl `hax_aeneas.py` patch). The trait-impl literals look like:
#   def X.Insts.Core_modelsFmtDebug : core_models.fmt.Debug Y := {
#     fmt := X.Insts.Core_modelsFmtDebug.fmt
#   }
# Or with the body line-broken:
#   def X.Insts.Core_modelsFmtDebug : core_models.fmt.Debug Y := {
#     fmt :=
#       X.Insts.Core_modelsFmtDebug.fmt
#   }
# Rename the field, anchored on `.Insts.Core_modelsFmtDebug.fmt` so we
# don't catch random `fmt :=` lines.
content = re.sub(
    r"^  fmt :=(?:[ \n]+)([^\n]*\.Insts\.Core_modelsFmtDebug\.fmt)$",
    r"  dbg_fmt :=\n    \1",
    content,
    flags=re.MULTILINE,
)

funs_lean.write_text(content)
