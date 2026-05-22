#!/usr/bin/env python3
"""One-shot extraction driver for libcrux-iot ML-KEM → aeneas-Lean.

Mirrors `libcrux-iot/sha3/hax_aeneas.py`. Three responsibilities:

1. Pin/check the hax + aeneas toolchain versions (matches the `Hax`
   Lake dep pin in `proofs/aeneas-lean/lakefile.toml`).
2. Run `cargo hax into aeneas-lean` with a Charon `--start-from` list
   chosen to bound the extraction boundary.
3. Patch the generated `LibcruxIotMlKem/Extraction/Funs.lean` in-place
   so it builds against the current `rust-core-models` pin (see
   `LibcruxIotMlKem/Extraction/Missing.lean` for the symbols being
   stubbed under the `PHASE0B-MISSING-PATCH` marker).

To widen the extraction boundary, append entries to `START_FROM`
below. Each `crate::<path>::*` becomes a Charon translation root;
Charon transitively pulls in every callee. Plan.lean's KNOWN BLOCKER
(b) lists the per-layer roots that unblock each L0–L10 lemma cluster.
"""

import os
import re
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "7b4bd97058e0fcbf9135b76297ca91942f2327a6"
AENEAS_VERSION = "b5c45e84"

# Charon translation roots. Anything not reachable from these is
# dropped from `Funs.lean`. Today's NTT-only boundary matches the
# legacy `hax_aeneas.sh`. To widen: add Plan.lean L1–L10 paths, e.g.
#   "crate::vector::portable::arithmetic::*",
#   "crate::invert_ntt::*",
#   "crate::sampling::*", "crate::serialize::*", "crate::compress::*",
#   "crate::polynomial::*", "crate::matrix::*",
#   "crate::ind_cpa::*", "crate::ind_cca::*",
#   "crate::mlkem512::*", "crate::mlkem768::*", "crate::mlkem1024::*".
START_FROM = [
    "crate::ntt::*",
    "crate::vector::portable::ntt::*",
]


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
# `LibcruxIotMlKem/Extraction/Missing.lean` lives *inside* `Extraction/`
# (alongside the auto-generated `Funs.lean`); current aeneas reports it
# as "unchanged file" but a future version could regenerate it and
# clobber our hand-written stubs. Snapshot+restore protects against
# that.
HAND_WRITTEN_GUARDED = [
    Path("proofs/aeneas-lean/LibcruxIotMlKem/Extraction/Missing.lean"),
]
guarded_snapshots = {p: p.read_bytes() for p in HAND_WRITTEN_GUARDED if p.exists()}

charon_args = " ".join(f"--start-from {root}" for root in START_FROM)
# NOTE: deliberately NOT setting `RUSTFLAGS=--cfg charon` here (unlike
# sha3/hax_aeneas.py). ml-kem source has no `#[cfg(charon)]` items, and
# enabling the cfg causes the sha3 dep to fail to compile because
# `sha3/src/state.rs:10` drops `derive(Debug)` on KeccakState under
# `not(any(eurydice, charon))` while `sha3/src/lib.rs:319` keeps it on
# UnbufferedXofState (which we pull in via the `unbuffered-xof` feature
# in our Cargo.toml) only under `not(eurydice)`. Restore the RUSTFLAGS
# line if ml-kem ever needs charon-gated annotations of its own.
result = subprocess.run(
    ["cargo", "hax", "into", "aeneas-lean", f"--charon-args={charon_args}"],
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
if result.returncode != 0:
    sys.exit(result.returncode)

# Restore any hand-written files aeneas may have clobbered.
for p, snapshot in guarded_snapshots.items():
    if not p.exists() or p.read_bytes() != snapshot:
        print(f"warning: restoring hand-written {p} from snapshot", file=sys.stderr)
        p.write_bytes(snapshot)

funs_lean = Path("proofs/aeneas-lean/LibcruxIotMlKem/Extraction/Funs.lean")
content = funs_lean.read_text()

# Add `import CoreModels` + `open core_models` (aeneas-lean emits only
# `import Aeneas`), and re-insert the `PHASE0B-MISSING-PATCH` block
# that pulls in our hand-written stubs for symbols the pinned
# rust-core-models doesn't export (see Missing.lean's header).
content = content.replace(
    "import Aeneas",
    "import Aeneas\n"
    "import CoreModels\n"
    "-- BEGIN PHASE0B-MISSING-PATCH (re-inserted by hax_aeneas.py)\n"
    "-- Stubs five symbols dangling under the current rust-core-models\n"
    "-- pin: I16↔I32 / U32→I32 casts, libcrux_secrets Classify.Blanket,\n"
    "-- and core_models.num.I16.wrapping_neg. See Missing.lean for the\n"
    "-- full list.\n"
    "import LibcruxIotMlKem.Extraction.Missing\n"
    "-- END PHASE0B-MISSING-PATCH\n"
    "open core_models",
    1,
)

funs_lean.write_text(content)
