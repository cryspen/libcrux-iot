#!/usr/bin/env python3
"""One-shot extraction driver for libcrux-iot SHA-3 → aeneas-Lean.

## Toolchain setup (matched cargo-hax + hax-engine pair)

This script auto-runs `cargo-hax` and `aeneas` inside the `hax-evit`
opam switch via `opam exec --switch=hax-evit -- …`, so you do NOT need
to `eval $(opam env --switch=hax-evit)` first. The switch provides a
matched `cargo-hax` + `hax-engine` pair (commit ee467e6ac3) — the
plain `hax` switch contains a 0.3.7 hax-engine that would produce
wrong output.

Override the switch with `HAX_OPAM_SWITCH=<other-switch>` in env if
you need a different one.
"""

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "ee467e6ac3f107047427b696878d0b5f76560d84"
AENEAS_VERSION = "b5c45e84"
HAX_OPAM_SWITCH = os.environ.get("HAX_OPAM_SWITCH", "hax-evit")


def in_hax_switch(cmd: list[str]) -> list[str]:
    """Wrap `cmd` to execute under the configured opam switch."""
    return ["opam", "exec", f"--switch={HAX_OPAM_SWITCH}", "--"] + cmd


def check_version(cmd: list[str], expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        if os.environ.get("SKIP_VERSION_CHECK") == "1":
            print(f"warning: version mismatch for {cmd[0]} (expected {expected!r}); continuing because SKIP_VERSION_CHECK=1", file=sys.stderr)
            return
        print(f"Version mismatch for {cmd[0]}: expected {expected!r} in output:\n{output}", file=sys.stderr)
        sys.exit(1)


if shutil.which("opam") is None:
    print("error: `opam` not found on PATH; install opam or set HAX_OPAM_SWITCH=", file=sys.stderr)
    sys.exit(1)

check_version(in_hax_switch(["cargo", "hax", "--version"]), HAX_VERSION)
check_version(in_hax_switch(["aeneas", "-version"]), AENEAS_VERSION)

# Items to keep opaque at the Charon boundary (extract signature only,
# skip body). The aeneas-lean backend does not honor `#[hax_lib::opaque]`
# / `#[cfg_attr(hax, hax_lib::exclude)]` source annotations uniformly,
# so we forward patterns to charon explicitly.
#
# **`impl_digest_trait::*` is opaque.** The 4 `impl_hash_traits!` macro
# invocations at `src/impl_digest_trait.rs:41-44` produce trait-impl
# glue that wraps the verified `sha{224,256,384,512}_ema` entry points
# with input-length checks and a `Result`-typed return. The wrappers
# themselves contain no verified content — they're API plumbing. New
# hax-evit (commit ee467e6) widens extraction to pull these in and
# aeneas can't translate the bodies, breaking the build. Opaque-ing
# the module at Charon level keeps the verified Keccak primitives
# extracted and skips the unverified wrappers.
OPAQUE = [
    "crate::impl_digest_trait::*",
]
charon_args = " ".join(f"--opaque {item}" for item in OPAQUE)

result = subprocess.run(
    in_hax_switch(["cargo", "hax", "into", "aeneas-lean", f"--charon-args={charon_args}"]),
    env={**os.environ, "RUSTFLAGS": "--cfg charon"},
    capture_output=True,
    text=True,
)

# Suppress version mismatch warnings. (We check versions above.)
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

funs_lean = Path("proofs/aeneas-lean/LibcruxIotSha3/Extraction/Funs.lean")

# Aeneas can return non-zero while still emitting a partial `Funs.lean`.
# Apply the patches whenever the file exists; only abort if extraction
# produced nothing at all. (Mirrors the tolerant pattern in
# `specs/ml-kem/hax_aeneas.py`.)
if not funs_lean.exists():
    sys.exit(result.returncode if result.returncode != 0 else 1)
if result.returncode != 0:
    print(
        f"warning: hax/aeneas exited with code {result.returncode}; "
        f"applying patches to partial {funs_lean}.",
        file=sys.stderr,
    )

content = funs_lean.read_text()

content = content.replace(
    "import Aeneas",
    "import Aeneas\nimport LibcruxIotSha3.Extraction.Missing\nopen core_models",
    1,
)

# This definition is hitting the recursion limit:
content = content.replace(
    "/-- [libcrux_iot_sha3::keccak::RC_INTERLEAVED_1]",
    "set_option maxRecDepth 1000 in\n/-- [libcrux_iot_sha3::keccak::RC_INTERLEAVED_1]",
    1,
)

# This definition is hitting the recursion limit:
content = content.replace(
    "/-- [libcrux_iot_sha3::keccak::RC_INTERLEAVED_0]",
    "set_option maxRecDepth 1000 in\n/-- [libcrux_iot_sha3::keccak::RC_INTERLEAVED_0]",
    1,
)

# Wrong signature of `core_models.fmt.rt.Argument.new_display`
block = (
    "    let a ←\n"
    "      core_models.fmt.rt.Argument.new_display\n"
    "        core_models.Usize.Insts.Core_modelsFmtDisplay i\n"
    "    let a1 ←\n"
    "      core_models.fmt.rt.Argument.new_display\n"
    "        core_models.Usize.Insts.Core_modelsFmtDisplay RATE\n"
    "    let _ ←\n"
    "      core_models.fmt.Arguments.new\n"
    "        (Array.make 7#usize [\n"
    "          192#u8, 3#u8, 32#u8, 62#u8, 32#u8, 192#u8, 0#u8\n"
    "          ]) (Array.make 2#usize [ a, a1 ])"
)
content = content.replace(block, "/-\n" + block + "\n-/", 1)

# Wrong field name in `core_models.fmt.Debug`
content = content.replace(
    "  fmt := ",
    "  dbg_fmt := ",
    1,
)


funs_lean.write_text(content)
