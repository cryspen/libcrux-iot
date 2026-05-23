#!/usr/bin/env python3
"""One-shot extraction driver for hacspec SHA-3 → aeneas-Lean.

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

result = subprocess.run(
    in_hax_switch(["cargo", "hax", "into", "aeneas-lean"]),
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
if result.returncode != 0:
    sys.exit(result.returncode)

funs_lean = Path("proofs/aeneas-lean/HacspecSha3/Extraction/Funs.lean")
content = funs_lean.read_text()
content = re.sub(
    r"import Aeneas",
    "import Aeneas\nimport HacspecSha3.Missing\nopen core_models",
    content,
)

# https://github.com/AeneasVerif/aeneas/issues/984
content = re.sub(
    r"(/-- \[hacspec_sha3::keccak_f::theta\]:)",
    "set_option Aeneas.customDoElab false in\n\\1",
    content,
)
funs_lean.write_text(content)
