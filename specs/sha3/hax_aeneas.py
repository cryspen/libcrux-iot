#!/usr/bin/env python3

import subprocess
import re
import sys
from pathlib import Path

import os

HAX_VERSION = "7b4bd97058e0fcbf9135b76297ca91942f2327a6"
AENEAS_VERSION = "b5c45e84"


def check_version(cmd: list[str], name: str, expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        print(f"Version mismatch for {name}: expected {expected!r} in output:\n{output}", file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], "hax", HAX_VERSION)
check_version(["aeneas", "-version"], "aeneas", AENEAS_VERSION)

result = subprocess.run(
    ["cargo", "hax", "into", "aeneas-lean"],
    env={**os.environ, "RUSTFLAGS": "--cfg hax_backend_lean"},
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
