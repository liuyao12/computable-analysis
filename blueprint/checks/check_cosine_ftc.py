#!/usr/bin/env python3
"""Check the cosine-FTC examples and reject proof holes in the dependency audit."""
from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
NEW_MODULES = (
    ROOT / "ComputableAnalysis/DovetailedFTC.lean",
    ROOT / "ComputableAnalysis/CosineFTC.lean",
)
AUDIT = ROOT / "blueprint/checks/CosineFTCAudit.lean"


def main() -> int:
    for source in NEW_MODULES:
        # These modules deliberately contain no declarations of axioms,
        # admitted proof terms, or native_decide invocations. Dependencies
        # are checked separately by Lean's transitive axiom collector.
        match = re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", source.read_text())
        if match:
            print(f"Forbidden proof token {match.group()!r} in {source}", file=sys.stderr)
            return 1

    command = ["lake", "env", "lean", str(AUDIT)]
    # LEAN_BIN is useful when checking against an already-built local import
    # path. Normal repository and CI usage always goes through lake env.
    if lean_bin := os.environ.get("LEAN_BIN"):
        command = [lean_bin, str(AUDIT)]
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    text = result.stdout + result.stderr
    log_path = Path(tempfile.gettempdir()) / "cosine-ftc-audit.log"
    log_path.write_text(text)
    if result.returncode:
        print(text)
        return result.returncode
    if re.search(r"\bsorryAx\b", text):
        print("The transitive theorem audit contains sorryAx.", file=sys.stderr)
        return 1
    if "integral_cosPi_equiv_sinPi_endpoints" not in text:
        print("The requested theorem was not included in the axiom audit.", file=sys.stderr)
        return 1
    native = set(re.findall(r"[A-Za-z0-9_.]+\._native\.native_decide\.[A-Za-z0-9_]+", text))
    print("Cosine FTC: examples and transitive axiom audit passed; no sorryAx.")
    print(f"Existing upstream native_decide axiom dependencies: {len(native)}.")
    print(f"Full axiom audit: {log_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
