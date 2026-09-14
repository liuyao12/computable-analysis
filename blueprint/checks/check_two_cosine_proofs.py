#!/usr/bin/env python3
"""Compile the two-proof audit and check types, dependencies, and trust boundary."""
from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MODULES = (
    "DovetailedFTC", "IntervalSelections", "FiniteRiemannAlgebra",
    "CosineIntegralData", "GeometricSineFiniteBounds", "GeometricSineDirectBounds",
    "ConcaveSecantFTC", "GeometricSineConcavity", "ConcaveFTCIntegral",
    "CosineFTC", "CosineIntegralViaFTC",
)
AUDIT = ROOT / "blueprint/checks/TwoCosineProofsAudit.lean"
EXPECTED = (
    "PASS: identical theorem types, including all parameters and hypotheses",
    "PASS: neither proof uses the other; direct route avoids the sine derivative and concave FTC",
    "PASS: computed derivative validity uses concavity and cross-stage secant compatibility",
    "PASS: all audited theorems are free of sorryAx",
)


def main() -> int:
    for module in MODULES:
        source = ROOT / "ComputableAnalysis" / f"{module}.lean"
        match = re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", source.read_text())
        if match:
            print(f"Forbidden proof token {match.group()!r} in {source}", file=sys.stderr)
            return 1
        if re.search(r"^import\s+(?:Mathlib|Std|Batteries)(?:\.|\s|$)", source.read_text(), re.M):
            print(f"Forbidden foundation import in {source}", file=sys.stderr)
            return 1

    command = ["lake", "env", "lean", str(AUDIT)]
    if lean_bin := os.environ.get("LEAN_BIN"):
        command = [lean_bin, str(AUDIT)]
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    text = result.stdout + result.stderr
    log = Path(tempfile.gettempdir()) / "two-cosine-proofs-audit.log"
    log.write_text(text)
    if result.returncode:
        print(text)
        return result.returncode
    missing = [line for line in EXPECTED if line not in text]
    if missing:
        print("Missing checks: " + "; ".join(missing), file=sys.stderr)
        return 1
    for line in text.splitlines():
        if line.startswith(("PASS:", "AXIOMS ")):
            print(line)
    print(f"Full dependency and axiom report: {log}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
