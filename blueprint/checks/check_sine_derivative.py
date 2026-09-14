"""Build and audit the rational sine derivative, without modifying sources.

Run from any directory:
    python3 blueprint/checks/check_sine_derivative.py

--no-build is for CI after a successful explicit Lake build.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
EXPECTED = {
    "ComputableAnalysis.FixedSchedule.sine_derivative_cosine",
    "ComputableAnalysis.FixedSchedule.sin'_eq_cos",
    "ComputableAnalysis.RotationSeries.uniformRotationSinOnTwo_hasDerivativeOnInterval",
    "ComputableAnalysis.RotationSeries.uniformRotationCosOnTwo_hasDerivativeOnInterval",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true")
    args = parser.parse_args()
    try:
        if not args.no_build:
            subprocess.run(
                ["lake", "build", "ComputableAnalysis.SineDerivative"],
                cwd=ROOT, check=True,
            )
        result = subprocess.run(
            ["lake", "env", "lean", "blueprint/checks/SineDerivativeAudit.lean"],
            cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    except FileNotFoundError:
        print("ERROR: Lake is not on PATH; install the repository's pinned Lean toolchain.", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as exc:
        if exc.stdout:
            print(exc.stdout)
        print(f"ERROR: Lean check failed with exit status {exc.returncode}.", file=sys.stderr)
        return 1

    print(result.stdout, end="")
    # Greedy name matching deliberately retains Lean identifiers such as sin'_eq_cos.
    matches = re.findall(
        r"^'(.+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout,
        flags=re.MULTILINE,
    )
    found = {name for name, _ in matches}
    if found != EXPECTED or len(matches) != len(EXPECTED):
        print(f"ERROR: expected exactly {sorted(EXPECTED)}, received {sorted(found)}.", file=sys.stderr)
        return 1
    for name, body in matches:
        axioms = {item.strip() for item in body.split(",") if item.strip()}
        unexpected = axioms - ALLOWED
        if unexpected:
            print(f"ERROR: {name} depends on prohibited axioms {sorted(unexpected)}.", file=sys.stderr)
            return 1
        print(f"PASS: {name}: no sorryAx, native-evaluation axiom, or custom axiom.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
