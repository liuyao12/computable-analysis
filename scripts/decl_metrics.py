#!/usr/bin/env python3
"""Rough declaration-size metrics for the Lean sources.

This intentionally stays simple: it counts source-line spans from one top-level
declaration to the next.  It is useful for spotting propositions whose proofs
are getting bulky, not for judging mathematical depth.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path
import re
import sys


DECL_RE = re.compile(
    r"^(?P<kind>theorem|lemma|def|structure|inductive|abbrev|class)\s+"
    r"(?P<name>[A-Za-z0-9_'.]+)"
)


@dataclass
class Decl:
    file: Path
    kind: str
    name: str
    start: int
    end: int

    @property
    def lines(self) -> int:
        return self.end - self.start + 1


def lean_files(root: Path) -> list[Path]:
    return sorted((root / "ComputableAnalysis").glob("*.lean"))


def declarations(path: Path) -> list[Decl]:
    lines = path.read_text(encoding="utf-8").splitlines()
    starts: list[tuple[int, str, str]] = []
    for i, line in enumerate(lines, start=1):
        match = DECL_RE.match(line)
        if match:
            starts.append((i, match.group("kind"), match.group("name")))

    decls: list[Decl] = []
    for idx, (start, kind, name) in enumerate(starts):
        end = starts[idx + 1][0] - 1 if idx + 1 < len(starts) else len(lines)
        decls.append(Decl(path, kind, name, start, end))
    return decls


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--kind", choices=["all", "proofs"], default="proofs")
    parser.add_argument("--min-lines", type=int, default=1)
    args = parser.parse_args()

    rows: list[Decl] = []
    for path in lean_files(args.root):
        for decl in declarations(path):
            if args.kind == "proofs" and decl.kind not in {"theorem", "lemma"}:
                continue
            if decl.lines >= args.min_lines:
                rows.append(decl)

    writer = csv.writer(sys.stdout)
    writer.writerow(["file", "kind", "name", "start", "end", "lines"])
    for decl in sorted(rows, key=lambda d: (-d.lines, str(d.file), d.start)):
        writer.writerow([
            decl.file.relative_to(args.root).as_posix(),
            decl.kind,
            decl.name,
            decl.start,
            decl.end,
            decl.lines,
        ])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
