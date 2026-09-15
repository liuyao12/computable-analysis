#!/usr/bin/env python3
"""Enforce the source/package boundary between the core and Mathlib comparison.

Lean separately checks mathematical dependencies in ComparisonAudit.lean.
This check scans every native module, not just the current import root.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import tomllib

ROOT = Path(__file__).resolve().parents[2]


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i+2]
        c = text[i]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2; continue
            if pair == '-/': depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if string:
            # Preserve line positions but don't interpret a string's contents as imports.
            out.append('\n' if c == '\n' else ' '); i += 1
            if c == '\\' and i < len(text): out.append(' '); i += 1
            elif c == '"': string = False
            continue
        if pair == '/-': depth = 1; out.extend('  '); i += 2; continue
        if pair == '--':
            while i < len(text) and text[i] != '\n': out.append(' '); i += 1
            continue
        if c == '"': string = True; out.append(' '); i += 1; continue
        out.append(c); i += 1
    if depth or string: raise ValueError('Unterminated comment or string in Lean source')
    return ''.join(out)


def imports(text: str) -> list[str]:
    return [token for line in strip_comments(text).splitlines()
            if (m := re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$', line))
            for token in m.group(1).split()]


def forbidden(name: str) -> bool:
    return name.split('.')[0] in {'Mathlib','MathlibComparison'}


def check(root: Path) -> dict:
    root_config = tomllib.loads((root/'lakefile.toml').read_text())
    comparison_config = tomllib.loads((root/'comparison/lakefile.toml').read_text())
    if any(r['name'].lower() == 'mathlib' for r in root_config.get('require', [])):
        raise ValueError('The core package must not require Mathlib')
    # Elan accepts a leading v in release tags; Mathlib's cache requires its
    # exact spelling. Compare normalized versions without changing core config.
    normalize = lambda text: re.sub(r':v(?=\d)', ':', text.strip())
    if normalize((root/'lean-toolchain').read_text()) != normalize((root/'comparison/lean-toolchain').read_text()):
        raise ValueError('The core and comparison toolchains must match')
    reqs = {r['name']:r for r in comparison_config['require']}
    if reqs['ComputableAnalysis'].get('path') != '..':
        raise ValueError('Comparison must import this repository, not a separate native copy')
    pin = reqs['mathlib'].get('rev','')
    if not re.fullmatch('[0-9a-f]{40}',pin): raise ValueError('Mathlib must have an immutable revision')
    lock = json.loads((root/'comparison/lake-manifest.json').read_text())
    locked = {p['name']:p for p in lock['packages']}
    if locked['mathlib']['rev'] != pin or locked['ComputableAnalysis'].get('dir') != '..':
        raise ValueError('The comparison lockfile disagrees with its package configuration')
    files = sorted((root/'ComputableAnalysis').rglob('*.lean')) + [root/'ComputableAnalysis.lean']
    edges = []
    for path in files:
        for name in imports(path.read_text()):
            if forbidden(name): raise ValueError(f'Forbidden native import: {path}: {name}')
            edges.append((str(path.relative_to(root)),name))
    for path in (root/'comparison/MathlibComparison').rglob('*.lean'):
        code = strip_comments(path.read_text())
        if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b',code,re.M):
            raise ValueError(f'Unapproved proof shortcut in {path}')
    # Parser regression tests include nested comments, strings, and module import prefixes.
    assert imports('/- import Mathlib /- import Mathlib.X -/ -/\npublic import ComputableAnalysis.Basic') == ['ComputableAnalysis.Basic']
    assert imports('def s := "import Mathlib"\nimport Mathlib.Data.Real.Basic') == ['Mathlib.Data.Real.Basic']
    assert forbidden('MathlibComparison.RealModel') and not forbidden('ComputableAnalysis.Basic')
    return {'nativeModulesScanned':len(files),'nativeImportEdges':len(edges),
            'mathlibRevision':pin,'noMathlibInCore':True,'comparisonUsesSameCore':True,
            'matchingToolchains':True}


def main() -> None:
    ap = argparse.ArgumentParser(); ap.add_argument('--root',type=Path,default=ROOT)
    args = ap.parse_args()
    print(json.dumps(check(args.root),indent=2))


if __name__ == '__main__': main()
