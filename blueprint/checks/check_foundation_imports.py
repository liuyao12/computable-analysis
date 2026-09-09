#!/usr/bin/env python3
"""Source-level import boundary audit; not a compiled-environment proof.

Run from a repository checkout. Only core Init/Lean/Std and local mathematical
modules are allowed in active sources. Historical dot-directory copies are
reported separately. A future compiled check must additionally inspect the
elaborated environment and theorem dependencies.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from collections import deque
from pathlib import Path

CORE = {"Init", "Lean", "Std"}
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
IMPORT = re.compile(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)")
FORBIDDEN = re.compile(r"ℝ|ℂ|\bMathlib(?:\.|\b)|\b_root_\.(?:Real|Complex)\b")


def code_only(text: str) -> str:
    """Blank nested block comments, line comments, and strings, keeping lines."""
    chars = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                chars[i:i + 2] = '  '
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                chars[i:i + 2] = '  '
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    chars[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\' and i + 1 < len(text):
                chars[i] = ' '
                if text[i + 1] != '\n':
                    chars[i + 1] = ' '
                i += 2
            else:
                if text[i] == '"':
                    string = False
                if text[i] != '\n':
                    chars[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            chars[i:i + 2] = '  '
            depth = 1
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0:
                j = len(text)
            chars[i:j] = ' ' * (j - i)
            i = j
        elif text[i] == '"':
            chars[i] = ' '
            string = True
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError('unclosed block comment or string')
    return ''.join(chars)


def imports(text: str) -> list[str]:
    result = []
    for match in IMPORT.finditer(code_only(text)):
        for name in match.group(1).split():
            if not MODULE.fullmatch(name):
                raise ValueError(f'unsupported import syntax: {name!r}')
            result.append(name)
    return result


def main() -> int:
    root = Path(subprocess.check_output(
        ['git', 'rev-parse', '--show-toplevel'], text=True).strip())
    tracked = subprocess.check_output(
        ['git', '-C', str(root), 'ls-files', '-z']).decode().split('\0')
    active = sorted(p for p in tracked if p.endswith('.lean') and (
        '/' not in p or p.startswith('ComputableAnalysis/')))
    other = sorted(p for p in tracked if p.endswith('.lean') and p not in active)
    if not active:
        raise ValueError('no active Lean sources found')
    by_module = {p[:-5].replace('/', '.'): p for p in active}
    graph = {}
    external = set()
    failures = []
    for module, path in by_module.items():
        text = (root / path).read_text(encoding='utf-8')
        cleaned = code_only(text)
        for hit in FORBIDDEN.finditer(cleaned):
            line = cleaned[:hit.start()].count('\n') + 1
            failures.append(f'{path}:{line}: forbidden ambient-real token {hit.group()!r}')
        graph[module] = imports(text)
        for target in graph[module]:
            if target in by_module:
                continue
            if target.split('.')[0] in CORE:
                local = root / (target.replace('.', '/') + '.lean')
                if local.exists():
                    failures.append(f'{path}: unaudited local shadow of {target}')
                external.add(target)
            else:
                failures.append(f'{path}: unaudited external or missing import {target}')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages = manifest.get('packages', [])
    for package in packages:
        if (package.get('name'), package.get('url'), package.get('rev')) != (
            'checkdecls', 'https://github.com/PatrickMassot/checkdecls.git',
            '3d425859e73fcfbef85b9638c2a91708ef4a22d4'):
            failures.append(f"unaudited dependency: {package.get('name')}")
    seen = set()
    queue = deque(['ComputableAnalysis'])
    while queue:
        module = queue.popleft()
        if module in seen:
            continue
        if module not in graph:
            failures.append(f'missing local entry point: {module}')
            continue
        seen.add(module)
        queue.extend(m for m in graph[module] if m in graph)
    print(f'Active Lean source files audited: {len(active)}')
    print(f'Local modules reachable from ComputableAnalysis: {len(seen)}')
    print('External module imports: ' + ', '.join(sorted(external)))
    print('Locked packages: ' + ', '.join(p['name'] for p in packages))
    print(f'Other tracked Lean files (not active roots): {len(other)}')
    for folder in sorted({p.split('/')[0] for p in other}):
        print('  outside active audit: ' + folder)
    if failures:
        print('\nFOUNDATION BOUNDARY FAILED', file=sys.stderr)
        for failure in failures:
            print(failure, file=sys.stderr)
        return 1
    print('PASS: active local import graph terminates only in Init/Lean/Std.')
    print('PASS: no Mathlib imports, ambient-real tokens, or new package dependencies.')
    print('Scope: source audit, not elaborated-environment or proof-dependency certification.')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(f'audit could not complete: {exc}', file=sys.stderr)
        sys.exit(2)
