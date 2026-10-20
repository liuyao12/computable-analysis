#!/usr/bin/env python3
"""Inventory identification-law review sources; this is not a proof checker."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

SUFFIXES = {'.lean', '.md', '.tex', '.html'}
DECLARATION = re.compile(
    r'^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|structure)\s+([^\s(:{]+)',
    re.M)


def scope(path):
    if path.startswith('ComputableAnalysis/') or path == 'ComputableAnalysis.lean':
        return 'main-library'
    if path.startswith('book/') and path.endswith('.lean'):
        return 'companion-or-published-source-copy'
    if path.startswith('scripts/') and path.endswith('.lean'):
        return 'checker-or-entry-point'
    if path.endswith('.lean'):
        return 'other-lean-source'
    return 'exposition-or-guidance'


def inventory(root, revision):
    rows = []
    for path in sorted(root.rglob('*')):
        rel = path.relative_to(root)
        if any(p in {'.git', '.lake', 'node_modules'} for p in rel.parts):
            continue
        if not path.is_file() or path.suffix not in SUFFIXES:
            continue
        # Reports describe their inputs rather than inventorying themselves.
        if rel.as_posix() == 'docs/IDENTIFICATION_AUDIT.md':
            continue
        data = path.read_bytes()
        text = data.decode('utf-8')
        names = DECLARATION.findall(text) if path.suffix == '.lean' else []
        hints = {
            'validity': [n for n in names if re.search(r'valid|nested|widthsShrink', n, re.I)],
            'identity-or-comparison': [n for n in names if re.search(
                r'equiv|hasDerivative|hasIntegral|forward.*target|mul_self', n, re.I)],
            'uniqueness': [n for n in names if re.search(r'unique|injective', n, re.I)],
        }
        rows.append({
            'path': rel.as_posix(), 'sha256': hashlib.sha256(data).hexdigest(),
            'bytes': len(data), 'scope': scope(rel.as_posix()),
            'review': 'indexed-only',
            'declarationHints': {k: v[:12] for k, v in hints.items() if v},
        })
    return {
        'revision': revision,
        'scope': 'All Lean, Markdown, TeX, and HTML files in the supplied snapshot, excluding build caches and this audit report.',
        'meaning': 'Hashes and declaration hints establish coverage only. Human contract findings are in IDENTIFICATION_AUDIT.md; no kernel check is claimed.',
        'counts': dict(sorted(Counter(r['scope'] for r in rows).items())),
        'uniqueContents': len({r['sha256'] for r in rows}),
        'files': rows,
    }


def check_euler_candidate():
    def stage(n):
        m = (n + 1) ** 2
        center = (1 + Fraction(2, m)) ** m
        radius = Fraction(1) if n == 0 else Fraction(1, 2 * n)
        return center - radius, center + radius
    assert stage(0) == (Fraction(2), Fraction(4))
    assert stage(1) == (Fraction(73, 16), Fraction(89, 16))
    assert stage(0)[1] < stage(1)[0]
    return {'input': '2', 'stage0': ['2', '4'],
            'stage1': ['73/16', '89/16'], 'finding': 'disjoint; nesting fails',
            'verification': 'exact Python Fraction arithmetic, not a new Lean kernel check'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path,
                        help='Explicit readable source snapshot, not an implicit working-tree claim')
    parser.add_argument('--revision', required=True)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = inventory(args.root.resolve(), args.revision)
    result['exactCounterexample'] = check_euler_candidate()
    rendered = json.dumps(result, indent=2) + '\n'
    if args.check:
        assert args.output.read_text() == rendered, 'Source snapshot changed; review and refresh the inventory.'
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print('PASS: indexed', len(result['files']), 'source files;', result['uniqueContents'], 'unique contents')
    print('Coverage only; mathematical identification requires contract and proof review.')
    print('PASS: exact rational counterexample to arbitrary-input expEuler nesting.')


if __name__ == '__main__':
    main()
