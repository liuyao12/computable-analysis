#!/usr/bin/env python3
"""Check native integration inventory coverage and reject weak integral APIs.
This is a source/schema audit; Lean separately checks the mathematical proofs.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INDEX = ROOT / 'docs/INTEGRAL_INVENTORY.json'
WORDS = re.compile(r'integral|darboux|riemann|quadrature', re.I)
DECL = re.compile(r'(?:private |noncomputable |protected )*(?:def|abbrev|structure|theorem)\s+([^\s(:{]+)')
FORBIDDEN = re.compile(r'^(?:structure (?:ConstructionFor|SegmentIntegralRaw)|def (?:integralFor|polygonalPolynomialIntegralRaw))\b', re.M)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--update-lines', action='store_true')
    args = ap.parse_args()
    inventory = json.loads(INDEX.read_text())
    indexed = {row['path']: row for row in inventory['files']}
    assert len(indexed) == len(inventory['files'])
    roles = {'enclosure', 'comparison', 'mixed', 'conditional', 'finite', 'support'}
    count = 0
    for path in sorted((ROOT / 'ComputableAnalysis').rglob('*.lean')):
        rel = str(path.relative_to(ROOT)); source = path.read_text()
        assert not FORBIDDEN.search(source), rel
        if not WORDS.search(source) and rel not in indexed:
            continue
        assert rel in indexed, f'Unreviewed integration-related module: {rel}'
        row = indexed[rel]
        assert row['role'] in roles, rel
        decls = [{'line': n, 'declaration': m.group(1)}
                 for n, line in enumerate(source.splitlines(), 1)
                 if (m := DECL.match(line)) and WORDS.search(m.group(1))]
        if args.update_lines:
            row['declarations'] = decls
        else:
            assert row['declarations'] == decls, f'Stale declaration index: {rel}'
        count += 1
    assert count == len(indexed), 'Inventory refers to missing source'
    auxiliary = {row['path']: row for row in inventory['auxiliaryFiles']}
    assert len(auxiliary) == len(inventory['auxiliaryFiles'])
    tracked = subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=ROOT, text=True).splitlines()
    expected = {name for name in tracked if not name.startswith('ComputableAnalysis/')
                and WORDS.search((ROOT / name).read_text())}
    assert set(auxiliary) == expected, f'Unreviewed or stale auxiliary sources: {set(auxiliary) ^ expected}'
    for row in auxiliary.values():
        assert row['role'] in {'historical-copy', 'pinned-proof', 'audit-helper', 'library-entry'}

    core = (ROOT / 'ComputableAnalysis/ComplexPathIntegral.lean').read_text()
    assert 'sound : f.Sound' in core
    assert 'polygonalIntegralBoxEntire f vertices (2 ^ n)' in core
    assert 'compute := fun n => polygonalIntegralBoxEntire f vertices n' not in core
    if args.update_lines:
        INDEX.write_text(json.dumps(inventory, indent=2) + '\n')
    print(f'PASS: {count} native and {len(auxiliary)} auxiliary modules classified; no obsolete weak native integral APIs')


if __name__ == '__main__':
    main()
