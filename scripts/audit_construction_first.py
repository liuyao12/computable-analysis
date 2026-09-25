#!/usr/bin/env python3
"""Check source coverage of the contract review, not mathematical correctness."""
import hashlib
import json
from collections import Counter
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def audit():
    inventory = json.loads((ROOT / 'docs/CONSTRUCTION_FIRST_INVENTORY.json').read_text())
    rows = inventory['files']
    paths = [row['path'] for row in rows]
    tracked = subprocess.check_output(
        ['git', 'ls-files', '*.lean'], cwd=ROOT, text=True).splitlines()
    assert len(paths) == len(set(paths)), 'Duplicate source entry'
    assert set(paths) == set(tracked), {
        'missing': sorted(set(tracked) - set(paths)),
        'stale': sorted(set(paths) - set(tracked)),
    }
    for row in rows:
        path = ROOT / row['path']
        assert row['area'] and row['area'] != 'UNCLASSIFIED', row['path']
        assert hashlib.sha256(path.read_bytes()).hexdigest() == row['sha256'], (
            'Source changed since the contract review; review and update its entry', row['path'])
    counts = Counter(row['scope'] for row in rows)
    print('Construction-first review source coverage:', dict(counts))
    print('Coverage only; semantic findings are in docs/CONSTRUCTION_FIRST_AUDIT.md')
    return counts


if __name__ == '__main__':
    audit()
