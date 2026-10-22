#!/usr/bin/env python3
"""Rebuild the recorded source closure and check the signed-area endpoints."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lean', default=shutil.which('lean'))
args = parser.parse_args()
report = json.loads((root/'verification/report.json').read_text())
for rel, expected in report['sourceSha256'].items():
    assert hashlib.sha256((root/rel).read_bytes()).hexdigest() == expected, rel
with tempfile.TemporaryDirectory(prefix='rational-signed-area-') as temporary:
    build = Path(temporary)
    env = dict(os.environ, LEAN_PATH=str(build))
    for name in report['compileOrder']:
        rel = name.replace('.', '/')
        output = build/(rel+'.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([args.lean, '-o', str(output), rel+'.lean'],
                       cwd=root, env=env, check=True)
        print('PASS', name, flush=True)
    checked = subprocess.check_output(
        [args.lean, 'scripts/check_rational_triangle_area_transform.lean'],
        cwd=root, env=env, text=True)
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", checked, re.S)
    assert {n for n,_ in matches} == set(report['auditedTheorems'])
    for name, axioms in matches:
        assert {a.strip() for a in axioms.split(',')} <= {
            'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    print(checked)
print('PASS: signed-area determinant law and seven theorem-axiom audits.')
