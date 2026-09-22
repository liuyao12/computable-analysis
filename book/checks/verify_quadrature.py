#!/usr/bin/env python3
"""Compile quadrature infrastructure and audit it without importing Mathlib.

Default build directory must be absent: no cached .olean files are trusted.
Optional legacy application/Taylor regressions are explicit CLI choices.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--build-dir', default='.lake/quadrature-fresh')
    parser.add_argument('--with-applications', action='store_true')
    parser.add_argument('--with-taylor', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    lean = shutil.which(args.lean)
    if lean is None:
        raise SystemExit(f'Lean not found: {args.lean}')
    out = (root / args.build_dir).resolve()
    if out.exists():
        raise SystemExit(f'Fresh build requires an absent directory: {out}')
    logs = out / 'logs'; logs.mkdir(parents=True)
    env = os.environ.copy(); env['LEAN_PATH'] = str(out / 'lib')
    targets = ['ComputableAnalysis.QuadratureAdapters']
    if args.with_applications:
        targets += ['ComputableAnalysis.IntegralApplications',
                    'ComputableAnalysis.CosineIntegralViaFTC', 'ComputableAnalysis.Cartwright']
    if args.with_taylor:
        targets += ['ComputableAnalysis.TaylorReciprocal']
    seen: set[str] = set()
    order: list[str] = []
    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        src = root / (module.replace('.', '/') + '.lean')
        if not src.exists():
            if module in {'Init', 'Lean'} or module.startswith(('Init.', 'Lean.')):
                return
            raise RuntimeError(f'Missing requested dependency: {module}')
        text = src.read_text()
        for dep in re.findall(r'^import\s+([\w.]+)', text, re.M):
            if dep.split('.')[0] in {'Mathlib', 'Std', 'Batteries'}:
                raise RuntimeError(f'Forbidden native import {dep} in {module}')
            visit(dep)
        order.append(module)
    for target in targets:
        visit(target)
    report = {'compiler': subprocess.check_output([lean, '--version'], text=True).strip(),
              'targets': targets, 'builds': [], 'checks': [], 'passed': False}
    def save() -> None:
        (out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    save()
    for module in order:
        src = root / (module.replace('.', '/') + '.lean')
        obj = out / 'lib' / (module.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        with (logs / (module + '.log')).open('w') as log:
            result = subprocess.run([lean, '-o', str(obj), str(src.relative_to(root))],
                                    cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT,
                                    timeout=600, check=False)
        report['builds'].append({'module': module, 'returncode': result.returncode,
            'sha256': hashlib.sha256(src.read_bytes()).hexdigest(),
            'seconds': round(time.monotonic() - start, 3)})
        save()
        if result.returncode:
            raise SystemExit(f'FAIL {module}; see {logs}')
        print(f'PASS {module}', flush=True)
    for check in ['CheckQuadratureMeaning', 'AuditQuadrature']:
        with (logs / (check + '.log')).open('w') as log:
            result = subprocess.run([lean, f'book/checks/{check}.lean'], cwd=root, env=env,
                                    stdout=log, stderr=subprocess.STDOUT, timeout=180, check=False)
        report['checks'].append({'name': check, 'returncode': result.returncode})
        save()
        if result.returncode:
            raise SystemExit(f'FAIL {check}; see {logs}')
    shutil.copy2(root / '.lake/cleanup/quadrature-audit.json', out / 'quadrature-audit.json')
    report['passed'] = True; save()
    print('PASS: fresh sources, quadrature regressions and stored-reference audit')

if __name__ == '__main__':
    main()
