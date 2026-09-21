#!/usr/bin/env python3
"""Fresh native compilation, regression builds, and the Taylor dependency audit."""
from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, subprocess, time
from pathlib import Path

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--build-dir', default='.lake/taylor-check')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    out = (root / args.build_dir).resolve()
    logs = out / 'logs'
    logs.mkdir(parents=True, exist_ok=True)
    lean = shutil.which(args.lean)
    if lean is None:
        raise SystemExit(f'Lean executable not found: {args.lean}')
    env = os.environ.copy()
    env['LEAN_PATH'] = str(out / 'lib')
    targets = ['ComputableAnalysis.TaylorReciprocal',
               'ComputableAnalysis.BetaViaFTC', 'ComputableAnalysis.WallisViaFTC']
    seen: set[str] = set()
    order: list[str] = []
    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        path = root / (module.replace('.', '/') + '.lean')
        if not path.is_file():
            if module.startswith(('Init.', 'Lean.')) or module in {'Init', 'Lean'}:
                return
            raise RuntimeError(f'Missing native source: {module}')
        text = path.read_text()
        if re.search(r'^import\s+(?:Mathlib|Std|Batteries)(?:\.|\s|$)', text, re.M):
            raise RuntimeError(f'Unexpected native import in {module}')
        for dep in re.findall(r'^import\s+([\w.]+)', text, re.M):
            visit(dep)
        order.append(module)
    for target in targets:
        visit(target)
    records = []
    for module in order:
        src = root / (module.replace('.', '/') + '.lean')
        obj = out / 'lib' / (module.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        started = time.monotonic()
        with (logs / (module + '.log')).open('w') as log:
            result = subprocess.run([lean, '-o', str(obj), str(src.relative_to(root))],
                                    cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT,
                                    timeout=600, check=False)
        records.append({'module': module, 'returncode': result.returncode,
                        'seconds': round(time.monotonic()-started, 3),
                        'sourceSha256': hashlib.sha256(src.read_bytes()).hexdigest()})
        (out / 'build.json').write_text(json.dumps(records, indent=2)+'\n')
        if result.returncode:
            raise SystemExit(f'Failed: {module}; see {logs / (module + ".log")}')
        print(f'PASS {module}', flush=True)
    with (logs / 'audit.log').open('w') as log:
        result = subprocess.run([lean, 'book/checks/CheckTaylorFTC.lean'], cwd=root,
                                env=env, stdout=log, stderr=subprocess.STDOUT,
                                timeout=180, check=False)
    if result.returncode:
        raise SystemExit(f'Audit failed; see {logs / "audit.log"}')
    audit = json.loads((root / 'reports/taylor-ftc-audit.json').read_text())
    assert all(audit[key] for key in ['nativeMathlibFree', 'noNativeNoncomputableDependencies',
               'noSorryAx', 'independentQuadratureAndValidity', 'exampleUsesTaylorAndExistingFTC'])
    print('PASS: fresh native build, beta/Wallis regressions, exact Taylor statements and dependency audit')

if __name__ == '__main__':
    main()
