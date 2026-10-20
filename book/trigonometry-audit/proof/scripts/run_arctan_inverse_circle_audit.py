#!/usr/bin/env python3
"""Cold-build the actual inverse-circle proof closure and check its axioms."""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

TARGET = 'ComputableAnalysis.ArctanInverseCircleAudit'
CHECK = 'scripts/check_arctan_inverse_circle_audit.lean'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--lean', default=shutil.which('lean'))
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    root, build = args.source_root.resolve(), args.build_dir.resolve()
    build.mkdir(parents=True, exist_ok=True)
    dependencies, hashes = {}, {}

    def visit(name):
        if name in dependencies or not name.startswith('ComputableAnalysis.'):
            return
        path = root / (name.replace('.', '/') + '.lean')
        data = path.read_bytes()
        hashes[str(path.relative_to(root))] = hashlib.sha256(data).hexdigest()
        imports = re.findall(r'^import\s+([\w.]+)', data.decode(), re.M)
        assert all(i.startswith(('ComputableAnalysis.', 'Init')) for i in imports), (name, imports)
        dependencies[name] = {i for i in imports if i.startswith('ComputableAnalysis.')}
        for dep in dependencies[name]:
            visit(dep)

    visit(TARGET)
    env = dict(os.environ, LEAN_PATH=str(build))
    version = subprocess.check_output([args.lean, '--version'], text=True).strip()
    completed, pending, running, timings = set(), set(dependencies), {}, {}

    def compile_module(name):
        rel = name.replace('.', '/')
        output = build / (rel + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        result = subprocess.run([args.lean, '-o', str(output), rel + '.lean'],
                                cwd=root, env=env, text=True, capture_output=True)
        log = build / (rel + '.log')
        log.write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(f'{name} failed; see {log}\n' + result.stdout + result.stderr)
        return round(time.monotonic() - start, 3)

    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        while pending or running:
            ready = sorted(n for n in pending if dependencies[n] <= completed)
            while ready and len(running) < args.jobs:
                name = ready.pop(0)
                pending.remove(name)
                running[executor.submit(compile_module, name)] = name
            if not running:
                raise RuntimeError('Import cycle or unresolved source dependency')
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                timings[name] = future.result()
                completed.add(name)
                print(f'PASS {name} ({timings[name]}s)', flush=True)
    check = root / CHECK
    hashes[CHECK] = hashlib.sha256(check.read_bytes()).hexdigest()
    result = subprocess.run([args.lean, CHECK], cwd=root, env=env,
                            text=True, capture_output=True)
    text = result.stdout + result.stderr
    (build / 'check.log').write_text(text)
    assert result.returncode == 0, text
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    assert len(matches) == 7, ('Expected seven explicit endpoint axiom audits', matches)
    for name, axioms in matches:
        assert {a.strip() for a in axioms.split(',')} <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    report = {'leanVersion': version, 'coldBuild': True, 'modulesBuilt': len(completed),
              'sourceSha256': hashes, 'buildSeconds': timings,
              'auditedTheorems': [n for n, _ in matches],
              'allowedAxioms': ['propext', 'Classical.choice', 'Quot.sound'],
              'noMathlibImportsInClosure': True}
    (build / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: cold source build, exact chart checks, endpoint/clock normalization, and seven standard-axiom audits.', flush=True)


if __name__ == '__main__':
    main()
