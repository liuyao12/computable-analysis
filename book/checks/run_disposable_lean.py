#!/usr/bin/env python3
"""Check an exercise against unchanged infrastructure; keep no successful proof.

This runner is for trusted, generated acceptance exercises, not sandboxing
arbitrary Lean metaprograms. Persistent specification regressions live apart.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


def source_digest(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted((root / 'ComputableAnalysis').rglob('*.lean')):
        digest.update(str(path.relative_to(root)).encode())
        digest.update(b'\0')
        digest.update(path.read_bytes())
    return digest.hexdigest()



def audit_suffix(roots: list[str]) -> str:
    """Audit only named roots, not unrelated imports; print exact types/axioms."""
    names = ', '.join(json.dumps(name) for name in roots)
    return r'''
namespace DisposableAcceptanceAudit
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def refs (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants).getD #[]
private partial def closure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n::rest =>
    if seen.contains n then closure env rest seen else
      match env.find? n with
      | none => closure env rest (seen.insert n)
      | some ci => closure env ((refs ci).toList ++ rest) (seen.insert n)
run_cmd do
  let env ← getEnv
  let roots : Array String := #[ROOT_NAMES]
  for spelling in roots do
    let root := spelling.toName
    let some ci := env.find? root | throwError "Missing acceptance root: {root}"
    let axs ← collectAxioms root
    for ax in axs do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unapproved axiom in acceptance root: {root} -> {ax}"
    for name in closure env [root] do
      let owner := match env.getModuleIdxFor? name with
        | some i => env.header.moduleNames[i.toNat]!.toString
        | none => ""
      if owner.startsWith "Mathlib" then throwError "Mathlib dependency in native exercise: {root} -> {name}"
      if (owner.startsWith "ComputableAnalysis" || owner == "") && isNoncomputable env name then
        throwError "Noncomputable declaration in acceptance dependency: {root} -> {name}"
    let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 100
    logInfo m!"AUDITED {root}\n{ty}\nAXIOMS {axs}"
end DisposableAcceptanceAudit
'''.replace('ROOT_NAMES', names)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--root', action='append', required=True, help='Fully qualified theorem or computation to audit; repeat as needed.')
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--lean-path', default='.lake/build/lib/lean')
    parser.add_argument('--record', type=Path, default=Path('.lake/disposable-tests.jsonl'))
    parser.add_argument('--discard-input', action='store_true', help='Delete the input only after a successful check.')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    source = args.source.resolve(strict=True)
    # Never delete or accept an exercise as native library implementation.
    if source.is_relative_to(root / 'ComputableAnalysis'):
        raise SystemExit('Exercise input must be outside the native library.')
    lean = shutil.which(args.lean)
    if lean is None:
        raise SystemExit(f'Lean executable not found: {args.lean}')
    text = source.read_bytes()
    audited_text = 'import Lean\n' + text.decode('utf-8') + audit_suffix(args.root)
    before = source_digest(root)
    env = os.environ.copy()
    env['LEAN_PATH'] = str((root / args.lean_path).resolve())
    work = root / '.lake' / 'disposable'; work.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    with tempfile.TemporaryDirectory(dir=work) as name:
        temporary = Path(name) / 'Exercise.lean'; temporary.write_text(audited_text)
        try:
            result = subprocess.run([lean, str(temporary)], cwd=root, env=env,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, timeout=300, check=False)
            code, log = result.returncode, result.stdout
        except subprocess.TimeoutExpired as error:
            code, log = 124, f'Timeout after {error.timeout} seconds'
        after = source_digest(root)
        passed = code == 0 and before == after
        failed_source = None
        if not passed:
            failure_dir = root / '.lake' / 'disposable-failures'; failure_dir.mkdir(exist_ok=True)
            failed_source = failure_dir / (hashlib.sha256(text).hexdigest() + '.lean')
            failed_source.write_bytes(text)
        row = {
            'problem': source.name, 'audited_roots': args.root, 'input_sha256': hashlib.sha256(text).hexdigest(),
            'library_before': before, 'library_after': after, 'unchanged_library': before == after,
            'returncode': code, 'passed': passed, 'seconds': round(time.monotonic()-started, 3),
            'compiler': subprocess.check_output([lean, '--version'], text=True).strip(),
            'output': log, 'failed_source': str(failed_source) if failed_source else None,
            'temporary_copy_retained': False,
            'input_discarded': passed and args.discard_input,
        }
    record = (root / args.record).resolve(); record.parent.mkdir(parents=True, exist_ok=True)
    with record.open('a') as stream: stream.write(json.dumps(row) + '\n')
    print(log, end='')
    if passed and args.discard_input: source.unlink()
    print('PASS: unchanged library; temporary proof removed' if passed else 'FAIL: see record and retained failed probe')
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()
