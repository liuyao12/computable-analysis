#!/usr/bin/env python3
"""Package the checked CM endpoint and its complete native source closure."""
import argparse,hashlib,json,re,tarfile,io
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser()
p.add_argument('--audit',required=True);p.add_argument('--build',required=True)
a=p.parse_args()
audit=Path(a.audit).read_bytes();build=Path(a.build).read_bytes()
assert b'error:' not in audit and b'sorryAx' not in audit
assert b'Build completed successfully' in build and b'error:' not in build
pending=['ComputableAnalysis.ModularForms.NearIntegerExponentials']
seen=set();files={}
while pending:
    name=pending.pop()
    if name in seen:continue
    seen.add(name);path=Path(*name.split('.')).with_suffix('.lean')
    code=(ROOT/path).read_bytes();files[str(path)]=code
    for line in code.decode().splitlines():
        if line.startswith('import '):
            for dep in line.split('--')[0].split()[1:]:
                if dep.startswith('ComputableAnalysis.'):pending.append(dep)
                else:assert dep in ['Init','Lean'] or dep.startswith(('Init.','Lean.')),dep
files.update({
    'ComputableAnalysis.lean':b'import ComputableAnalysis.ModularForms.NearIntegerExponentials\n',
    'scripts/check_cm_elliptic_values.lean':(ROOT/'scripts/check_cm_elliptic_values.lean').read_bytes(),
    'scripts/build_cm_values_proof_bundle.py':Path(__file__).read_bytes(),
    'lean-toolchain':(ROOT/'lean-toolchain').read_bytes(),
    'lakefile.toml':b'name = "cm_values_proof"\nversion = "0.1.0"\ndefaultTargets = ["ComputableAnalysis"]\n\n[[lean_lib]]\nname = "ComputableAnalysis"\n',
    'axiom-audit.txt':audit,'scoped-build.txt':build,
    'README.txt':b"""Complete checked source closure for the actual modular j values at
discriminants -4, -43 and -163, and unconditional near-integer exponential showpieces
at both irrational arguments through the current exponential API. The general class-polynomial theorem
is not included. Only Lean and Init external imports are needed.

Replay with the pinned Lean toolchain:
  lake build ComputableAnalysis.ModularForms.NearIntegerExponentials
  lake env lean scripts/check_cm_elliptic_values.lean

All concrete point, denominator, modular relation and isolation evidence
is constructed in the source. Finite data are checked by the Lean kernel.
The public theorem audit excludes sorryAx and native evaluation axioms.
The manifest records SHA-256 hashes for every packaged file except itself.
This scoped source archive does not claim that the larger repository root
build or unrelated auxiliary audits pass.
"""
})
files['manifest.json']=(json.dumps({n:hashlib.sha256(c).hexdigest() for n,c in sorted(files.items())},indent=2)+'\n').encode()
dest=ROOT/'book/modular-dependencies/cm-values-proof.tar.gz'
dest.parent.mkdir(parents=True,exist_ok=True)
with tarfile.open(dest,'w:gz',compresslevel=9) as t:
    for n,c in sorted(files.items()):
        info=tarfile.TarInfo('cm-values-proof/'+n);info.size=len(c);info.mtime=0;info.mode=0o644
        t.addfile(info,io.BytesIO(c))
meta=dict(path='modular-cm-values-proof.tar.gz',sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),sourceModules=len(seen),bytes=dest.stat().st_size,toolchain=(ROOT/'lean-toolchain').read_text().strip())
dest.with_name('cm-values-proof.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta))
