"""Reproducible source snapshot for the concrete opening-chapter proofs."""
from pathlib import Path
import gzip, hashlib, io, json, re, tarfile
root=Path(__file__).resolve().parents[1]
out=root/'book/foundation-story'
modules=set(); todo=['ComputableAnalysis.BracketDerivativeExamples','ComputableAnalysis.SqrtSecantFoundation','ComputableAnalysis.SquareRootSecantNewton','ComputableAnalysis.ArctanInverseCircle']
while todo:
    name=todo.pop()
    if name in modules: continue
    modules.add(name)
    source=root/(name.replace('.','/')+'.lean')
    todo.extend(re.findall(r'^import\s+(ComputableAnalysis(?:\.[A-Za-z0-9_]+)+)',source.read_text(),re.M))
files={n.replace('.','/')+'.lean':(root/(n.replace('.','/')+'.lean')).read_bytes() for n in modules}
for name in ['lean-toolchain','lake-manifest.json','scripts/check_opening_foundation.lean','scripts/check_bracket_derivative.lean','scripts/export_foundation_dependencies.lean','skills/intermediate-value-construction/SKILL.md']:
    files[name]=(root/name).read_bytes()
files['lakefile.toml']=b'name = "OpeningFoundation"\nversion = "0.1.0"\ndefaultTargets = ["ComputableAnalysis"]\n\n[[lean_lib]]\nname = "ComputableAnalysis"\nroots = ["ComputableAnalysis"]\n\n[[require]]\nname = "checkdecls"\ngit = "https://github.com/PatrickMassot/checkdecls.git"\n'
files['ComputableAnalysis.lean']=b'import ComputableAnalysis.BracketDerivativeExamples\nimport ComputableAnalysis.SqrtSecantFoundation\nimport ComputableAnalysis.SquareRootSecantNewton\nimport ComputableAnalysis.ArctanInverseCircle\n'
raw=io.BytesIO()
with tarfile.open(fileobj=raw,mode='w') as tar:
    for name,data in sorted(files.items()):
        entry=tarfile.TarInfo(name);entry.size=len(data);entry.mtime=0;entry.mode=0o644
        tar.addfile(entry,io.BytesIO(data))
compressed=gzip.compress(raw.getvalue(),mtime=0)
(out/'proof.tar.gz').write_bytes(compressed)
meta={'sha256':hashlib.sha256(compressed).hexdigest(),'bytes':len(compressed),'projectModules':len(modules),'files':{name:hashlib.sha256(data).hexdigest() for name,data in sorted(files.items())},'auditCommand':'lake env lean scripts/check_opening_foundation.lean', 'bracketAuditCommand':'lake env lean scripts/check_bracket_derivative.lean','buildCommand':'lake build','scope':'Two-index represented limits and rational-endpoint bracket derivatives, uniqueness and representation invariance, generic outer-secant law, old centered convex instances, and concrete square-root rational-line inversion, secant derivatives and FTC, and first-quadrant inverse-arctangent circle computations; existing imported results are retained.'}
(out/'proof.json').write_text(json.dumps(meta,indent=2)+'\n')
sources=out/'sources';sources.mkdir(exist_ok=True)
for p in sources.glob('*.lean'):p.unlink()
for n in modules:(sources/(n+'.lean')).write_bytes(files[n.replace('.','/')+'.lean'])
print('Bundled',len(modules),'project modules;',len(compressed),'bytes')
