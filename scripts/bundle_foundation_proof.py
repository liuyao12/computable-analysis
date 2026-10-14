"""Reproducible source snapshot for the concrete opening-chapter proofs."""
from pathlib import Path
import gzip, hashlib, io, json, re, tarfile
root=Path(__file__).resolve().parents[1]
out=root/'book/foundation-story'
modules=set(); todo=['ComputableAnalysis.EnclosureHolomorphicExamples','ComputableAnalysis.EnclosureHolomorphicCounterexample','ComputableAnalysis.ParametrizedFoundationExamples','ComputableAnalysis.BracketDerivativeExamples','ComputableAnalysis.SqrtSecantFoundation','ComputableAnalysis.SquareRootSecantNewton','ComputableAnalysis.ArctanInverseCircle']
while todo:
    name=todo.pop()
    if name in modules: continue
    modules.add(name)
    source=root/(name.replace('.','/')+'.lean')
    todo.extend(re.findall(r'^import\s+(ComputableAnalysis(?:\.[A-Za-z0-9_]+)+)',source.read_text(),re.M))
files={n.replace('.','/')+'.lean':(root/(n.replace('.','/')+'.lean')).read_bytes() for n in modules}
for name in ['lean-toolchain','lake-manifest.json','scripts/check_opening_foundation.lean','scripts/check_bracket_derivative.lean','scripts/check_parametrized_foundation.lean','scripts/check_enclosure_holomorphic.lean','docs/HOLOMORPHIC_ENCLOSURES.md','docs/PARAMETRIZED_FOUNDATION.md','scripts/export_foundation_dependencies.lean','skills/intermediate-value-construction/SKILL.md']:
    files[name]=(root/name).read_bytes()
files['lakefile.toml']=b'name = "OpeningFoundation"\nversion = "0.1.0"\ndefaultTargets = ["ComputableAnalysis"]\n\n[[lean_lib]]\nname = "ComputableAnalysis"\nroots = ["ComputableAnalysis"]\n\n[[require]]\nname = "checkdecls"\ngit = "https://github.com/PatrickMassot/checkdecls.git"\n'
files['ComputableAnalysis.lean']=b'import ComputableAnalysis.EnclosureHolomorphicExamples\nimport ComputableAnalysis.EnclosureHolomorphicCounterexample\nimport ComputableAnalysis.ParametrizedFoundationExamples\nimport ComputableAnalysis.BracketDerivativeExamples\nimport ComputableAnalysis.SqrtSecantFoundation\nimport ComputableAnalysis.SquareRootSecantNewton\nimport ComputableAnalysis.ArctanInverseCircle\n'
raw=io.BytesIO()
with tarfile.open(fileobj=raw,mode='w') as tar:
    for name,data in sorted(files.items()):
        entry=tarfile.TarInfo(name);entry.size=len(data);entry.mtime=0;entry.mode=0o644
        tar.addfile(entry,io.BytesIO(data))
compressed=gzip.compress(raw.getvalue(),mtime=0)
(out/'proof.tar.gz').write_bytes(compressed)
meta={'sha256':hashlib.sha256(compressed).hexdigest(),'bytes':len(compressed),'projectModules':len(modules),'files':{name:hashlib.sha256(data).hexdigest() for name,data in sorted(files.items())},'auditCommand':'lake env lean scripts/check_opening_foundation.lean', 'bracketAuditCommand':'lake env lean scripts/check_bracket_derivative.lean', 'parametrizedAuditCommand':'lake env lean scripts/check_parametrized_foundation.lean','holomorphicAuditCommand':'lake env lean scripts/check_enclosure_holomorphic.lean','buildCommand':'lake build','scope':'Covered complex first-order error enclosures, holomorphicity by shrinking computed complex secant boxes with derived derivative continuity and exact equivalence to the previous definition, exact equivalence with quantitative holomorphy, proved Cauchy recovery and Taylor reconstruction with all higher derivatives, separate weaker pointwise calculus, actual elementary and special-function examples, conjugation rejection; covered cofinal valid diagonals, continuity, rational-endpoint bracket derivatives, exact compatibility and invariance, interval and finite derivative bridges, complex coordinate and normalized remainder adapters; original secant, convex, square-root FTC and inverse-arctangent circle computations retained.'}
(out/'proof.json').write_text(json.dumps(meta,indent=2)+'\n')
sources=out/'sources';sources.mkdir(exist_ok=True)
for p in sources.glob('*.lean'):p.unlink()
for n in modules:(sources/(n+'.lean')).write_bytes(files[n.replace('.','/')+'.lean'])
print('Bundled',len(modules),'project modules;',len(compressed),'bytes')
