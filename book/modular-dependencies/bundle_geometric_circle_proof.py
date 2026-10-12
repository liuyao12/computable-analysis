"""Package exactly the local import closure of the geometric comparison."""
from pathlib import Path
import gzip, hashlib, io, json, re, tarfile
root = Path(__file__).resolve().parents[1]
out = root / 'book/modular-dependencies'
modules = set()
todo = ['ComputableAnalysis.GeometricCircleODEComparison']
while todo:
    name = todo.pop()
    if name in modules:
        continue
    modules.add(name)
    source = root / (name.replace('.', '/') + '.lean')
    todo.extend(re.findall(r'^import\s+(ComputableAnalysis(?:\.[A-Za-z0-9_]+)+)', source.read_text(), re.M))
files = {name.replace('.', '/') + '.lean': (root / (name.replace('.', '/') + '.lean')).read_bytes() for name in modules}
files['lean-toolchain'] = (root / 'lean-toolchain').read_bytes()
files['GeometricCircleProof.lean'] = b'import ComputableAnalysis.GeometricCircleODEComparison\n'
files['lakefile.toml'] = b'name = "GeometricCircleProof"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "GeometricCircleProof"\nroots = ["GeometricCircleProof"]\n'
files['scripts/check_geometric_circle_ode_comparison.lean'] = (root / 'scripts/check_geometric_circle_ode_comparison.lean').read_bytes()
files['README.md'] = b'# Checked geometric circle and power-series sine comparison\n\nThis bundle includes exactly the project import closure of the comparison, its audit, and a minimal Lake target.\n\nRun `lake build`, then `lake env lean scripts/check_geometric_circle_ode_comparison.lean`.\n\nThe primary geometric circle takes rational stereographic slopes. The exact theorem is `ComputableAnalysis.GeometricCircleODEComparison.geometric_sine_powerSeries`. Its irrational-angle evaluation is derived from the primary rational-complex power series.\n'
data = io.BytesIO()
with gzip.GzipFile(fileobj=data, mode='wb', mtime=0) as gz:
    with tarfile.open(fileobj=gz, mode='w') as archive:
        for name, body in sorted(files.items()):
            info = tarfile.TarInfo(name)
            info.size = len(body)
            info.mode = 0o644
            archive.addfile(info, io.BytesIO(body))
path = out / 'geometric-circle-proof.tar.gz'
path.write_bytes(data.getvalue())
metadata = dict(path=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest(), bytes=path.stat().st_size, projectModules=len(modules))
(out / 'geometric-circle-proof.json').write_text(json.dumps(metadata) + '\n')
print(metadata)
