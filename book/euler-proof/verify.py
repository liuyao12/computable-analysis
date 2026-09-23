#!/usr/bin/env python3
"""Build the isolated Mathlib companion and audit the elaborated Euler proof."""
import argparse, hashlib, json, shutil, subprocess, tarfile, urllib.request
from pathlib import Path
REVISION = '51e6992efd06126df61a496bebf8f49482a4e129'
ARCHIVE_SHA256 = '0d44640e4a47b76187c0d6d31800a2e8c05001629c75010cff4c21031f5fa8b3'
SOURCE = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    work, report = args.work_dir.resolve(), args.report.resolve()
    if not (work / 'lakefile.lean').exists():
        work.mkdir(parents=True, exist_ok=True)
        archive = work / 'mathlib.tar.gz'
        urllib.request.urlretrieve(f'https://codeload.github.com/leanprover-community/mathlib4/tar.gz/{REVISION}', archive)
        assert hashlib.sha256(archive.read_bytes()).hexdigest() == ARCHIVE_SHA256
        with tarfile.open(archive) as tar:
            prefix = f'mathlib4-{REVISION}/'
            for member in tar.getmembers():
                if not member.name.startswith(prefix) or member.name == prefix: continue
                member.name = member.name[len(prefix):]
                if member.issym() or member.islnk() or '..' in Path(member.name).parts:
                    raise ValueError('Unexpected archive member')
                tar.extract(member, work)
        archive.unlink()
        (work / '.euler-mathlib-revision').write_text(REVISION)
    assert (work / '.euler-mathlib-revision').read_text() == REVISION
    assert (work / 'lean-toolchain').read_bytes() == (SOURCE / 'lean-toolchain').read_bytes()
    for name in ['EulerBasel.lean', 'CheckEuler.lean']:
        shutil.copyfile(SOURCE / name, work / name)
    imports = [line.removeprefix('import ') for line in (SOURCE / 'EulerBasel.lean').read_text().splitlines() if line.startswith('import ')]
    # A missing remote cache object is recoverable: lake builds it below.
    subprocess.run(['lake', 'exe', 'cache', 'get', *[name.replace('.', '/') + '.lean' for name in imports]], cwd=work, check=False)
    subprocess.run(['lake', 'build', *imports], cwd=work, check=True)
    subprocess.run(['lake', 'env', 'lean', '-o', '.lake/build/lib/lean/EulerBasel.olean', 'EulerBasel.lean'], cwd=work, check=True)
    subprocess.run(['lake', 'env', 'lean', 'CheckEuler.lean'], cwd=work, check=True)
    report.mkdir(parents=True, exist_ok=True)
    for name in ['proofs.json', 'dependencies.txt']:
        shutil.copyfile(work / 'euler-reports' / name, report / name)
    audit = json.loads((report / 'proofs.json').read_text())
    audit['sourceHashes'] = {name: hashlib.sha256((SOURCE / name).read_bytes()).hexdigest() for name in ['EulerBasel.lean', 'CheckEuler.lean', 'lean-toolchain', 'verify.py']}
    audit['mathlibArchiveSha256'] = ARCHIVE_SHA256
    (report / 'proofs.json').write_text(json.dumps(audit, indent=2) + '\n')

if __name__ == '__main__': main()
