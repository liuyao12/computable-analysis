#!/usr/bin/env python3
"""Recover the exact pinned reader when its short-lived Pages artifact expires.

Every output file is checked against the previously downloaded original
snapshot. A small repair archive restores files changed by later editions;
unchanged large assets come from a known successful deployment. Subsequent
runs reuse a durable copy, still checking every original file hash.
"""
import argparse,hashlib,io,json,os,subprocess,tarfile,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
DONOR_RUN='35815335502'

def files(path):
    with tarfile.open(path) as t:
        return {m.name.removeprefix('./'):t.extractfile(m).read()
                for m in t.getmembers() if m.isfile()}

def recover(donor, output):
    expected=json.loads((HERE/'reader-base-manifest.json').read_text())
    data=files(donor)
    data.update(files(HERE/'reader-base-repair.tar.gz'))
    assert set(expected)<=set(data)
    for name,digest in expected.items():
        assert '..' not in Path(name).parts and not Path(name).is_absolute()
        assert hashlib.sha256(data[name]).hexdigest()==digest,name
    output.parent.mkdir(parents=True,exist_ok=True)
    with tarfile.open(output,'w') as t:
        for name in sorted(expected):
            b=data[name];m=tarfile.TarInfo(name);m.size=len(b);m.mode=0o644;m.mtime=0
            t.addfile(m,io.BytesIO(b))
    print('PASS: recovered exact pinned reader;',len(expected),'file hashes verified')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--donor',type=Path)
    ap.add_argument('--output',type=Path,default=Path('downloaded/artifact.tar'))
    args=ap.parse_args()
    if args.donor:return recover(args.donor,args.output)
    repo=os.environ['GITHUB_REPOSITORY']
    artifacts=json.loads(subprocess.check_output(['gh','api',f'repos/{repo}/actions/artifacts?per_page=100']))['artifacts']
    saved=next((a for a in artifacts if a['name']=='verified-reader-base' and not a['expired']),None)
    run=str(saved['workflow_run']['id']) if saved else DONOR_RUN
    name='verified-reader-base' if saved else 'github-pages'
    with tempfile.TemporaryDirectory() as d:
        subprocess.run(['gh','run','download',run,'--repo',repo,'--name',name,'--dir',d],check=True)
        recover(Path(d)/'artifact.tar',args.output)

if __name__=='__main__': main()
