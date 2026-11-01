#!/usr/bin/env python3
"""Recover and verify the existing Pages site before adding the textbook."""
import concurrent.futures, hashlib, json, pathlib, tarfile, time, urllib.request, urllib.parse
ROOT=pathlib.Path(__file__).resolve().parents[1]
SITE=ROOT/'_site'
BASE=ROOT/'book/modular-dependencies/pages-base.tar.gz'
EXPECTED='5fc6fcae73b770c58d85796620b3b862c9050b2b11192064ab39313a6c6fe404'
assert hashlib.sha256(BASE.read_bytes()).hexdigest()==EXPECTED, 'Unexpected preservation archive'
SITE.mkdir(exist_ok=True)
with tarfile.open(BASE) as archive:
    for m in archive.getmembers():
        assert not m.issym() and not m.islnk(), 'Archive link refused'
        target=(SITE/m.name).resolve()
        assert target.is_relative_to(SITE.resolve()), 'Unsafe archive path'
    archive.extractall(SITE, filter='data')
manifest=json.loads((ROOT/'book-preservation.json').read_text())
def recover(item):
    path,digest=item
    dest=SITE/path
    assert dest.resolve().is_relative_to(SITE.resolve())
    if dest.is_file() and hashlib.sha256(dest.read_bytes()).hexdigest()==digest:return
    for attempt in range(5):
        try:
            with urllib.request.urlopen(manifest['base']+urllib.parse.quote(path),timeout=90) as response:data=response.read()
            assert hashlib.sha256(data).hexdigest()==digest, 'Live content changed: '+path
            dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);return
        except Exception:
            if attempt==4:raise
            time.sleep(attempt+1)
with concurrent.futures.ThreadPoolExecutor(max_workers=16) as pool:list(pool.map(recover,manifest['files'].items()))
print('Preserved',len(manifest['files']),'verified live files plus the complete earlier backup.')
