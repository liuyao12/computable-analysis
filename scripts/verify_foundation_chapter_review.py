#!/usr/bin/env python3
"""Check the chapter edits against the exact previous deployment."""

import hashlib
import json
import re
import sys
import tarfile
from pathlib import Path


root = Path(__file__).resolve().parents[1]
site = Path(sys.argv[1])
archive_path = Path(sys.argv[2])
reviews = {
    item['page']: item['foundationReview']
    for item in json.loads((root / 'book/pedagogy/pages.json').read_text())
    if 'foundationReview' in item
}
pattern = rb'\n?<section id="current-foundation" class="pedagogical-opening">\n.*?</section>\n'
home_link = b'<p id="foundation-textbook-link"><a href="foundation-textbook/">Read the living foundation textbook</a></p>\n'
seen = set()

with tarfile.open(archive_path) as archive:
    for member in archive:
        if not member.isfile():
            continue
        path = Path(member.name).as_posix()
        seen.add(path)
        if path.startswith('foundation-textbook/'):
            continue
        before = archive.extractfile(member).read()
        after = (site / path).read_bytes()
        if path in reviews:
            assert after.count(b'id="current-foundation"') == 1, path
            for filename in reviews[path]['links'].values():
                assert (site / 'foundation-textbook' / filename).is_file(), filename
                assert f'href="foundation-textbook/{filename}"'.encode() in after, path
            before = re.sub(pattern, b'', before, count=1, flags=re.S)
            after = re.sub(pattern, b'', after, count=1, flags=re.S)
        if path == 'index.html':
            assert home_link in after
            before = before.replace(home_link, b'', 1)
            after = after.replace(home_link, b'', 1)
        assert hashlib.sha256(after).digest() == hashlib.sha256(before).digest(), path

assert set(reviews).issubset(seen)
assert {
    p.relative_to(site).as_posix()
    for p in site.rglob('*')
    if p.is_file() and p.relative_to(site).parts[0] != 'foundation-textbook'
} == {path for path in seen if not path.startswith('foundation-textbook/')}
print(f'Verified {len(reviews)} chapter overlays and preserved {len(seen)} existing artifact paths.')
