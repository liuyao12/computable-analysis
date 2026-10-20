#!/usr/bin/env python3
"""Overlay the checked geometric-trigonometry audit on the established reader."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import shutil
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[1]
MATH = re.compile(r'\\\(.*?\\\)|\\\[.*?\\\]', re.S)
IDS = re.compile(r'\bid=[\"\']([^\"\']+)[\"\']')


def apply(site):
    before = {str(p.relative_to(site)): p.read_bytes() for p in site.rglob('*') if p.is_file()}
    content = (ROOT / 'book/trigonometry-audit/content.html').read_text()
    assert '<sup' not in content and '<sub' not in content
    assert content.count('\\(') == content.count('\\)')
    assert content.count('\\[') == content.count('\\]')
    page = (site / 'preface.html').read_text()
    page = re.sub(r'<title>.*?</title>', '<title>Geometric sine and cosine audit · Computable Analysis</title>', page, count=1)
    page = re.sub(r'<meta name="description" content="[^"]*">', '<meta name="description" content="The geometric arctangent to sine and cosine construction, exact inverse-circle checks, and the fixed-grid integral question.">', page, count=1)
    page = page.replace('aria-current="page"', '').replace('class="current"', 'class=""')
    page, count = re.subn(r'<article>.*?</article>', lambda _: '<article><div class="main-text">' + content + '</div></article>', page, count=1, flags=re.S)
    assert count == 1
    toc = ''.join('<a href="#' + key + '">' + title + '</a>' for key, title in re.findall(r'<h2 id="([^"]+)">([^<]+)</h2>', content))
    page = re.sub(r'<aside class="on-this-page">.*?</aside>', '<aside class="on-this-page"><span>On this page</span>' + toc + '</aside>', page, count=1, flags=re.S)
    page = page.replace('<div class="chapter-kicker">PREFACE</div>', '<div class="chapter-kicker">CONSTRUCTION AUDIT</div>')
    page = re.sub(r'<footer class="chapter-footer">.*?</footer>', '<footer class="chapter-footer"><span>Concrete inverse; justified angle and coordinates</span><a href="identification-audit.html">Identification strategy</a></footer>', page, count=1, flags=re.S)
    page = page.replace('</style>', '.audit-table{overflow-x:auto}.audit-table table{width:100%;border-collapse:collapse;font-size:.9rem}.audit-table th,.audit-table td{padding:.8rem .6rem;border-bottom:1px solid #d8ded9;text-align:left;vertical-align:top}.audit-table td:first-child{width:27%;font-weight:600}</style>')
    (site / 'geometric-trigonometry-audit.html').write_text(page)

    assets = site / 'geometric-trigonometry-audit'
    assets.mkdir(exist_ok=True)
    (assets / 'audit.md').write_bytes((ROOT / 'docs/GEOMETRIC_TRIGONOMETRY_AUDIT.md').read_bytes())
    source = ROOT / 'book/trigonometry-audit/proof'
    report = json.loads((source / 'verification/report.json').read_text())
    assert report['coldBuild'] and report['modulesBuilt'] == 52
    assert len(report['auditedTheorems']) == 7
    for rel, expected in report['sourceSha256'].items():
        assert hashlib.sha256((source / rel).read_bytes()).hexdigest() == expected, rel
    shutil.copytree(source, assets / 'proof', dirs_exist_ok=True)
    with (assets / 'proof.tar.gz').open('wb') as out:
        with gzip.GzipFile(filename='', mode='wb', fileobj=out, mtime=0) as gz:
            with tarfile.open(fileobj=gz, mode='w') as archive:
                for path in sorted(source.rglob('*')):
                    if not path.is_file():
                        continue
                    info = archive.gettarinfo(str(path), arcname='arctan-circle-proof/' + str(path.relative_to(source)))
                    info.mtime, info.uid, info.gid = 0, 0, 0
                    info.uname = info.gname = ''
                    info.mode = 0o644
                    with path.open('rb') as data:
                        archive.addfile(info, data)

    changed = {'identification-audit.html'}
    target = site / 'identification-audit.html'
    old = target.read_text()
    fragment = '<section id="geometric-trigonometry-followup"><h2>A checked geometric trigonometry follow-up</h2><p>The next audit follows geometric arctangent through the concrete inverse to sine and cosine. It adds exact chart, endpoint and angle-clock checks, with a cold-built proof bundle. Read the <a href="geometric-trigonometry-audit.html">geometric trigonometry audit</a> and the remaining public-interface bridges.</p></section>'
    assert 'id="geometric-trigonometry-followup"' not in old
    assert '<h2 id="sources">' in old
    target.write_text(old.replace('<h2 id="sources">', fragment + '<h2 id="sources">', 1))
    for name in changed:
        old = before[name].decode()
        new = (site / name).read_text()
        assert set(IDS.findall(old)) <= set(IDS.findall(new)), name
        cursor = iter(MATH.findall(new))
        assert all(any(candidate == formula for candidate in cursor) for formula in MATH.findall(old)), name
    for name, data in before.items():
        if name not in changed:
            assert (site / name).read_bytes() == data, name
    publication = {'changedExistingPages': sorted(changed), 'preservedFiles': len(before)-len(changed),
                   'preservedExistingMath': True, 'preservedExistingAnchors': True,
                   'proofModules': report['modulesBuilt'], 'auditedTheorems': report['auditedTheorems'],
                   'contentSha256': hashlib.sha256(content.encode()).hexdigest(),
                   'proofArchiveSha256': hashlib.sha256((assets/'proof.tar.gz').read_bytes()).hexdigest()}
    (assets / 'publication.json').write_text(json.dumps(publication, indent=2) + '\n')
    print('PASS: exact source manifest; preserved', publication['preservedFiles'], 'existing files and all existing mathematics and anchors.')


if __name__ == '__main__':
    apply(Path(sys.argv[1]))
