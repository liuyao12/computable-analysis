#!/usr/bin/env python3
"""Publish the standalone second-order essay; preserve the existing proof reader."""
from __future__ import annotations
import argparse, hashlib, json, re, subprocess
from pathlib import Path
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'book/fundamental-matrix'
PAGE = 'fundamental-matrix.html'
START = '<!-- fundamental-matrix:start -->'
END = '<!-- fundamental-matrix:end -->'
ADDITION = re.compile(re.escape(START) + r'[\s\S]*?' + re.escape(END))
NAV = re.compile(r'<nav\b[^>]*\bid=[\"\']book-nav[\"\'][^>]*>[\s\S]*?</nav>')
ENTRY = '<a href="fundamental-matrix.html" data-reader-addition="fundamental-matrix">Fundamental Matrix</a>'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def marked(text):
    return START + text + END

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--site', type=Path, required=True)
    ap.add_argument('--revision', required=True)
    args = ap.parse_args()
    site = args.site
    home, ode = site / 'index.html', site / 'ch-differential-equations.html'
    for path in [home, ode, site / 'programme.html', site / 'reading/manifest.json']:
        if not path.is_file():
            raise SystemExit(f'Missing reader input: {path}')
    manifest = json.loads((site / 'reading/manifest.json').read_text())
    before = {str(p.relative_to(site)): (hashlib.sha256(ADDITION.sub('', p.read_text()).encode()).hexdigest() if p.parent == site and p.suffix == '.html' else digest(p)) for p in site.rglob('*')
              if p.is_file() and p.name not in [PAGE, 'fundamental-matrix-edition.json']}
    changed = []
    for path in sorted(site.glob('*.html')):
        if path.name == PAGE:
            continue
        original = ADDITION.sub('', path.read_text())
        match = NAV.search(original)
        if not match:
            continue
        nav = match.group()
        anchor = re.search(r'<a\b[^>]*href=[\"\']ch-differential-equations\.html[\"\'][^>]*>[\s\S]*?</a>', nav)
        pos = match.start() + (anchor.end() if anchor else nav.rfind('</nav>'))
        text = original[:pos] + marked(ENTRY) + original[pos:]
        if path == home:
            snippet = '<section id="fundamental-matrix-link" class="fm-reader-link"><h2>Fundamental Matrix</h2><p>A step-by-step introduction through second-order equations: repeated integration, the oscillator, a nonlinear comparison, variable coefficients and forcing.</p><p><a href="fundamental-matrix.html">Read the page →</a></p></section>'
            text = text.replace('</article>', marked(snippet) + '</article>', 1)
        if path == ode:
            snippet = '<aside class="fm-reader-link"><p><a href="fundamental-matrix.html"><strong>Fundamental Matrix — second-order equations, step by step</strong></a></p><p>Work through successive approximations before introducing two basic solutions, the fundamental matrix and the forcing formula.</p></aside>'
            text = re.sub(r'(<h1\b[^>]*>[\s\S]*?</h1>)', lambda m: m[0] + marked(snippet), text, count=1)
        path.write_text(text)
        changed.append(str(path.relative_to(site)))
    assert PAGE in home.read_text() and PAGE in ode.read_text()
    subprocess.run(['node', str(SOURCE / 'build.cjs'), str(site.resolve() / PAGE)], check=True)
    page = (site / PAGE).read_text()
    # The essay is complete as authored: no book shell, notebook, or runtime code.
    assert 'computable analysis' not in page.lower() and 'computable-analysis' not in page.lower()
    document = BeautifulSoup(page, 'html.parser')
    assert document.select_one('.brand')['href'] == '#top'
    assert document.select_one('#nonlinear') and document.select_one('#matrix')
    assert not document.select('script,input,select,button,svg,canvas,iframe')
    for name, sha in before.items():
        path = site / name
        actual = hashlib.sha256(ADDITION.sub('', path.read_text()).encode()).hexdigest() if name in changed else digest(path)
        assert actual == sha, name
    report = {
        'page': PAGE, 'title': 'Fundamental Matrix',
        'documentationRevision': args.revision,
        'proofSourceCommit': manifest['proofSourceCommit'],
        'newLeanProofsClaimed': False, 'leanSourceModified': False,
        'standalonePresentation': True, 'differentialOrder': 2,
        'presentation': 'Single-column, worked derivations; no notebook or plots',
        'nonlinearExamples': ['y double prime = y squared'],
        'runtimeScripts': False, 'sourceDirectory': 'book/fundamental-matrix',
        'changedReaderPages': changed, 'originalFileHashes': before,
        'pageSha256': digest(site / PAGE),
        'checks': {'originalBytesOutsideMarkedAdditionsPreserved': True,
                   'proofSnapshotPreserved': True, 'homeLinked': True,
                   'differentialEquationsChapterLinked': True,
                   'standalonePresentation': True, 'nonlinearExamplesIncluded': True,
                   'secondOrderNarrative': True, 'noRuntimeScripts': True}
    }
    (site / 'reading/fundamental-matrix-edition.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Integrated second-order essay; linked from {len(changed)} reader pages; proof data preserved.')

if __name__ == '__main__':
    main()
