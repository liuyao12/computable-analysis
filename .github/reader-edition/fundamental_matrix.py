#!/usr/bin/env python3
"""Publish a standalone classical ODE exposition within the existing reader site."""
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
    home = site / 'index.html'
    ode = site / 'ch-differential-equations.html'
    for path in [home, ode, site / 'programme.html', site / 'reading/manifest.json']:
        if not path.is_file():
            raise SystemExit(f'Missing reader input: {path}')
    proof_manifest = json.loads((site / 'reading/manifest.json').read_text())
    # Existing reader HTML receives only delimited incoming links. Proof reports,
    # reference pages, and assets remain byte-identical.
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
            snippet = '<section id="fundamental-matrix-link" class="fm-reader-link"><h2>Fundamental Matrix</h2><p>A standalone introduction to Picard iteration: nonlinear growth and saturation, followed by one solution operator for linear equations with variable coefficients and forcing.</p><p><a href="fundamental-matrix.html">Read the interactive page →</a></p></section>'
            text = text.replace('</article>', marked(snippet) + '</article>', 1)
        if path == ode:
            snippet = '<aside class="fm-reader-link"><p><a href="fundamental-matrix.html"><strong>Fundamental Matrix — an interactive exposition</strong></a></p><p>Begin with explicit nonlinear Picard iterates; then obtain the linear solution, forcing term and worked examples from the same construction.</p></aside>'
            text = re.sub(r'(<h1\b[^>]*>[\s\S]*?</h1>)', lambda m: m[0] + marked(snippet), text, count=1)
        path.write_text(text)
        changed.append(str(path.relative_to(site)))
    assert PAGE in home.read_text() and PAGE in ode.read_text()
    subprocess.run(['node', str(SOURCE / 'build.cjs'), str(site.resolve() / PAGE)], check=True)
    page = (site / PAGE).read_text()
    # Keep the authored title and in-page navigation. Hosting in the book does
    # not add project branding, proof-status text, or a book contents menu.
    page = page.replace('</head>', '<style>' + (SOURCE / 'site.css').read_text() + '</style></head>', 1)
    page = page.replace('</body>', '<script>' + (SOURCE / 'site.js').read_text() + '</script></body>', 1)
    assert 'computable analysis' not in page.lower()
    assert 'computable-analysis' not in page.lower()
    document = BeautifulSoup(page, 'html.parser')
    assert document.select_one('.brand')['href'] == '#top'
    assert document.select_one('#nonlinear') and document.select_one('#saturation')
    (site / PAGE).write_text(page)
    for name, sha in before.items():
        path = site / name
        if name in changed:
            assert hashlib.sha256(ADDITION.sub('', path.read_text()).encode()).hexdigest() == sha, name
        else:
            assert digest(path) == sha, name
    report = {
        'page': PAGE, 'title': 'Fundamental Matrix',
        'documentationRevision': args.revision,
        'proofSourceCommit': proof_manifest['proofSourceCommit'],
        'newLeanProofsClaimed': False, 'leanSourceModified': False,
        'standalonePresentation': True, 'nonlinearExamples': ['growth', 'saturation'],
        'sourceDirectory': 'book/fundamental-matrix',
        'arithmetic': 'Exact BigInt rational polynomial Picard iteration',
        'changedReaderPages': changed, 'originalFileHashes': before,
        'pageSha256': digest(site / PAGE),
        'checks': {'originalBytesOutsideMarkedAdditionsPreserved': True,
                   'proofSnapshotPreserved': True, 'homeLinked': True,
                   'differentialEquationsChapterLinked': True,
                   'standalonePresentation': True, 'nonlinearExamplesIncluded': True}
    }
    (site / 'reading/fundamental-matrix-edition.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Integrated standalone {PAGE}; linked from {len(changed)} reader pages; proof data preserved.')

if __name__ == '__main__':
    main()
