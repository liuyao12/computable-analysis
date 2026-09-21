#!/usr/bin/env python3
"""Add an expository ODE page without altering the verified proof snapshot."""
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
    # All existing bytes are recorded. Root reader HTML receives only delimited
    # additions; proof reports, assets, and reference pages are byte-preserved.
    before = {str(p.relative_to(site)): (hashlib.sha256(ADDITION.sub('', p.read_text()).encode()).hexdigest() if p.parent == site and p.suffix == '.html' else digest(p)) for p in site.rglob('*')
              if p.is_file() and p.name not in [PAGE, 'fundamental-matrix-edition.json']}
    changed = []
    for path in sorted(site.glob('*.html')):
        if path.name == PAGE:
            continue
        original = path.read_text()
        original = ADDITION.sub('', original)
        match = NAV.search(original)
        if not match:
            continue
        nav = match.group()
        anchor = re.search(r'<a\b[^>]*href=[\"\']ch-differential-equations\.html[\"\'][^>]*>[\s\S]*?</a>', nav)
        pos = match.start() + (anchor.end() if anchor else nav.rfind('</nav>'))
        text = original[:pos] + marked(ENTRY) + original[pos:]
        if path == home:
            snippet = '<section id="fundamental-matrix-link" class="fm-reader-link"><h2>Fundamental Matrix</h2><p>Picard iteration builds one solution operator for linear differential equations, with variable coefficients and forcing. Work through the examples in an exact-rational interactive notebook.</p><p><a href="fundamental-matrix.html">Read the page →</a></p></section>'
            text = text.replace('</article>', marked(snippet) + '</article>', 1)
        if path == ode:
            snippet = '<aside class="fm-reader-link"><p><a href="fundamental-matrix.html"><strong>Fundamental Matrix — an interactive exposition</strong></a></p><p>Begin with Picard iteration; obtain the general solution, forcing term and worked examples from the same construction. The notebook is an explanatory companion to this chapter, not a new Lean verification claim.</p></aside>'
            text = re.sub(r'(<h1\b[^>]*>[\s\S]*?</h1>)', lambda m: m[0] + marked(snippet), text, count=1)
        path.write_text(text)
        changed.append(str(path.relative_to(site)))
    assert PAGE in home.read_text() and PAGE in ode.read_text()
    subprocess.run(['node', str(SOURCE / 'build.cjs'), str(site.resolve() / PAGE)], check=True)
    page = (site / PAGE).read_text()
    nav_match = NAV.search(home.read_text())
    assert nav_match, 'The book navigation must remain available.'
    nav = BeautifulSoup(nav_match.group(), 'html.parser').nav
    nav['id'] = 'fm-book-contents'
    nav['aria-label'] = 'Computable Analysis book contents'
    for a in nav.select('a.current'):
        a['class'] = [c for c in a.get('class', []) if c != 'current']
        a.attrs.pop('aria-current', None)
    current = nav.find('a', href=PAGE)
    current['class'] = ['current']
    current['aria-current'] = 'page'
    for parent in current.parents:
        if parent.name == 'details':
            parent['open'] = ''
    header = '<header class="topbar"><a class="brand" href="index.html">Computable <em>Analysis</em></a><details class="book-menu"><summary>Contents</summary>' + str(nav) + '</details><nav class="local-nav" aria-label="On this page"><a href="#iteration">Iteration</a><a href="#matrix">The matrix</a><a href="#forcing">Forcing</a><a href="#examples">Examples</a><a href="#convergence">Convergence</a></nav></header>'
    page = re.sub(r'<header class="topbar">[\s\S]*?</header>', lambda _: header, page, count=1)
    page = re.sub(r'<title>[\s\S]*?</title>', '<title>Fundamental Matrix · Computable Analysis</title>', page, count=1)
    page = page.replace('Differential equations / one construction', 'Computable Analysis / Differential equations')
    page = page.replace('<footer id="sources"', '<p class="book-return"><a href="ch-differential-equations.html">← Differential equations chapter</a> · <a href="index.html">Book contents</a></p><footer id="sources"', 1)
    page = page.replace('</head>', '<style>' + (SOURCE / 'site.css').read_text() + '</style></head>', 1)
    page = page.replace('</body>', '<script>' + (SOURCE / 'site.js').read_text() + '</script></body>', 1)
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
        'sourceDirectory': 'book/fundamental-matrix',
        'arithmetic': 'Exact BigInt rational polynomial matrix iteration',
        'changedReaderPages': changed, 'originalFileHashes': before,
        'pageSha256': digest(site / PAGE),
        'checks': {'originalBytesOutsideMarkedAdditionsPreserved': True,
                   'proofSnapshotPreserved': True, 'homeLinked': True,
                   'differentialEquationsChapterLinked': True}
    }
    (site / 'reading/fundamental-matrix-edition.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Integrated {PAGE}; linked from {len(changed)} reader pages; proof data preserved.')

if __name__ == '__main__':
    main()
