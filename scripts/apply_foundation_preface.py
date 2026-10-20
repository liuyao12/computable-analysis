"""Add a reader preface while retaining the deployed mathematics and proof assets."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
CONTENT = ROOT / 'book/foundation-preface/content.html'
LINK = '<a data-foundation-preface="true" href="preface.html">Preface</a>'
NAV = re.compile(r'<nav\b[^>]*\bid=[\"\']book-nav[\"\'][^>]*>.*?</nav>', re.S)
ID = re.compile(r'\bid=[\"\']([^\"\']+)[\"\']')
MATH = re.compile(r'\\\(.*?\\\)|\\\[.*?\\\]', re.S)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def add_nav(text):
    def replace(match):
        nav = match[0]
        if 'data-foundation-preface="true"' in nav:
            return nav
        label = re.search(r'<span class="nav-label">The book</span>', nav)
        assert label, 'Book label missing'
        return nav[:label.end()] + LINK + nav[label.end():]
    return NAV.sub(replace, text)

def apply(site):
    before = {str(p.relative_to(site)): p.read_bytes() for p in site.rglob('*') if p.is_file()}
    changed = set()
    for name, data in before.items():
        if not name.endswith('.html'):
            continue
        text = data.decode('utf-8')
        if not NAV.search(text):
            continue
        edited = add_nav(text)
        if name == 'index.html':
            intro = '<section id="foundation-preface-intro"><h2>Read the preface</h2><p>How an Observable programming exercise grew into a foundation for proving calculus: rational algorithms, square-root intervals, and different computations of pi.</p><p><a href="preface.html">From a programming exercise to a foundation</a></p></section>'
            if 'id="foundation-preface-intro"' in edited:
                edited, count = re.subn(r'<section id="foundation-preface-intro">.*?</section>', lambda _: intro, edited, count=1, flags=re.S)
                assert count == 1
            else:
                anchor = '<section id="foundation-story">'
                assert anchor in edited
                edited = edited.replace(anchor, intro + anchor, 1)
        if name == 'ch-foundations.html' and 'class="preface-reader-link"' not in edited:
            anchor = '<div class="chapter-kicker">'
            assert anchor in edited
            edited = edited.replace(anchor, '<p class="preface-reader-link"><a href="preface.html">Before Chapter 1: how to read this foundation</a></p>' + anchor, 1)
        # Navigation and introductions may be added; existing mathematics and
        # theorem anchors must remain unchanged even in the edited pages.
        assert MATH.findall(edited) == MATH.findall(text), name
        assert set(ID.findall(text)) <= set(ID.findall(edited)), name
        if edited != text:
            (site / name).write_text(edited)
            changed.add(name)
    template = (site / 'ch-foundations.html').read_text()
    nav = NAV.search(template)[0]
    nav = re.sub(r'class="current"', 'class=""', nav)
    nav = nav.replace(LINK, '<a class="current" aria-current="page" data-foundation-preface="true" href="preface.html">Preface</a>')
    header = re.search(r'<header class="book-header">.*?</header>', template, re.S)[0]
    content = CONTENT.read_text()
    assert '<h1 id="preface">' in content
    assert '<sup' not in content and '<sub' not in content
    assert content.count('\\(') == content.count('\\)')
    assert content.count('\\[') == content.count('\\]')
    toc = ''.join('<a href="#'+key+'">'+title+'</a>' for key, title in re.findall(r'<h2 id="([^"]+)">([^<]+)</h2>', content))
    head = r'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="description" content="From Observable and exact fractions to a foundation for proving calculus, with rational square-root algorithms and stage-by-stage decimal enclosures."><title>Preface · Computable Analysis</title><link href="reading/book.css" rel="stylesheet"><link href="reading/analysis-edition.css" rel="stylesheet"><script>window.MathJax={tex:{inlineMath:[['\\(','\\)']],displayMath:[['\\[','\\]']],processEscapes:true},options:{skipHtmlTags:['script','noscript','style','textarea','pre','code']}};</script><script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script><script defer src="reading/book.js"></script><style>.reader h1,.reader h2{overflow-wrap:anywhere}.reader mjx-container{max-width:100%;overflow-x:auto;overflow-y:hidden}.reader{min-width:0}.preface-reader-link{font:12px/1.7 system-ui}.preface-table{overflow-x:auto;margin:1.4rem 0;padding-bottom:.4rem}.preface-table table{border-collapse:collapse;width:100%;font-size:.88rem}.preface-table th,.preface-table td{padding:.65rem .6rem;border-bottom:1px solid #d8ded9;text-align:left;white-space:nowrap}.preface-table thead th{font:600 .75rem/1.5 system-ui;color:#52615b}.decimal-number{display:inline-flex;align-items:baseline;gap:0}.decimal-number mjx-container{margin:0!important;overflow:visible!important;flex:none}.preface-table mark{background:#f5e3a0;color:inherit;padding:2px 0;border-radius:2px}.reader pre{overflow-x:auto;padding:1.2rem;background:#f3f5f2;border:1px solid #dce2da;border-radius:8px;line-height:1.7}.reader pre code{font-size:.87rem}</style></head><body><a class="skip" href="#main">Skip to preface</a>'''
    footer = '<footer class="chapter-footer"><span>From Observable to exact mathematical proofs</span><a href="foundation-preface/00-preface.tex">Preface manuscript</a></footer>'
    html = head + header + nav + '<div class="page"><main class="reader" id="main"><div class="chapter-kicker">PREFACE</div><article><div class="main-text">' + content + '</div></article>' + footer + '</main><aside class="on-this-page"><span>On this page</span>' + toc + '</aside></div></body></html>\n'
    (site / 'preface.html').write_text(html)
    assets = site / 'foundation-preface'
    assets.mkdir(exist_ok=True)
    (assets / 'content.html').write_text(content)
    (assets / '00-preface.tex').write_bytes((ROOT / 'blueprint/src/00-preface.tex').read_bytes())
    map_path = site / 'foundation-story/index.html'
    map_text = map_path.read_text()
    if 'href="../preface.html"' not in map_text:
        map_path.write_text(map_text.replace('<nav>', '<nav><a href="../preface.html">Preface</a>', 1))
        changed.add('foundation-story/index.html')
    for name in ["preface.html", "foundation-preface/content.html", "foundation-preface/00-preface.tex"]:
        if name in before and (site / name).read_bytes() != before[name]:
            changed.add(name)
    for name, data in before.items():
        if name not in changed:
            assert (site / name).read_bytes() == data, name
    report = {'changedExistingPages': sorted(changed), 'preservedFiles': len(before) - len(changed), 'preservedExistingMath': True, 'preservedExistingAnchors': True, 'contentSha256': sha(CONTENT.read_bytes()), 'leanSourcesChanged': False}
    (assets / 'publication.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: added preface and navigation to', len(changed), 'pages;', report['preservedFiles'], 'existing files preserved; existing mathematics and anchors unchanged.')
    return report

if __name__ == '__main__':
    apply(Path(sys.argv[1]))
