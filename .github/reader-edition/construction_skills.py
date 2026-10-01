#!/usr/bin/env python3
"""Render function-specific skill sources and expose them in the book navigation.

Install before the reader editions record their HTML hashes. Finalize after all
editions so the publication record describes the actual delivered pages.
"""
import argparse
import hashlib
import html
import json
import os
import re
from pathlib import Path
from urllib.parse import urlsplit

import markdown
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'book/construction-skills'
NAV = re.compile(r'<nav\b[^>]*\bid=["\']book-nav["\'][^>]*>[\s\S]*?</nav>')
MATH = re.compile(r'\\\[[\s\S]*?\\\]|\\\([\s\S]*?\\\)')
OVERVIEW = 'construction-skills.html'


def catalogue(examples=False):
    rows = json.loads((SOURCE / ('examples.json' if examples else 'catalogue.json')).read_text())
    assert len({r['page'] for r in rows}) == len(rows)
    for row in rows:
        if not examples:
            assert re.fullmatch(r'[a-z0-9-]+', row['skill'])
        assert re.fullmatch(r'skill-[a-z0-9-]+\.html', row['page'])
        assert (ROOT / row['source']).is_file()
    return rows


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def render_skill(row, revision):
    source = ROOT / row['source']
    text = source.read_text()
    body = text.split('---', 2)[2] if text.startswith('---\n') else text
    formulas = []

    def protect(match):
        formulas.append(match.group())
        return f'CONSTRUCTIONMATHPLACEHOLDER{len(formulas)-1}END'

    rendered = markdown.markdown(MATH.sub(protect, body), extensions=['fenced_code', 'tables'])
    for i, formula in enumerate(formulas):
        rendered = rendered.replace(f'CONSTRUCTIONMATHPLACEHOLDER{i}END', html.escape(formula))
    doc = BeautifulSoup(rendered, 'html.parser')
    pages = {r['source']: r['page'] for r in catalogue() + catalogue(examples=True)}
    pages.update({'blueprint/src/03-integrals.tex': 'ch-integrals.html',
                  'blueprint/src/13-complex-paths.tex': 'ch-complex-paths.html',
                  'blueprint/src/04-infinite-series.tex': 'ch-infinite-series.html',
                  'book/classics/analytic-continuation.html': 'analytic-continuation.html',
                  'book/classics/zeta-zeros.html': 'zeta-zeros.html',
                  'book/rational-primitives/index.html': 'rational-primitives.html',
                  'docs/POWER_IMPROPER.md': 'power-improper.html',
                  'docs/GAUSSIAN_CONVOLUTION.md': 'gaussian-convolution.html',
                  'docs/N_BALL_GAMMA.md': 'n-ball-volume.html',
                  'docs/RATIONAL_PRIMITIVES.md': 'rational-primitives.html',
                  'docs/POLYGONAL_CAUCHY.md': 'complex-analysis.html',
                  'book/cosine-square/page.html': 'cosine.html'})
    for link in doc.select('a[href]'):
        href = link['href']
        if urlsplit(href).scheme or href.startswith('#'):
            continue
        path, _, fragment = href.partition('#')
        resolved = (source.parent / path).resolve()
        relative = str(resolved.relative_to(ROOT))
        assert resolved.is_file(), (source, href)
        link['href'] = pages.get(relative, f'https://github.com/liuyao12/computable-analysis/blob/{revision}/{relative}')
        if fragment:
            link['href'] += '#' + fragment
    for p in doc.select('p'):
        if p.get_text().strip().startswith(r'\['):
            p['class'] = ['formula']
    for i, heading in enumerate(doc.select('h2')):
        heading['id'] = 'step-' + str(i+1)
    return str(doc)


def add_navigation(path, site, rows):
    original = path.read_text()
    match = NAV.search(original)
    if not match:
        return False
    nav = BeautifulSoup(match.group(), 'html.parser').nav
    assert not nav.select('.construction-skill-navigation, .construction-skill-label'), path
    links = [(r['page'], r['title']) for r in rows]
    section = BeautifulSoup('<a class="nav-label construction-skill-label">Skills</a>', 'html.parser')
    section.a['href'] = os.path.relpath(site / OVERVIEW, path.parent).replace(os.sep, '/')
    for target, title in links:
        href = os.path.relpath(site / target, path.parent).replace(os.sep, '/')
        link = section.new_tag('a', href=href, attrs={'class': 'construction-skill-navigation'})
        link.string = title
        section.append(link)
    chapters = nav.select_one(".later-chapters")
    assert chapters is not None, (path, "missing chapter navigation")
    for node in reversed(list(section.contents)):
        chapters.insert_after(node.extract())
    updated = original[:match.start()] + str(nav) + original[match.end():]
    # Only the existing navigation may change; preserve all other bytes.
    assert NAV.sub('', updated, count=1) == NAV.sub('', original, count=1)
    path.write_text(updated)
    return True


def make_page(template, body, title, name, revision, row=None):
    doc = BeautifulSoup(template, 'html.parser')
    doc.title.string = title + ' · Computable Analysis'
    meta = doc.select_one('meta[name="documentation-revision"]')
    if not meta:
        meta = doc.new_tag('meta', attrs={'name': 'documentation-revision'})
        doc.head.append(meta)
    meta['content'] = revision
    doc.select_one('meta[name="description"]')['content'] = 'Integrals, series, holomorphic functions, and analytic continuation: constructions and proof status.'
    for link in doc.select('#book-nav a.current'):
        link['class'] = [c for c in link.get('class', []) if c != 'current']
        link.attrs.pop('aria-current', None)
    active_name = name if row is None or 'skill' in row else row.get('parent', 'skill-real-integrals.html')
    active = doc.select_one(f'#book-nav a[href="{active_name}"]')
    assert active
    active['class'] = active.get('class', []) + ['current']
    active['aria-current'] = 'page'
    main = doc.select_one('main.reader')
    assert main
    main.clear()
    if row is None:
        main.append(BeautifulSoup('<div class="chapter-kicker">SKILLS</div>', 'html.parser'))
    article = doc.new_tag('article', attrs={'class': 'construction-skill'})
    article.append(BeautifulSoup(body, 'html.parser'))
    main.append(article)
    toc = doc.select_one('.on-this-page')
    if toc:
        toc.clear()
        for heading in article.select('h2[id]'):
            link = doc.new_tag('a', href='#' + heading['id'])
            link.string = heading.get_text()
            toc.append(link)
    if row:
        main.append(BeautifulSoup(f'<footer class="chapter-footer construction-skill-links"><a href="reading/{row["source"]}" download>Download Markdown</a><a href="https://github.com/liuyao12/computable-analysis/blob/{revision}/{row["source"]}">View source</a></footer>', 'html.parser'))
    else:
        main.append(BeautifulSoup(f'<footer class="chapter-footer"><a href="https://github.com/liuyao12/computable-analysis/tree/{revision}/skills">Skill sources · {revision[:12]}</a></footer>', 'html.parser'))
    doc.head.append(doc.new_tag('link', rel='stylesheet', href='reading/construction-skills.css'))
    assert not doc.select('article sup, article sub')
    return str(doc)


def install(site, revision):
    rows = catalogue()
    assert not (site / OVERVIEW).exists(), 'Construction skills already installed'
    for path in sorted(site.rglob('*.html')):
        if 'reference' not in path.relative_to(site).parts:
            add_navigation(path, site, rows)
    template = (site / 'programme.html').read_text()
    cards = []
    for row in rows:
        cards.append(f'<section class="construction-skill-card"><h3><a href="{row["page"]}">{html.escape(row["title"])}</a></h3><p>{html.escape(row["summary"])}</p><p class="construction-skill-status">{html.escape(row["status"])}</p><a href="{row["page"]}">Read the construction →</a></section>')
    for row in rows + catalogue(examples=True):
        body = render_skill(row, revision)
        (site / row['page']).write_text(make_page(template, body, row['title'], row['page'], revision, row))
        target = site / 'reading' / row['source']
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((ROOT / row['source']).read_bytes())
    body = (SOURCE / 'index.html').read_text().replace('__CARDS__', ''.join(cards)).replace('__REPO__', f'https://github.com/liuyao12/computable-analysis/blob/{revision}/')
    (site / OVERVIEW).write_text(make_page(template, body, 'Skills', OVERVIEW, revision))
    (site / 'reading/construction-skills.css').write_bytes((SOURCE / 'skills.css').read_bytes())
    print('Installed construction skills after the chapters')


def finalize(site, revision):
    rows = catalogue()
    all_rows = rows + catalogue(examples=True)
    pages = [OVERVIEW] + [r['page'] for r in all_rows]
    navigation = []
    for path in sorted(site.rglob('*.html')):
        if 'reference' in path.relative_to(site).parts:
            continue
        doc = BeautifulSoup(path.read_text(), 'html.parser')
        if doc.select_one('#book-nav'):
            assert len(doc.select('#book-nav .construction-skill-navigation')) == len(rows), path
            navigation.append(str(path.relative_to(site)))
    files = pages + ['reading/construction-skills.css'] + ['reading/' + r['source'] for r in all_rows]
    report = dict(documentationRevision=revision, newLeanTheoremsClaimed=False,
                  skills=rows, constructionExamples=catalogue(examples=True), navigationPages=navigation,
                  sourceHashes={r['source']: digest(ROOT / r['source']) for r in all_rows},
                  artifacts={p: digest(site / p) for p in files})
    (site / 'reading/construction-skills.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Recorded final skills, downloads, and navigation in', len(navigation), 'reader pages')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--revision', required=True)
    parser.add_argument('--finalize', action='store_true')
    args = parser.parse_args()
    assert re.fullmatch(r'[0-9a-f]{40}', args.revision)
    (finalize if args.finalize else install)(args.site, args.revision)
