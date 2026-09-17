#!/usr/bin/env python3
"""Finalize the reader edition: the pi examples belong to Chapter 1.

Run after analysis_edition.py and its baseline tests. This placement-only pass
keeps all proof data and the worked cosine quadrature illustration unchanged.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path
from bs4 import BeautifulSoup

DESTINATION = 'ch-foundations.html#pi-computations'
OTHER = 'rem:sources-of-raw-reals'


def parse(text: str):
    return BeautifulSoup(text, 'html.parser')


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mathematical_text(doc) -> str:
    article = parse(str(doc.article))
    for item in article.select('#pi-computations'):
        item.decompose()
    heading = article.find(id=OTHER)
    heading.string = '1.2.2 Other computations of numbers'
    return re.sub(r'\s+', ' ', article.get_text(' ', strip=True))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--site', type=Path, required=True)
    ap.add_argument('--revision', required=True)
    args = ap.parse_args()
    site = args.site
    report_path = site / 'reading/analysis-edition.json'
    report = json.loads(report_path.read_text())
    assert report['proofDeclarationsAndEdgesUnchanged']
    protected = dict(report['protectedArtifacts'])
    for path in ['reading/maps.json', 'reading/animations/cosine.gif',
                 'reading/animations/cosine.png', 'reading/cosine-half-interval.json']:
        protected[path] = sha(site / path)
    worked_files = ['cosine.html', 'dyadic-integral.html']
    worked = {name: str(parse((site / name).read_text()).article) for name in worked_files}

    chapter_path = site / 'ch-foundations.html'
    chapter = parse(chapter_path.read_text())
    before = mathematical_text(chapter)
    other = chapter.find(id=OTHER)
    gallery = chapter.select_one('#pi-computations')
    assert other and gallery, 'Expected the restored catalogue and original examples subsection'
    assert chapter.find(id='rem:algebraic-numbers-sqrt-two')
    cosine = gallery.select_one('#pi-cosine')
    if cosine:
        cosine.decompose()
    assert len(gallery.select('.pi-formula-card')) == 9
    gallery.extract()
    other.string = '1.2.2 Other examples'
    other.insert_after(gallery)
    title = gallery.find(['h2', 'h3'])
    title.name = 'h3'
    for link in gallery.select('a[href]'):
        if link['href'] == 'pi-computations.html#programme':
            link['href'] = '#pi-computation-programme'
    if not gallery.select_one('#pi-computation-programme'):
        detail = parse('''<details id="pi-computation-programme"><summary>Construction and equivalence programme</summary><p>Each formula suggests an independently specified rational-enclosure computation. Its chosen schedule needs a convergence certificate, and its identification with geometric π is a separate theorem. The displayed formulas are mathematical destinations, not a claim that every native equivalence is already proved.</p><p>Geometry, finite recurrences, series tails, algebraic substitutions and improper-integral estimates supply different parts of the foundation. Their checked declarations and alternative proof routes belong in the later chapters and worked comparisons.</p></details>''').details
        gallery.append(detail)
    assert mathematical_text(chapter) == before, 'Mathematical chapter content changed'
    toc = chapter.select_one('.on-this-page')
    if toc:
        for link in toc.select('a[href="#' + OTHER + '"]'):
            link.string = '1.2.2 Other examples'
        links = toc.select('a[href="#pi-computations"]')
        anchor = toc.select_one('a[href="#' + OTHER + '"]')
        if anchor and links:
            links[0].extract()
            anchor.insert_after(links[0])
    chapter_path.write_text(str(chapter))

    home_path = site / 'index.html'
    home = parse(home_path.read_text())
    for teaser in home.select('.pi-teaser, #pi-computations'):
        teaser.decompose()
    # Keep a modest navigation link, not a duplicate formula gallery or teaser.
    if not home.select_one('.chapter-one-examples-link'):
        link = parse('<p class="chapter-one-examples-link"><a href="' + DESTINATION + '">Other examples in Chapter 1: computations of π →</a></p>').p
        pair = home.select_one('.chapter-pair')
        assert pair
        pair.insert_after(link)
    home_path.write_text(str(home))

    for page in sorted(site.glob('*.html')):
        if page.name == 'pi-computations.html':
            continue
        doc = parse(page.read_text())
        nav = doc.select_one('#book-nav')
        if not nav:
            continue
        for link in nav.select('.pi-catalogue-navigation'):
            link['href'] = DESTINATION
            link.string = 'Other examples: π'
        page.write_text(str(doc))

    # One canonical location, while preserving the bookmark from the last edition.
    (site / 'pi-computations.html').write_text('''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta http-equiv="refresh" content="0;url=''' + DESTINATION + '''"><title>Other examples · Computable Analysis</title><link rel="canonical" href="''' + DESTINATION + '''"></head><body><p>The π catalogue is in <a href="''' + DESTINATION + '''">Chapter 1, Other examples</a>.</p></body></html>''')

    for name, text in worked.items():
        assert str(parse((site / name).read_text()).article) == text, name
    for path, expected in protected.items():
        assert sha(site / path) == expected, path
    report.update(documentationRevision=args.revision, homeTeaser=False,
        chapterOneCatalogue=True, formulaCount=9, catalogueSubsection=OTHER,
        catalogueImmediatelyAfterHeading=True, cosineQuadratureInCatalogue=False,
        cosineQuadratureLocation='cosine.html#numerical-comparison',
        oldCatalogueRedirect=DESTINATION, chapterOneMathematicsUnchanged=True,
        otherExamplesHeading='1.2.2 Other examples', workedComparisonContentUnchanged=True)
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    audit = dict(documentationRevision=args.revision, proofSourceCommit=report['proofSourceCommit'],
        catalogueSubsection=OTHER, formulaCount=9, homeTeaser=False,
        cosineQuadratureInCatalogue=False, workedComparisonContentUnchanged=True,
        originalChapterMathematicsPreserved=True, proofDataAndCosineAnimationUnchanged=True,
        protectedArtifacts=protected, newLeanProofsClaimed=False)
    (site / 'reading/catalogue-placement.json').write_text(json.dumps(audit, indent=2) + '\n')
    print('PASS: nine pi examples immediately under Other examples; no home cosine teaser; worked comparisons and proofs unchanged')


if __name__ == '__main__':
    main()
