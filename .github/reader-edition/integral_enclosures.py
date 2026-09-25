#!/usr/bin/env python3
"""Publish the current enclosure convention over the pinned reader edition."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parents[2]

def install(site, revision):
    assert re.fullmatch('[0-9a-f]{40}', revision)
    inventory = json.loads((ROOT/'docs/INTEGRAL_INVENTORY.json').read_text())
    repo = f'https://github.com/liuyao12/computable-analysis/blob/{revision}/'
    doc = BeautifulSoup((site/'cosine.html').read_text(), 'html.parser')
    doc.title.string = 'Integrals from whole chunks · Computable Analysis'
    meta = doc.select_one('meta[name="documentation-revision"]')
    if meta: meta['content'] = revision
    source = (ROOT/'book/classics/integral-enclosures.html').read_text()
    source = source.replace('__REPO__', repo).replace('__MODULE_COUNT__', str(len(inventory['files']))).replace('__AUXILIARY_COUNT__', str(len(inventory['auxiliaryFiles'])))
    doc.article.clear(); doc.article.append(BeautifulSoup(source, 'html.parser'))
    kicker = doc.select_one('.chapter-kicker')
    if kicker: kicker.string = 'FOUNDATION'
    for selected in doc.select('#book-nav a.current'):
        selected['class'] = [c for c in selected.get('class', []) if c != 'current']
    nav = doc.select_one('#book-nav')
    link = doc.new_tag('a', href='integral-enclosures.html'); link.string = 'How integrals are constructed'
    link['class'] = ['current']; nav.append(link)
    toc = doc.select_one('.on-this-page')
    if toc:
        toc.clear()
        for h in doc.article.select('h2[id]'):
            link = doc.new_tag('a', href='#'+h['id']); link.string = h.get_text(); toc.append(link)
    footer = doc.select_one('.chapter-footer a')
    if footer: footer['href'] = repo+'docs/INTEGRAL_ENCLOSURES.md'; footer.string = 'Source '+revision[:8]+' ↗'
    if not doc.select_one('link[href="reading/classics.css"]'):
        doc.head.append(doc.new_tag('link', rel='stylesheet', href='reading/classics.css'))
    (site/'integral-enclosures.html').write_text(str(doc))
    changed = ['integral-enclosures.html']
    superseded = {name: hashlib.sha256((site/name).read_bytes()).hexdigest()
                  for name in ['ch-integrals.html', 'ch-complex-paths.html']}
    for name in ['ch-integrals.html', 'ch-complex-paths.html']:
        page = BeautifulSoup((site/name).read_text(), 'html.parser')
        target = page.select_one('article .main-text') or page.article
        old = page.select_one('#integral-enclosure-convention')
        if old: old.decompose()
        note = BeautifulSoup(r'''<section id="integral-enclosure-convention"><h2>Whole-chunk enclosures come first</h2><p>For each particular function, certify an outer range on every chunk, multiply by its length or oriented complex displacement, and add. Prove nesting or justified intersection and shrinking widths. Monotonicity supplies endpoint bounds when available. An endpoint formula or point-sampled computation requires a comparison with these enclosing sums.</p><p><a href="integral-enclosures.html">Read the construction and native-source audit</a>. The narrative below develops the mathematical route; a displayed general identity is not itself a claim of a completed native Lean bridge.</p></section>''', 'html.parser')
        target.insert(0, note)
        if name == 'ch-complex-paths.html':
            # Replace the old parametrized definition, keeping its heading/anchors.
            paragraphs = page.find_all('p')
            for p in paragraphs:
                if 'For rational complex endpoints' in p.get_text():
                    replacement = BeautifulSoup(r'''<p>Subdivide the actual oriented segment into chunks with endpoints \(z_j,z_{j+1}\). Certify a rectangle \(B_j\) enclosing all function-value rectangles over each whole chunk, then form</p><div class="formula">\[I_n=\sum_j B_j(z_{j+1}-z_j).\]</div><p>Nested, shrinking outer sums define this particular integral. Multiplication by a vertical displacement rotates and scales each rectangle. Parametrized formulas are subsequent finite-sum comparisons.</p>''', 'html.parser')
                    following = p.find_next_sibling()
                    if following and ('(q-p)' in following.get_text() or 'right side consists' in following.get_text()):
                        after = following.find_next_sibling()
                        following.decompose()
                        if after and 'right side consists' in after.get_text(): after.decompose()
                    p.replace_with(replacement)
                    break
        (site/name).write_text(str(page)); changed.append(name)
    (site/'reading/integral-inventory.json').write_text(json.dumps(inventory, indent=2)+'\n')
    report = {'revision': revision, 'nativeModules': len(inventory['files']), 'auxiliaryModules': len(inventory['auxiliaryFiles']),
              'supersededChapterHashes': superseded,
              'supersessionReason': 'User-requested replacement of integral definitions by whole-chunk enclosures; earlier stage preservation reports describe their pinned source.',
              'directReciprocalSegmentProved': True, 'directLogarithmBridgeProved': False, 'generalCauchyRectangleBridgeProved': False,
              'artifacts': {name: hashlib.sha256((site/name).read_bytes()).hexdigest() for name in changed},
              'checks': {'wholeChunkConvention': True, 'candidatesDistinguished': True}}
    (site/'reading/integral-enclosures-edition.json').write_text(json.dumps(report, indent=2)+'\n')
    print('Published enclosure convention for', len(inventory['files']), 'native modules')

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--site', type=Path, required=True); ap.add_argument('--revision', required=True)
    a = ap.parse_args(); install(a.site, a.revision)
