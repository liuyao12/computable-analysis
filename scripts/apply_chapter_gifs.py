"""Publish revised chapter figures and collect the reader's GIFs for review."""

import argparse
import csv
import hashlib
import json
import re
import shutil
import zipfile
from html import escape
from itertools import groupby
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CATALOG = ROOT/'book/chapter-gifs'


def collect(site):
    gallery = site/'chapter-gifs'
    folder = gallery/'gifs'
    folder.mkdir(parents=True, exist_ok=True)
    with (CATALOG/'figures.tsv').open() as file:
        rows = list(csv.DictReader(file, delimiter='\t'))
    options, links, digests = [], [], set()
    for chapter, entries in groupby(rows, lambda r: r['Chapter or collection']):
        options.append(f'<optgroup label="{escape(chapter)}">')
        for row in entries:
            name, source = row['File name'], row['Source']
            path = site/source[5:] if source.startswith('site:') else ROOT/source
            data = path.read_bytes()
            digest = hashlib.sha256(data).digest()
            assert data.startswith((b'GIF87a',b'GIF89a')) and digest not in digests, name
            digests.add(digest)
            (folder/name).write_bytes(data)
            title = escape(row['Title'])
            options.append(f'<option value="{Path(name).stem}">{title}</option>')
            links.append(f'<li><a href="gifs/{name}">{title}</a></li>')
        options.append('</optgroup>')
    html = (CATALOG/'review.html').read_text().replace('<!-- options -->','\n'.join(options))
    html = html.replace('<!-- links -->','\n'.join(links))
    (gallery/'index.html').write_text(html)
    with zipfile.ZipFile(gallery/'chapter-gifs.zip','w',zipfile.ZIP_DEFLATED) as archive:
        archive.writestr('index.html', re.sub(r'<a id="archive".*?</a>', '', html))
        for row in rows:
            name = row['File name']
            archive.write(folder/name, 'gifs/'+name)
    print(f"Extracted {len(rows)} distinct GIFs.")


def update_figure(site):
    assets = site/'foundation-preface'
    assets.mkdir(exist_ok=True)
    for suffix in ('gif','png'):
        name = 'sqrt-secant-zoom.'+suffix
        shutil.copyfile(ROOT/'textbook/assets'/name, assets/name)
    source = (ROOT/'book/foundation-preface/content.html').read_text()
    figure = re.search(r'<figure id="fig:sqrt-secant-tangent">.*?</figure>',source,re.S)[0]
    picture = re.search(r'<picture>.*?</picture>',figure,re.S)[0]
    caption = re.search(r'<figcaption>(.*?)</figcaption>',figure,re.S)[1]
    chapter = site/'ch-foundations.html'
    original = chapter.read_text()
    pattern = (r'(<figure id="fig:sqrt-secant-tangent">\s*<div class="centered">)'
               r'(?:<picture>.*?</picture>|<img [^>]+>)'
               r'(\s*<figcaption>.*?<span class="caption_text">).*?(</span>)')
    updated, count = re.subn(pattern,lambda m: m[1]+picture+m[2]+caption+m[3],original,flags=re.S)
    assert count == 1, 'square-root chapter figure missing'
    chapter.write_text(updated)
    preface = site/'preface.html'
    original = preface.read_text()
    if 'id="fig:sqrt-secant-tangent"' in original:
        updated, count = re.subn(r'<figure id="fig:sqrt-secant-tangent">.*?</figure>',
                                 lambda _: figure,original,flags=re.S)
        assert count == 1
    else:
        # In the longer preface the worked first update immediately precedes
        # the exercise on nesting. Keep the full pseudocode and tables in place.
        anchor = '<p>Readers who wish can verify that the intervals remain nested'
        assert original.count(anchor) == 1
        updated = original.replace(anchor,figure+'\n'+anchor)
    preface.write_text(updated)


def update_circle_figure(site):
    page = site/'ch-circle-sphere.html'
    image = 'images/img-0002.gif'
    poster = 'images/rational-circle-subdivision.png'
    assets = ROOT/'blueprint/src/assets'
    shutil.copyfile(assets/'rational-circle-subdivision.gif', site/image)
    shutil.copyfile(assets/'rational-circle-subdivision.png', site/poster)
    alt = ('Rays grow together from the left endpoint through dots on the vertical radius to the arc. '
           'Green triangles join the inscribed polygon and yellow triangles are cut from the outer polygon. '
           'As the areas merge, the dashed boundaries become thin solid lines. The rays fade and the equally spaced dots remain. '
           'Below, a and b show the lower and upper quarter-disk areas in decimal form.')
    picture = (f'<picture><source media="(prefers-reduced-motion: reduce)" srcset="{poster}">'
               f'<img src="{image}" alt="{alt}" style="width:360pt;max-width:100%;height:auto"/></picture>')
    pattern = (r'(<figure id="fig:rational-parameter-line">\s*<div class="centered">)'
               r'(?:<picture>.*?</picture>|<img [^>]+>)')
    updated, count = re.subn(pattern,lambda m: m[1]+picture,page.read_text(),flags=re.S)
    assert count == 1, 'circle subdivision figure missing'
    page.write_text(updated)


def update_arctan_figure(site):
    animations = site/'reading/animations'
    assets = ROOT/'blueprint/src/assets'
    manifest_file = animations/'manifest.json'
    manifest = json.loads(manifest_file.read_text())
    edition_file = site/'reading/analysis-edition.json'
    edition = json.loads(edition_file.read_text())
    for suffix, key in (('gif', 'gifSha256'), ('png', 'posterSha256')):
        name = 'arctan.'+suffix
        data = (assets/('arctan-sector.'+suffix)).read_bytes()
        (animations/name).write_bytes(data)
        digest = hashlib.sha256(data).hexdigest()
        manifest['files'][name] = digest
        edition['circleAnimation'][key] = digest
    manifest_file.write_text(json.dumps(manifest, indent=2, ensure_ascii=False)+'\n')
    edition_file.write_text(json.dumps(edition, indent=2, ensure_ascii=False)+'\n')

    page = site/'cosine-primitive.html'
    alt = ('A thick red segment runs from the center to the mark t on the vertical radius. '
           'The corresponding shaded sector is labeled arctan(t) outside the circle. '
           'New rays project the subdivisions onto the arc as green chords and yellow tangents refine its area bounds.')
    caption = (r'Project the equally spaced marks up to \(t\) onto the arc from the left end of the diameter. '
               r'The shaded sector has area \(A(t)=\arctan(t)\).')
    pattern = r'(<figure [^>]*data-animation="arctan"[^>]*>)<img [^>]*>\s*<figcaption>.*?</figcaption>'
    updated, count = re.subn(
        pattern, lambda m: m[1]+f'<img src="reading/animations/arctan.gif" alt="{alt}" '
        f'width="798" height="421"/><figcaption>{caption}</figcaption>', page.read_text(), flags=re.S)
    assert count == 1, 'arctangent sector figure missing'
    page.write_text(updated)


def update_integral_picture(site, name, alt, caption=None):
    folder = 'reading/integral-grid'
    for suffix in ('gif', 'png'):
        filename = f'{name}.{suffix}'
        shutil.copyfile(ROOT/'blueprint/src/assets'/filename, site/folder/filename)
    page = site/'ch-integrals.html'
    image = f'{folder}/{name}.gif'
    picture = (f'<picture><source media="(prefers-reduced-motion: reduce)" srcset="{folder}/{name}.png">'
               f'<img src="{image}" alt="{alt}" style="width:360pt;max-width:100%;height:auto"/></picture>')
    pattern = rf'(?:<picture>\s*<source\b[^>]*>\s*)?<img\b[^>]*\bsrc="{re.escape(image)}"[^>]*>(?:\s*</picture>)?'
    if caption is not None:
        pattern += r'(\s*<figcaption>(?:(?!</figcaption>).)*?<span class="caption_text">)[^<]*(</span>)'
    updated, count = re.subn(pattern, lambda m: picture if caption is None else
                             picture+m[1]+escape(caption)+m[2], page.read_text(), flags=re.S)
    assert count == 1, f'{name} figure missing'
    page.write_text(updated)


def update_integral_figure(site):
    update_integral_picture(site, 'arctan-rectangle-enclosure',
                            'Dashed lines rise from new midpoints to the curve. Green rectangles join the lower sum '
                            'and gold rectangles drop out of the upper sum. The two bounds appear below the graph.')
    chapter = (ROOT/'blueprint/src/03-integrals.tex').read_text()
    caption = re.search(r'\\intervalSineIntegralStageAnimation\s*\\caption\{(.*?)\}\s*\\end\{figure\}', chapter, re.S)[1]
    update_integral_picture(site, 'interval-sine-integral-stage',
                            'In a unit square, dashed guides rise to capped intervals around the sine curve. '
                            'The upper cap sends a gold edge left and the lower cap sends a green edge right. '
                            'Earlier bars shrink as the mesh is halved.', ' '.join(caption.split()))


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('site',type=Path)
    site = cli.parse_args().site
    update_circle_figure(site)
    update_arctan_figure(site)
    update_integral_figure(site)
    update_figure(site)
    collect(site)
