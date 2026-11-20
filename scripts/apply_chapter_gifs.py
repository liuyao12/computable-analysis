"""Collect chapter GIFs and place the revised square-root figure in the reader."""

import argparse
import csv
import hashlib
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
    pattern = r'(<figure id="fig:sqrt-secant-tangent">\s*<div class="centered">)<img [^>]+>'
    updated, count = re.subn(pattern,lambda m: m[1]+picture,original)
    assert count == 1, 'square-root chapter image missing'
    old = r'Secant–tangent rational enclosures for \(\sqrt2\).'
    assert updated.count(old) == 1
    chapter.write_text(updated.replace(old,caption))
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


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('site',type=Path)
    site = cli.parse_args().site
    collect(site)
    update_figure(site)
