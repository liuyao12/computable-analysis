#!/usr/bin/env python3
"""Overlay the textbook onto a complete existing Pages artifact."""
import argparse
import html
import json
import re
from pathlib import Path

from render_foundation_textbook import SOURCE, destination, generated_files, image_tag, write_files

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('site', type=Path)
parser.add_argument('--chapter-review', action='store_true')
args = parser.parse_args()
index = args.site / 'index.html'
if not index.is_file():
    raise SystemExit('A complete previous Pages site is required; refusing a textbook-only replacement.')
chapters = [SOURCE / 'README.md'] + sorted(p for p in SOURCE.glob('*.md') if p.name != 'README.md')
output = args.site / 'foundation-textbook'
write_files(output, generated_files(chapters))
text = index.read_text()
if 'id="foundation-textbook-link"' not in text:
    link = '<p id="foundation-textbook-link"><a href="foundation-textbook/">Read the living foundation textbook</a></p>'
    marker = '</main>' if '</main>' in text else '</body>'
    if marker not in text:
        raise SystemExit('Unrecognized previous home page; refusing to replace it.')
    index.write_text(text.replace(marker, link + '\n' + marker, 1))
print('Added the textbook and its home-page link.')

if args.chapter_review:
    reviews = json.loads((SOURCE.parent / 'book/pedagogy/pages.json').read_text())
    chapter_files = {destination(p.name) for p in chapters}
    existing = re.compile(r'<section id="current-foundation" class="pedagogical-opening">\n.*?</section>\n', re.S)
    for item in reviews:
        if 'foundationReview' not in item:
            continue
        review = item['foundationReview']
        target = args.site / item['page']
        original = target.read_text()
        links = []
        for label, filename in review['links'].items():
            if filename not in chapter_files:
                raise SystemExit(f'Unknown textbook chapter {filename}')
            links.append(f'<li><a href="foundation-textbook/{filename}">{html.escape(label)}</a></li>')
        figures = []
        for figure in review.get('figures', []):
            asset = f'assets/{figure["file"]}'
            if not (output / asset).is_file():
                raise SystemExit(f'Missing textbook figure {asset}')
            figures.append(
                f'<figure>{image_tag(asset, figure["alt"], "foundation-textbook/")}'
                f'<figcaption>{html.escape(figure["caption"])}</figcaption></figure>'
            )
        section = (
            '<section id="current-foundation" class="pedagogical-opening">\n'
            f'<h2>{html.escape(review["heading"])}</h2>\n'
            f'{review["body"]}\n{"".join(figures)}<ul>{"".join(links)}</ul>\n</section>\n'
        )
        if existing.search(original):
            revised = existing.sub(lambda _: section, original, count=1)
        else:
            heading = re.search(r'<h1\b[^>]*>.*?</h1>', original, re.S)
            if not heading:
                raise SystemExit(f'No chapter heading in {target}')
            end = heading.end()
            revised = original[:end] + '\n' + section + original[end:]
        target.write_text(revised)
    print('Updated the reviewed reader chapters.')
