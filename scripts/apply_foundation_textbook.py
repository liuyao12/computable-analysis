#!/usr/bin/env python3
"""Overlay the textbook onto a complete existing Pages artifact."""
import argparse
from pathlib import Path

from render_foundation_textbook import SOURCE, generated_files, write_files

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('site', type=Path)
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
print('Added the textbook and its home-page link; existing Pages files preserved.')
