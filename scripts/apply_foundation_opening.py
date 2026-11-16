#!/usr/bin/env python3
"""Lead the book with the concise chapter while retaining the checked reference."""

import re
import sys
from pathlib import Path

from apply_foundation_preface import apply as apply_preface
from render_foundation_textbook import SOURCE, markdown

REFERENCE = 'id="chapter-one-reference"'
DEEP_LINK = """<script id="chapter-one-open-reference">
(() => {
  const reference = document.getElementById('chapter-one-reference');
  function reveal() {
    const id = location.hash.slice(1);
    if (!id) return;
    const target = document.getElementById(decodeURIComponent(id));
    if (target && reference.contains(target)) {
      reference.open = true;
      target.scrollIntoView();
    }
  }
  addEventListener('hashchange', reveal);
  reveal();
})();
</script>"""


def chapter_body():
    chapter, _, body = (SOURCE / '01-numbers-and-functions.md').read_text().partition('\n\n')
    assert chapter.startswith('# Chapter 1.')
    content = markdown(body)
    # The main reader uses MathJax with explicit LaTeX delimiters.
    content = re.sub(r'\$\$(.*?)\$\$', lambda m: r'\[' + m[1] + r'\]', content, flags=re.S)
    content = re.sub(r'\$([^$\n]+)\$', lambda m: r'\(' + m[1] + r'\)', content)
    content = content.replace('<h2>', '<h2 id="square-root-opening">', 1)
    content = re.sub(r'(?P<attr>(?:href|src|srcset)=")(?P<url>assets/[^"]+|0[^/"]+\.html)"',
                     r'\g<attr>foundation-textbook/\g<url>"', content)
    return content


def apply(site):
    apply_preface(site)
    page = site / 'ch-foundations.html'
    original = page.read_text()
    heading = re.search(r'<h1 id="ch:foundations">[^<]+</h1>', original)
    assert heading, 'Chapter 1 heading missing'
    end = original.index('</div></article>', heading.end())
    old_body = original[heading.end():end]
    if REFERENCE in old_body:
        old_body = old_body.split('<div class="chapter-one-reference-body">', 1)[1]
        old_body = old_body.rsplit('</div></details>', 1)[0]

    new_body = (
        '\n<section aria-label="Chapter 1 reading text">\n' + chapter_body() + '\n</section>\n'
        f'<details {REFERENCE}><summary>Proofs and further details</summary>'
        '<div class="chapter-one-reference-body">' + old_body + '</div></details>\n'
    )
    updated = original[:heading.end()] + new_body + original[end:]
    if 'id="chapter-one-open-reference"' not in updated:
        updated = updated.replace('</body>', DEEP_LINK + '</body>', 1)
    assert old_body in updated
    assert updated.count('id="square-root-opening"') == 1
    assert updated.index('sqrt-secant-zoom.gif') < updated.index(REFERENCE)
    assert 'enclose(value, tolerance)' in (site / 'preface.html').read_text()
    for asset in ('sqrt-secant-zoom.gif', 'sqrt-secant-zoom.png'):
        assert (site / 'foundation-textbook/assets' / asset).is_file(), asset
    page.write_text(updated)
    print('Verified the concise Chapter 1 opens with the animation and retains its full proof reference.')


if __name__ == '__main__':
    apply(Path(sys.argv[1]))
