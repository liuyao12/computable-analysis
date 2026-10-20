#!/usr/bin/env python3
"""Add the identification strategy and scoped audit to the established reader."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MATH = re.compile(r'\\\(.*?\\\)|\\\[.*?\\\]', re.S)
IDS = re.compile(r'\bid=[\"\']([^\"\']+)[\"\']')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def apply(site):
    before = {str(p.relative_to(site)): p.read_bytes() for p in site.rglob('*') if p.is_file()}
    changed = set()
    content = (ROOT / 'book/identification-audit/content.html').read_text()
    template = (site / 'preface.html').read_text()
    page = re.sub(r'<title>.*?</title>', '<title>Identification strategy and audit · Computable Analysis</title>', template, count=1)
    page = re.sub(r'<meta name="description" content="[^"]*">', '<meta name="description" content="Valid computations need mathematical identification: the strategy, square-root example and first source audit.">', page, count=1)
    page = page.replace('aria-current="page"', '').replace('class="current"', 'class=""')
    page, count = re.subn(r'<article>.*?</article>', lambda _: '<article><div class="main-text">' + content + '</div></article>', page, count=1, flags=re.S)
    assert count == 1
    page = re.sub(r'<aside class="on-this-page">.*?</aside>', '<aside class="on-this-page"><span>On this page</span>' + ''.join('<a href="#' + key + '">' + title + '</a>' for key, title in re.findall(r'<h2 id="([^"]+)">([^<]+)</h2>', content)) + '</aside>', page, count=1, flags=re.S)
    page = page.replace('<div class="chapter-kicker">PREFACE</div>', '<div class="chapter-kicker">THE STRATEGY</div>')
    page = re.sub(r'<footer class="chapter-footer">.*?</footer>', '<footer class="chapter-footer"><span>Valid computations; justified mathematical identities</span><a href="programme.html">Purpose and boundary</a></footer>', page, count=1, flags=re.S)
    page = page.replace('</style>', '.audit-table{overflow-x:auto}.audit-table table{width:100%;border-collapse:collapse;font-size:.9rem}.audit-table th,.audit-table td{padding:.8rem .6rem;border-bottom:1px solid #d8ded9;text-align:left;vertical-align:top}.audit-table td:first-child{width:30%;font-weight:600}</style>')
    assert '<sup' not in content and '<sub' not in content
    assert content.count('\\(') == content.count('\\)')
    assert content.count('\\[') == content.count('\\]')
    (site / 'identification-audit.html').write_text(page)
    assets = site / 'identification-audit'
    assets.mkdir(exist_ok=True)
    for rel, name in [
        ('docs/IDENTIFICATION_AUDIT.md', 'audit.md'),
        ('docs/IDENTIFICATION_INVENTORY.json', 'inventory.json'),
        ('skills/computable-analysis-formalization/references/identification-laws.md', 'strategy.md'),
        ('skills/computable-analysis-formalization/SKILL.md', 'master-skill.md'),
    ]:
        (assets / name).write_bytes((ROOT / rel).read_bytes())
    chapter = site / 'ch-foundations.html'
    original = chapter.read_text()
    fragment = (ROOT / 'book/identification-audit/chapter-one.html').read_text()
    assert 'id="square-root-identification"' not in original
    anchor = '<h2 id="square-root-lines">'
    assert anchor in original
    edited = original.replace(anchor, fragment + anchor, 1)
    chapter.write_text(edited)
    changed.add('ch-foundations.html')
    for name in ['programme.html', 'construction-skills.html']:
        target = site / name
        if not target.exists():
            continue
        text = target.read_text()
        addition = '<section id="identification-strategy-intro"><h2>Validate the computation; identify the object</h2><p>Nested, shrinking intervals establish a represented value. Separate mathematical laws justify its name. Read the <a href="identification-audit.html">strategy and first identification audit</a>, including the reusable square-root law and the remaining review work.</p></section>'
        text, count = re.subn(r'(<h1\b[^>]*>.*?</h1>)', lambda m: m[1] + addition, text, count=1, flags=re.S)
        assert count == 1, name
        target.write_text(text)
        changed.add(name)
    # Every existing formula and anchor remains. New formulas may be added.
    for name in changed:
        old = before[name].decode()
        new = (site / name).read_text()
        assert set(IDS.findall(old)) <= set(IDS.findall(new)), name
        cursor = iter(MATH.findall(new))
        assert all(any(candidate == formula for candidate in cursor) for formula in MATH.findall(old)), name
    for name, data in before.items():
        if name not in changed:
            assert (site / name).read_bytes() == data, name
    report = {'changedExistingPages': sorted(changed), 'preservedFiles': len(before) - len(changed),
              'preservedExistingMath': True, 'preservedExistingAnchors': True,
              'contentSha256': digest(content.encode()), 'newLeanTheoremsClaimed': False,
              'auditInputRevision': 'c38cfc25d224a98fdd36f2bf018f3cf51da7c8da'}
    (assets / 'publication.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: published identification strategy; preserved', report['preservedFiles'], 'existing files and all existing mathematics and anchors.')


if __name__ == '__main__':
    apply(Path(sys.argv[1]))
