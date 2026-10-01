#!/usr/bin/env python3
"""Apply maintained narrative additions after the checked reader editions.

Earlier edition reports remain immutable records of their audited stages.
This final report records each prose supersession and preserves the old proof
content, formulas, links, source inventories and numerical artifacts.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
from urllib.parse import urlsplit, unquote
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'book/pedagogy/pages.json'
MATH = re.compile(r'\\\[[\s\S]*?\\\]|\\\([\s\S]*?\\\)')
CSS = '.pedagogical-opening{margin:1em 0 1.6em}.pedagogical-context{font-size:.9em}.pedagogical-bridge{margin:.8em 0 1.2em}'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def narrative_pages(site):
    return {p.name for p in site.glob('*.html')
        if (lambda d: d.select_one('main') and d.select_one('main').find('h1'))(
            BeautifulSoup(p.read_text(), 'html.parser'))}


def check_links(site, fragment):
    doc = BeautifulSoup(fragment, 'html.parser')
    assert not doc.select('script,style,h1,h2,h3,pre,code,sup,sub')
    for link in doc.select('a[href]'):
        href = link['href']; url = urlsplit(href)
        assert not url.scheme and url.path and not url.path.startswith('/'), href
        target = site / url.path
        assert target.is_file(), href
        if url.fragment:
            assert BeautifulSoup(target.read_text(), 'html.parser').find(id=unquote(url.fragment)), href


def existing_content(source):
    doc = BeautifulSoup(source, 'html.parser')
    for node in doc.select('[data-pedagogy],#pedagogy-style'): node.decompose()
    # These are all original mathematical expressions, code and interactive
    # sources. Their exact sequence is retained; only a prose note may move.
    return dict(math=MATH.findall(str(doc)),
        code=[str(x) for x in doc.select('pre,code')],
        mathml=[str(x) for x in doc.select('math')],
        theorem=[str(x) for x in doc.select('[class*="thmwrapper"],.showcase-statement')],
        scripts=[str(x) for x in doc.select('script')],
        links=Counter(x['href'] for x in doc.select('a[href]')),
        ids=Counter(x['id'] for x in doc.select('[id]')))


def install(site, revision):
    rows = json.loads(SOURCE.read_text())
    assert len({r['page'] for r in rows}) == len(rows)
    assert {r['page'] for r in rows} == narrative_pages(site), 'Review new narrative pages before publication'
    assert not (site/'reading/pedagogy-edition.json').exists(), 'Build from the checked pre-pedagogy edition'
    before = {p.relative_to(site).as_posix(): digest(p.read_bytes())
        for p in site.rglob('*') if p.is_file()}
    reviewed = []
    changes = {}
    for row in rows:
        path = site/row['page']; old = path.read_text(); content = existing_content(old)
        doc = BeautifulSoup(old, 'html.parser'); h1 = doc.select_one('main h1')
        assert h1 and row['action'] in ['retain','strengthen']
        entry = dict(page=row['page'], action=row['action'], title=h1.get_text(' ',strip=True),
            reason=row.get('reason'), earlierMotivation=row.get('earlierMotivation'), sections=[])
        if row['action'] == 'retain':
            assert row['reason']; reviewed.append(entry); continue
        body = row['opening']
        check_links(site, body)
        earlier = row.get('earlierMotivation')
        if earlier and f'href="{earlier}"' not in body:
            target = site / earlier.split('#')[0]
            title = BeautifulSoup(target.read_text(), 'html.parser').select_one('main h1').get_text(' ',strip=True)
            from html import escape
            body += f'<p class="pedagogical-context">Earlier context: <a href="{escape(earlier)}">{escape(title)}</a>.</p>'
        section = '<section class="pedagogical-opening" data-pedagogy="opening" id="why-this-page">'+body+'</section>'
        # Scope guidance remains accessible, after the chapter title and question.
        relocated = ''
        note = re.search(r'<section\b[^>]*\bid=["\']integral-enclosure-convention["\'][^>]*>[\s\S]*?</section>', old)
        if note and note.start() < old.index(str(h1)):
            relocated = note.group(); old = old[:note.start()]+old[note.end():]
        updated = old.replace(str(h1), str(h1)+section+relocated, 1)
        assert updated != old, row['page']
        for bridge in row['sectionBridges']:
            check_links(site, bridge['body'])
            headings = [h for h in doc.select('main h2,main h3') if bridge['heading'] in h.get_text()]
            assert len(headings) == 1, (row['page'],bridge['heading'])
            heading = str(headings[0]); anchor = headings[0]['id']
            assert heading in updated, (row['page'],anchor)
            addition = '<div class="pedagogical-bridge" data-pedagogy="bridge">'+bridge['body']+'</div>'
            updated = updated.replace(heading, heading+addition, 1)
            entry['sections'].append(anchor)
        updated = updated.replace('</head>', '<style id="pedagogy-style">'+CSS+'</style></head>', 1)
        assert existing_content(updated) == content, ('Existing mathematical content changed', row['page'])
        changed = BeautifulSoup(updated, 'html.parser')
        ids = [x['id'] for x in changed.select('[id]')]
        assert len(ids) == len(set(ids)), row['page']
        assert not changed.select_one('main h1').find_previous_sibling('section',id='integral-enclosure-convention')
        path.write_text(updated)
        changes[row['page']] = dict(before=before[row['page']], after=digest(path.read_bytes()),
            existingMathematicalContentPreserved=True, source='book/pedagogy/pages.json')
        reviewed.append(entry)
    protected = {name: h for name,h in before.items() if name not in changes}
    assert all(digest((site/name).read_bytes()) == h for name,h in protected.items())
    report = dict(schemaVersion=1, documentationRevision=revision, newLeanTheoremsClaimed=False,
        publicationStage='Final narrative layer after the existing checked reader editions',
        supersessionReason='User-requested pedagogical motivations and transitions; earlier artifact hashes describe their audited pre-narrative stages.',
        sourceSha256=digest(SOURCE.read_bytes()), reviewedPages=reviewed, changedArtifacts=changes,
        protectedArtifacts=protected, checks=dict(allNarrativePagesReviewed=True,
            existingMathematicalContentPreserved=True, proofReportsAndNumericalArtifactsPreserved=True,
            internalMotivationLinksChecked=True))
    (site/'reading/pedagogy-edition.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS:',len(rows),'pages reviewed;',len(changes),'motivated openings;',
        sum(len(x['sections']) for x in reviewed),'section transitions; proof content preserved')


if __name__ == '__main__':
    p=argparse.ArgumentParser();p.add_argument('--site',type=Path,required=True);p.add_argument('--revision',required=True)
    a=p.parse_args();install(a.site.resolve(),a.revision)
