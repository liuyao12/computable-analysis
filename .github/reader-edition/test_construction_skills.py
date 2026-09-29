#!/usr/bin/env python3
"""Check skill provenance, navigation, links, and mathematical rendering."""
import argparse
import hashlib
import json
import shutil
import threading
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit
from bs4 import BeautifulSoup
from construction_skills import MATH, OVERVIEW, ROOT, catalogue


def check(site):
    rows = catalogue()
    report = json.loads((site / 'reading/construction-skills.json').read_text())
    assert not report['newLeanTheoremsClaimed']
    assert report['skills'] == rows
    for name, digest in report['artifacts'].items():
        assert hashlib.sha256((site / name).read_bytes()).hexdigest() == digest, name
    all_rows = rows + catalogue(examples=True)
    assert report['constructionExamples'] == catalogue(examples=True)
    pages = [OVERVIEW] + [r['page'] for r in all_rows]
    for name in report['navigationPages']:
        path = site / name
        doc = BeautifulSoup(path.read_text(), 'html.parser')
        nav = doc.select_one('#book-nav')
        assert nav.select_one('.nav-label').get_text() == 'The book', name
        chapters = nav.select_one('.later-chapters')
        assert 'construction-skill-label' in chapters.find_next_sibling().get('class', []), name
        links = nav.select('.construction-skill-navigation')
        assert len(links) == len(rows), name
        for link, target in zip(links, [r['page'] for r in rows]):
            assert not link.find_parent('details'), (name, 'collapsed skill navigation')
            assert (path.parent / link['href']).resolve() == (site / target).resolve()
            assert (site / target).is_file()
    for name in pages:
        doc = BeautifulSoup((site / name).read_text(), 'html.parser')
        current = doc.select('#book-nav a[aria-current="page"]')
        active = 'skill-real-integrals.html' if name in [r['page'] for r in catalogue(examples=True)] else name
        assert len(current) == 1 and current[0]['href'] == active, name
        ids = [n['id'] for n in doc.select('[id]')]
        assert len(ids) == len(set(ids)), name
        assert not doc.select('article sup, article sub'), name
        for link in doc.select('a[href]'):
            u = urlsplit(link['href'])
            if u.scheme:
                continue
            target = site / (u.path or name)
            assert target.is_file() or (target / 'index.html').is_file(), (name, link['href'])
            if u.fragment and target.suffix == '.html':
                assert BeautifulSoup(target.read_text(), 'html.parser').find(id=u.fragment), (name, link['href'])
    for row in all_rows:
        source = ROOT / row['source']
        download = site / 'reading' / row['source']
        assert download.read_bytes() == source.read_bytes()
        assert report['sourceHashes'][str(source.relative_to(ROOT))] == hashlib.sha256(source.read_bytes()).hexdigest()
        doc = BeautifulSoup((site / row['page']).read_text(), 'html.parser')
        assert MATH.findall(source.read_text()) == MATH.findall(doc.article.get_text()), row['source']
        assert doc.select_one('.construction-skill-proof summary')
        assert doc.select_one('.construction-skill-links a[download]')
    print('PASS: three skills and their examples, exact downloads, preserved TeX, local links, and visible navigation on', len(report['navigationPages']), 'pages')


def browser_check(site, output):
    from playwright.sync_api import sync_playwright
    class Quiet(SimpleHTTPRequestHandler):
        def log_message(self, *args):
            pass
    server = ThreadingHTTPServer(('127.0.0.1', 0), partial(Quiet, directory=str(site)))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    errors = []
    output.mkdir(parents=True, exist_ok=True)
    try:
        with sync_playwright() as pw:
            opts = dict(headless=True, args=['--no-sandbox'])
            executable = shutil.which('google-chrome') or shutil.which('chromium')
            if executable:
                opts['executable_path'] = executable
            browser = pw.chromium.launch(**opts)
            for width in [1440, 390, 320]:
                page = browser.new_page(viewport={'width': width, 'height': 1000})
                page.on('pageerror', lambda e: errors.append(str(e)))
                for name in [OVERVIEW] + [r['page'] for r in catalogue() + catalogue(examples=True)]:
                    page.goto(f'http://127.0.0.1:{server.server_port}/{name}', wait_until='networkidle')
                    page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise')
                    page.evaluate('() => MathJax.startup.promise')
                    assert page.locator('mjx-merror,[data-mjx-error]').count() == 0, (name, width)
                    assert page.locator('article mjx-container').count() >= 1, name
                    assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2'), (name, width)
                    if width < 720:
                        page.locator('#menu-button').click()
                    for link in page.locator('#book-nav .construction-skill-navigation').all():
                        assert link.is_visible(), (name, width)
                    if width < 720:
                        page.locator('#menu-button').click()
                    if name != OVERVIEW:
                        page.locator('.construction-skill-proof summary').click()
                        assert page.locator('.construction-skill-proof[open]').count() == 1
                        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2'), (name, width, 'proof sources')
                    page.screenshot(path=str(output / f'{Path(name).stem}-{width}.png'), full_page=True)
                page.goto(f'http://127.0.0.1:{server.server_port}/{OVERVIEW}', wait_until='networkidle')
                if width < 720:
                    page.locator('#menu-button').click()
                page.locator('#book-nav a[href="skill-real-integrals.html"]').click()
                assert page.locator('#book-nav a[aria-current="page"]').get_attribute('href') == 'skill-real-integrals.html'
                page.close()
            browser.close()
        assert not errors, errors
    finally:
        server.shutdown()
    print('PASS: desktop/mobile navigation, active state, formulas, and expandable proof sources')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--report', type=Path, default=Path('reader-edition-tests/construction-skills'))
    parser.add_argument('--static-only', action='store_true')
    args = parser.parse_args()
    check(args.site.resolve())
    if not args.static_only:
        browser_check(args.site.resolve(), args.report)
