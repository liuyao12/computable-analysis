#!/usr/bin/env python3
"""Check final placement after the baseline edition passes its own tests."""
from __future__ import annotations
import argparse
import functools
import hashlib
import http.server
import json
import shutil
import threading
from pathlib import Path
from bs4 import BeautifulSoup


def check(site: Path):
    report = json.loads((site / 'reading/catalogue-placement.json').read_text())
    edition = json.loads((site / 'reading/analysis-edition.json').read_text())
    assert edition['documentationRevision'] == report['documentationRevision']
    assert edition['formulaCount'] == 9 and not edition['homeTeaser']
    assert not edition['cosineQuadratureInCatalogue']
    chapter = BeautifulSoup((site / 'ch-foundations.html').read_text(), 'html.parser')
    other = chapter.find(id='rem:sources-of-raw-reals')
    gallery = chapter.select_one('#pi-computations')
    assert other.text == '1.2.2 Other examples'
    assert other.find_next_sibling() == gallery
    assert gallery.find_previous(['h1', 'h2']) == other
    assert len(gallery.select('.pi-formula-card')) == 9
    assert not gallery.select('#pi-cosine, [data-animation="cosine"]')
    assert '\\cos(' not in gallery.get_text() and 'Cosine quadrature' not in gallery.get_text()
    assert chapter.find(id='rem:algebraic-numbers-sqrt-two').find_next(id='rem:sources-of-raw-reals') == other
    for link in gallery.select('a[href^="#"]'):
        assert chapter.find(id=link['href'][1:]), link['href']
    home = BeautifulSoup((site / 'index.html').read_text(), 'html.parser')
    assert not home.select('.pi-teaser, .pi-formula-card')
    assert home.select_one('.chapter-one-examples-link a')['href'] == 'ch-foundations.html#pi-computations'
    assert home.select_one('article h1 em').text == 'Analysis'
    assert home.select_one('.book-subtitle').text == 'An alternative foundation to Calculus'
    old = (site / 'pi-computations.html').read_text()
    assert '0;url=ch-foundations.html#pi-computations' in old
    worked = BeautifulSoup((site / 'cosine.html').read_text(), 'html.parser')
    assert worked.select_one('[data-animation="cosine"]')
    assert len(worked.select('.numerical-bounds tbody tr')) >= 4
    for path, expected in report['protectedArtifacts'].items():
        assert hashlib.sha256((site / path).read_bytes()).hexdigest() == expected, path
    return report


def browser_test(site: Path, out: Path):
    from playwright.sync_api import sync_playwright
    out.mkdir(parents=True, exist_ok=True)
    server = http.server.ThreadingHTTPServer(('127.0.0.1', 0),
        functools.partial(http.server.SimpleHTTPRequestHandler, directory=str(site)))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    base = f'http://127.0.0.1:{server.server_port}/'
    errors = []
    with sync_playwright() as p:
        exe = next((shutil.which(n) for n in ['google-chrome', 'chromium', 'chromium-browser'] if shutil.which(n)), None)
        opts = dict(headless=True, args=['--no-sandbox'])
        if exe:
            opts['executable_path'] = exe
        browser = p.chromium.launch(**opts)
        page = browser.new_page(viewport=dict(width=1500, height=1050))
        page.on('pageerror', lambda e: errors.append(str(e)))
        page.goto(base + 'index.html', wait_until='domcontentloaded')
        assert not page.locator('.pi-teaser').count()
        page.locator('.chapter-one-examples-link a').click()
        page.wait_for_url('**/ch-foundations.html#pi-computations')
        page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise', timeout=60000)
        page.evaluate('() => MathJax.startup.promise')
        assert page.locator('#pi-computations .pi-formula-card').count() == 9
        assert not page.locator('mjx-merror,[data-mjx-error]').count()
        assert not page.locator('#pi-cosine').count()
        page.locator('[id="rem:sources-of-raw-reals"]').scroll_into_view_if_needed()
        page.screenshot(path=str(out / 'other-examples-desktop.png'), full_page=False)
        page.set_viewport_size(dict(width=390, height=850))
        page.locator('[id="rem:sources-of-raw-reals"]').scroll_into_view_if_needed()
        assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 2')
        page.screenshot(path=str(out / 'other-examples-mobile.png'), full_page=False)
        page.goto(base + 'pi-computations.html', wait_until='domcontentloaded')
        page.wait_for_url('**/ch-foundations.html#pi-computations')
        page.goto(base + 'cosine.html', wait_until='domcontentloaded')
        assert page.locator('[data-animation="cosine"]').count() == 1
        assert not errors, errors
        browser.close()
    server.shutdown()
    (out / 'catalogue-placement-tests.json').write_text(json.dumps(dict(passed=True,
        correctSubsection=True, cosineReservedForWorkedComparison=True,
        oldBookmarkRedirect=True, mobile=True, mathematicalRendering=True, errors=errors), indent=2) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--site', type=Path, required=True)
    ap.add_argument('--report', type=Path, default=Path('reader-edition-tests'))
    ap.add_argument('--structural-only', action='store_true')
    args = ap.parse_args()
    check(args.site)
    if not args.structural_only:
        browser_test(args.site, args.report)
    print('PASS: catalogue ordering and exclusion, nine formulas, preserved mathematical data' +
          (' (structural checks only)' if args.structural_only else ', rendered desktop/mobile and legacy navigation'))


if __name__ == '__main__':
    main()
