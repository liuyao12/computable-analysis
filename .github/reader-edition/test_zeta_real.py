#!/usr/bin/env python3
"""Check the published zeta proof boundary, links, hashes and responsive layout."""
import argparse
import hashlib
import http.server
import json
import shutil
import threading
from functools import partial
from pathlib import Path
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--site', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    a = p.parse_args()
    report = json.loads((a.site / 'reading/zeta-real-edition.json').read_text())
    assert report['realInputsAboveOne'] and report['allPreviousContentPreserved']
    assert not report['mathlibDependency'] and not report['logExpBridgeProved']
    assert not report['analyticContinuationProved']
    assert len(report['auditedDeclarations']) == 33
    assert hashlib.sha256((a.site / report['page']).read_bytes()).hexdigest() == report['pageSha256']
    assert hashlib.sha256((a.site / 'reading/zeta-real-axioms.log').read_bytes()).hexdigest() == report['auditSha256']
    soup = BeautifulSoup((a.site / report['page']).read_text(), 'html.parser')
    assert 'not an analytic derivative theorem' in soup.select_one('#boundary').get_text()
    assert len(soup.select('#checked tbody tr')) == 5
    assert not soup.select('sup, sub')
    assert not any(c in soup.get_text() for c in 'ζπΣ₀₁₂ₖᵏ⁻≤≥ε')
    assert report['baselProved'] and report['primesFromPiSquaredIrrationality']
    assert not report['piSquaredIrrationalityProved']
    assert 'Basel is proved' in soup.select_one('#basel').get_text()
    assert 'not yet proved in the project' in soup.select_one('#euler').get_text()
    for link in soup.select('a[href]'):
        href = link['href']
        if href.startswith('https://github.com/'):
            assert '/blob/' + report['proofSourceCommit'] + '/' in href
        elif not href.startswith(('#', 'https:')):
            assert (a.site / href.split('#')[0]).is_file(), href
    for name in report['changedReaderPages']:
        assert 'href="zeta-real.html"' in (a.site / name).read_text()
    a.report.mkdir(parents=True, exist_ok=True)
    class QuietHandler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *_): pass
    server = http.server.ThreadingHTTPServer(('127.0.0.1', 0), partial(QuietHandler, directory=str(a.site.resolve())))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    try:
        with sync_playwright() as pw:
            options = dict(headless=True)
            executable = shutil.which('google-chrome') or shutil.which('chromium') or shutil.which('chromium-browser')
            if executable:
                options['executable_path'] = executable
            browser = pw.chromium.launch(**options)
            for width, height in [(1440, 1000), (390, 844)]:
                page = browser.new_page(viewport=dict(width=width, height=height))
                errors = []
                page.on('pageerror', lambda e: errors.append(str(e)))
                page.goto(f'http://127.0.0.1:{server.server_port}/zeta-real.html', wait_until='networkidle')
                page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise', timeout=60000)
                page.evaluate('() => MathJax.startup.promise')
                assert page.locator('mjx-container').count() >= 35
                assert page.locator('mjx-merror').count() == 0
                assert page.locator('#basel mjx-container[display="true"]').evaluate_all(
                    '(els) => els.every(e => e.querySelector("mjx-math").getBoundingClientRect().width <= e.clientWidth)')
                assert page.locator('#euler mjx-container[display="true"]').count() == 1
                assert page.title().startswith('Zeta for real exponents')
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth'), width
                assert not errors
                page.screenshot(path=str(a.report / f'zeta-real-{width}.png'), full_page=True)
                page.locator('nav a[href="ch-transforms-zeta.html"]').click()
                page.wait_for_url('**/ch-transforms-zeta.html')
                page.locator('a[href="zeta-real.html"]').click()
                page.wait_for_url('**/zeta-real.html')
                page.close()
            browser.close()
    finally:
        server.shutdown()
    print('PASS: zeta reader hashes, rendered LaTeX, Euler boundary, links, and desktop/mobile layout')


if __name__ == '__main__':
    main()
