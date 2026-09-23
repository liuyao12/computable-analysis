#!/usr/bin/env python3
"""Verify proof scope, links, LaTeX rendering, and mobile layout."""
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
    parser = argparse.ArgumentParser()
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    report = json.loads((args.site / 'reading/rational-primitives-edition.json').read_text())
    assert report['allPreviousContentPreserved']
    assert report['formalPartialFractionIntegrationProved']
    assert report['domainPreservingRationalizationProved']
    assert report['analyticPolynomialPrimitivesProved']
    assert report['analyticSimplePoleLocalPrimitivesProved']
    assert report['automaticRationalLinearPartialFractionsProved']
    assert report['automaticRationalQuadraticPartialFractionsProved']
    assert report['factorizationToFormalPrimitiveProved']
    assert report['computableRealCoefficientFormalPrimitivesProved']
    assert report['irrationalCoefficientRegressionProved']
    assert report['computableLogarithmArctangentDerivativesProved']
    assert report['computableQuadraticBasePrimitivesProved']
    assert report['trigonometricElementaryFormulaTheoremProved']
    assert report['finitePrimitiveChangeOfVariablesProved']
    assert not report['trigonometricIntervalPrimitiveTheoremProved']
    assert report['analyticRepeatedLinearPolePrimitivesProved']
    assert report['analyticRationallySplitLocalPrimitivesProved']
    assert not report['generalAnalyticTheoremProved'] and not report['mathlibDependency']
    for file, key in [(report['page'], 'pageSha256'),
                      ('reading/rational-primitives-audit.log', 'auditSha256')]:
        assert hashlib.sha256((args.site / file).read_bytes()).hexdigest() == report[key]
    soup = BeautifulSoup((args.site / report['page']).read_text(), 'html.parser')
    assert 'The full rational-function primitive theorem remains open.' in soup.get_text()
    assert len(soup.select('#status li')) == 4
    assert not soup.select('sup, sub')
    for link in soup.select('a[href]'):
        href = link['href']
        if href.startswith('https://github.com/'):
            assert report['proofSourceCommit'] in href
        elif href.startswith('#'):
            assert soup.select_one(href)
        elif not href.startswith('https:'):
            assert (args.site / href.split('#')[0]).is_file(), href
    for name in report['changedReaderPages']:
        assert 'href="rational-primitives.html"' in (args.site / name).read_text()
    args.report.mkdir(parents=True, exist_ok=True)

    class QuietHandler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *_):
            pass

    server = http.server.ThreadingHTTPServer(('127.0.0.1', 0),
        partial(QuietHandler, directory=str(args.site.resolve())))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    try:
        with sync_playwright() as pw:
            options = dict(headless=True)
            executable = shutil.which('google-chrome') or shutil.which('chromium')
            mac_chrome = Path('/Applications/Google Chrome.app/Contents/MacOS/Google Chrome')
            if executable:
                options['executable_path'] = executable
            elif mac_chrome.exists():
                options['executable_path'] = str(mac_chrome)
            browser = pw.chromium.launch(**options)
            for width, height in [(1440, 1000), (390, 844)]:
                page = browser.new_page(viewport=dict(width=width, height=height))
                errors = []
                page.on('pageerror', lambda e: errors.append(str(e)))
                page.goto(f'http://127.0.0.1:{server.server_port}/{report["page"]}',
                          wait_until='networkidle')
                page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',
                                       timeout=60000)
                page.evaluate('() => MathJax.startup.promise')
                assert page.locator('mjx-container').count() >= 20
                assert page.locator('mjx-merror').count() == 0
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth'), width
                assert not errors, errors
                page.screenshot(path=str(args.report / f'rational-primitives-{width}.png'), full_page=True)
                page.locator('nav a[href="ch-integrals.html"]').click()
                page.wait_for_url('**/ch-integrals.html')
                page.locator('a[href="rational-primitives.html"]').click()
                page.wait_for_url('**/rational-primitives.html')
                page.close()
            browser.close()
    finally:
        server.shutdown()
    print('PASS: rational primitives scope, hashes, links, LaTeX, and desktop/mobile layout')


if __name__ == '__main__':
    main()
