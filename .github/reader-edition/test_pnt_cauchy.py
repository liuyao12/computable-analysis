#!/usr/bin/env python3
"""Check publication scope, source links, preservation and responsive reading."""
import argparse
import hashlib
import http.server
import json
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
    report = json.loads((a.site / 'reading/cauchy-arctan-publication.json').read_text())
    assert all(report['checks'].values())
    assert not report['nativeGeneralResidueTheorem'] and not report['nativeCauchyFormula']
    assert not report['mathlibDependency'] and not report['newPiDefinition']
    for name, sha in (report['protectedArtifactHashes'] | report['artifactHashes']).items():
        assert hashlib.sha256((a.site / name).read_bytes()).hexdigest() == sha, name
    soup = BeautifulSoup((a.site / 'cauchy-arctan.html').read_text(), 'html.parser')
    assert len(soup.select('#sources tbody tr')) == 6
    upstream = [el['href'] for el in soup.select('a[href]') if 'AlexKontorovich' in el['href']]
    assert len(upstream) == 7
    assert all('/blob/' + report['pntRevision'] + '/' in url for url in upstream)
    assert soup.select_one('#remaining') and soup.select_one('#native details')
    for el in soup.select('a[href]'):
        href = el['href']
        if not href.startswith(('https:', '#')):
            assert (a.site / href.split('#')[0]).is_file(), href
    a.report.mkdir(parents=True, exist_ok=True)
    class QuietHandler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *_): pass
    server = http.server.ThreadingHTTPServer(('127.0.0.1', 0), partial(QuietHandler, directory=str(a.site.resolve())))
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    url = f'http://127.0.0.1:{server.server_port}/cauchy-arctan.html'
    results = []
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            for width, height in [(1440, 1000), (390, 844)]:
                page = browser.new_page(viewport=dict(width=width, height=height), device_scale_factor=1)
                errors = []
                page.on('pageerror', lambda e: errors.append(str(e)))
                page.goto(url, wait_until='networkidle')
                assert page.title().startswith('Arctangent, residues')
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth'), width
                page.locator('summary').click()
                assert page.locator('details').get_attribute('open') is not None
                assert page.locator('details pre').is_visible()
                page.locator('#dependencies').scroll_into_view_if_needed()
                page.screenshot(path=str(a.report / f'cauchy-map-{width}.png'), full_page=False)
                page.evaluate('scrollTo(0,0)')
                page.screenshot(path=str(a.report / f'cauchy-page-{width}.png'), full_page=True)
                page.locator('a[href="ch-complex-paths.html"]').first.click()
                page.wait_for_url('**/ch-complex-paths.html')
                page.locator('#cauchy-arctan a').click()
                page.wait_for_url('**/cauchy-arctan.html')
                assert not errors, errors
                results.append(dict(width=width, noHorizontalOverflow=True, sourceDisclosure=True, chapterRoundTrip=True))
                page.close()
            browser.close()
    finally:
        server.shutdown()
    (a.report / 'cauchy-arctan-browser.json').write_text(json.dumps(results, indent=2) + '\n')
    print('PASS: Cauchy scope, pinned sources, preservation, desktop and mobile reading')

if __name__ == '__main__':
    main()
