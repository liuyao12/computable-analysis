#!/usr/bin/env python3
"""Check current convention, proof boundaries, links, and rendered equations."""
import argparse
import hashlib
import json
import shutil
import threading
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright

class Quiet(SimpleHTTPRequestHandler):
    def log_message(self, *_args): pass

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--site', type=Path, required=True); ap.add_argument('--report', type=Path, required=True)
    a = ap.parse_args(); site = a.site.resolve(); a.report.mkdir(parents=True, exist_ok=True)
    data = json.loads((site/'reading/integral-enclosures-edition.json').read_text())
    assert all(data['checks'].values())
    assert not data['directLogarithmBridgeProved'] and not data['generalCauchyRectangleBridgeProved']
    inventory = json.loads((site/'reading/integral-inventory.json').read_text())
    assert len(inventory['files']) == data['nativeModules']
    for name, digest in data['artifacts'].items():
        assert hashlib.sha256((site/name).read_bytes()).hexdigest() == digest, name
    for name in ['ch-integrals.html', 'ch-complex-paths.html']:
        doc = BeautifulSoup((site/name).read_text(), 'html.parser')
        assert doc.select_one('#integral-enclosure-convention a')['href'] == 'integral-enclosures.html'
    text = BeautifulSoup((site/'ch-complex-paths.html').read_text(), 'html.parser').get_text()
    assert 'The right side consists of two real integral computations' not in text
    doc = BeautifulSoup((site/'integral-enclosures.html').read_text(), 'html.parser')
    assert doc.select_one('#vertical') and doc.select_one('#formalization')
    assert not doc.select('sup, sub')
    server = ThreadingHTTPServer(('127.0.0.1', 0), partial(Quiet, directory=str(site)))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    try:
        with sync_playwright() as p:
            options = {'headless': True, 'args': ['--no-sandbox']}
            exe = shutil.which('google-chrome') or shutil.which('chromium')
            if exe: options['executable_path'] = exe
            browser = p.chromium.launch(**options)
            for width in [1440, 390, 320]:
                page = browser.new_page(viewport={'width': width, 'height': 1000})
                page.goto(f'http://127.0.0.1:{server.server_port}/integral-enclosures.html', wait_until='networkidle')
                page.wait_for_function("document.querySelectorAll('mjx-container').length >= 7")
                assert page.locator('mjx-merror').count() == 0
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 2'), width
                page.screenshot(path=str(a.report/f'integral-enclosures-{width}.png'), full_page=True)
                page.close()
            browser.close()
    finally:
        server.shutdown()
    (a.report/'integral-enclosures.json').write_text(json.dumps({'checks': 'passed', 'nativeModules': data['nativeModules'], 'widths': [1440,390,320]}, indent=2)+'\n')
    print('PASS: enclosure convention, proof scope, source inventory, and responsive typeset equations')

if __name__ == '__main__': main()
