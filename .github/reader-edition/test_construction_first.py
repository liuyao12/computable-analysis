#!/usr/bin/env python3
"""Check provenance, retained routes, and mathematical rendering of the purpose page."""
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
    def log_message(self, *_args):
        pass


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    site = args.site.resolve()
    args.report.mkdir(parents=True, exist_ok=True)
    report = json.loads((site / 'reading/construction-first-edition.json').read_text())
    assert not report['newLeanTheoremsClaimed'] and not report['leanStatementsChanged']
    inventory = json.loads((site / 'reading/construction-first-inventory.json').read_text())
    assert report['reviewedSourceRevision'] == inventory['sourceRevision']
    assert len(inventory['files']) == report['nativeModules'] + report['otherSourceFiles']
    for name, digest in report['artifacts'].items():
        assert hashlib.sha256((site / name).read_bytes()).hexdigest() == digest, name
    doc = BeautifulSoup((site / 'programme.html').read_text(), 'html.parser')
    ids = [tag['id'] for tag in doc.select('[id]')]
    assert len(ids) == len(set(ids)), 'Duplicate page anchors'
    for anchor in ['boundary', 'audit', 'scope', 'next', 'edition', 'construction-first']:
        assert doc.select_one('#' + anchor), anchor
    for link in doc.select('a[href]'):
        href = link['href']
        if '://' in href or href.startswith(('#', 'mailto:')):
            continue
        target = site / href.split('#')[0]
        assert target.is_file() or (target / 'index.html').is_file(), href
    assert not doc.select('#construction-first sup, #construction-first sub')
    server = ThreadingHTTPServer(('127.0.0.1', 0), partial(Quiet, directory=str(site)))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    try:
        with sync_playwright() as p:
            options = {'headless': True, 'args': ['--no-sandbox']}
            executable = shutil.which('google-chrome') or shutil.which('chromium')
            if executable:
                options['executable_path'] = executable
            browser = p.chromium.launch(**options)
            for width in [1440, 390, 320]:
                page = browser.new_page(viewport={'width': width, 'height': 1000})
                page.goto(f'http://127.0.0.1:{server.server_port}/programme.html',
                          wait_until='networkidle')
                page.wait_for_function(
                    "document.querySelectorAll('#construction-first mjx-container').length >= 3")
                assert page.locator('mjx-merror').count() == 0
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 2'), width
                page.screenshot(path=str(args.report / f'construction-first-{width}.png'), full_page=True)
                page.close()
            browser.close()
    finally:
        server.shutdown()
    print('PASS: source provenance, retained routes, anchors, and responsive mathematical rendering')


if __name__ == '__main__':
    main()
