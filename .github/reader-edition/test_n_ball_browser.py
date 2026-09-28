#!/usr/bin/env python3
"""Exercise the calculator, rendered mathematics, and responsive layout in CI."""
import argparse
import http.server
import json
import shutil
import threading
from functools import partial
from pathlib import Path
from playwright.sync_api import sync_playwright

p = argparse.ArgumentParser()
p.add_argument('--site', type=Path, required=True)
p.add_argument('--report', type=Path, required=True)
a = p.parse_args()
a.report.mkdir(parents=True, exist_ok=True)

class QuietHandler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *_):
        pass

server = http.server.ThreadingHTTPServer(('127.0.0.1', 0),
    partial(QuietHandler, directory=str(a.site.resolve())))
threading.Thread(target=server.serve_forever, daemon=True).start()
checks = []
try:
    with sync_playwright() as pw:
        options = dict(headless=True)
        executable = shutil.which('google-chrome') or shutil.which('chromium') or shutil.which('chromium-browser')
        if executable:
            options['executable_path'] = executable
        browser = pw.chromium.launch(**options)
        for width in [1440, 390]:
            page = browser.new_page(viewport=dict(width=width, height=1000))
            errors = []
            page.on('pageerror', lambda e: errors.append(str(e)))
            page.goto(f'http://127.0.0.1:{server.server_port}/n-ball-volume.html', wait_until='networkidle')
            page.wait_for_function('document.querySelectorAll("#result mjx-container").length >= 4')
            assert page.locator('#dimension-table tr').count() == 13
            assert page.locator('mjx-merror').count() == 0
            assert '4.18879020' in page.locator('#result').inner_text()
            page.get_by_role('button', name='Ordinary ball', exact=True).click()
            page.wait_for_function('document.querySelector("#rational-bounds").textContent.includes("3/2")')
            assert page.locator('#radius').input_value() == '3/2'
            page.locator('#dimension').fill('0')
            page.locator('#radius').fill('0')
            page.get_by_role('button', name='Compute', exact=True).click()
            raw = json.loads(page.locator('#rational-bounds').inner_text())
            assert raw['volume'] == dict(lower='1', upper='1')
            page.locator('#dimension').fill('3')
            page.get_by_role('button', name='Compute', exact=True).click()
            raw = json.loads(page.locator('#rational-bounds').inner_text())
            assert raw['volume'] == dict(lower='0', upper='0')
            page.locator('#radius').fill('1/0')
            page.get_by_role('button', name='Compute', exact=True).click()
            assert 'nonzero' in page.locator('#error').inner_text()
            assert not page.locator('#result').is_visible()
            page.get_by_role('button', name='Five dimensions', exact=True).click()
            page.wait_for_function('document.querySelectorAll("#result mjx-container").length >= 4')
            assert page.locator('#result').is_visible()
            assert not page.locator('#error').inner_text()
            assert not page.locator('mjx-merror').count()
            assert page.evaluate('document.documentElement.scrollWidth <= innerWidth')
            assert not errors, errors
            page.screenshot(path=str(a.report / f'n-ball-{width}.png'), full_page=True)
            page.locator('nav a[href="gaussian-convolution.html"]').click()
            page.wait_for_url('**/gaussian-convolution.html')
            page.get_by_role('link', name='Ball volumes and Gamma', exact=True).click()
            page.wait_for_url('**/n-ball-volume.html')
            checks.append(dict(width=width,mathRendered=True,calculator=True,links=True,noOverflow=True))
            page.close()
        browser.close()
finally:
    server.shutdown()
(a.report / 'n-ball-browser.json').write_text(json.dumps(checks, indent=2)+'\n')
print('PASS: ball calculator interactions, LaTeX, links, and desktop/mobile layouts')
