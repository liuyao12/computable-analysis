#!/usr/bin/env python3
"""Exact engine tests plus rendered reader integration and preservation checks."""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, shutil, subprocess, threading
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote, urlsplit
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'book/fundamental-matrix'
spec = importlib.util.spec_from_file_location('fundamental_matrix', Path(__file__).with_name('fundamental_matrix.py'))
fm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fm)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--site', type=Path, required=True)
    ap.add_argument('--report', type=Path, default=Path('reader-edition-tests'))
    ap.add_argument('--inline-preview', action='store_true', help='Use inline HTML only for sandbox browser previews; CI uses HTTP.')
    args = ap.parse_args()
    site, out = args.site.resolve(), args.report
    out.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(['node', str(SOURCE / 'test.cjs')], check=True, capture_output=True, text=True)
    (out / 'fundamental-matrix-engine.log').write_text(result.stdout)
    report = json.loads((site / 'reading/fundamental-matrix-edition.json').read_text())
    assert not report['newLeanProofsClaimed'] and not report['leanSourceModified']
    assert all(report['checks'].values())
    assert report['proofSourceCommit'] == json.loads((site / 'reading/manifest.json').read_text())['proofSourceCommit']
    assert fm.digest(site / fm.PAGE) == report['pageSha256']
    for name, expected in report['originalFileHashes'].items():
        p = site / name
        actual = hashlib.sha256(fm.ADDITION.sub('', p.read_text()).encode()).hexdigest() if name in report['changedReaderPages'] else fm.digest(p)
        assert actual == expected, f'Changed pre-existing content: {name}'
    document = BeautifulSoup((site / fm.PAGE).read_text(), 'html.parser')
    assert document.title.get_text() == 'Fundamental Matrix · Computable Analysis'
    assert document.select_one('.brand')['href'] == 'index.html'
    assert document.select_one('#fm-book-contents a[aria-current="page"]')['href'] == fm.PAGE
    assert len(document.select('math')) > 100 and not document.select('merror')
    ids = [t['id'] for t in document.select('[id]')]
    assert len(ids) == len(set(ids)), 'Duplicate HTML IDs'
    for a in document.select('a[href]'):
        link = urlsplit(a['href'])
        if link.scheme or link.netloc:
            continue
        target = site / unquote(link.path) if link.path else site / fm.PAGE
        assert target.exists(), f'Broken local link: {a["href"]}'
        if not link.path and link.fragment:
            assert unquote(link.fragment) in ids
    for name in ['index.html', 'ch-differential-equations.html']:
        d = BeautifulSoup((site / name).read_text(), 'html.parser')
        assert d.select_one('#book-nav a[href="fundamental-matrix.html"]')
        assert d.select_one('article a[href="fundamental-matrix.html"]')
    class Quiet(SimpleHTTPRequestHandler):
        def log_message(self, *args):
            pass
    server = ThreadingHTTPServer(('127.0.0.1', 0), partial(Quiet, directory=str(site)))
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    origin = f'http://127.0.0.1:{server.server_port}'
    errors, external = [], []
    try:
        with sync_playwright() as p:
            executable = shutil.which('chromium') or shutil.which('google-chrome')
            options = {'headless': True, 'args': ['--no-sandbox']}
            if executable:
                options['executable_path'] = executable
            browser = p.chromium.launch(**options)
            for width in [1440, 1024, 768, 390]:
                page = browser.new_page(viewport={'width': width, 'height': 1000})
                page.on('pageerror', lambda error: errors.append(str(error)))
                page.on('request', lambda request: external.append(request.url) if not request.url.startswith(origin) else None)
                if args.inline_preview:
                    page.set_content((site / fm.PAGE).read_text(), wait_until='load')
                else:
                    page.goto(origin + '/' + fm.PAGE, wait_until='networkidle')
                page.wait_for_function('window.FundamentalMatrixNotebook && document.getElementById("value").textContent.includes("≈")')
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1'), width
                page.locator('.book-menu > summary').click()
                assert page.locator('#fm-book-contents').is_visible()
                box = page.locator('#fm-book-contents').bounding_box()
                assert box['x'] >= 0 and box['x'] + box['width'] <= width + 1
                page.keyboard.press('Escape')
                assert not page.locator('#fm-book-contents').is_visible()
                for model in ['exponential', 'scalar', 'oscillator', 'triangular', 'airy']:
                    page.locator('#model').select_option(model)
                    page.locator('#plus').click()
                    page.wait_for_timeout(60)
                    assert page.locator('#value').inner_text().startswith('≈ ')
                    assert page.locator('#plot path').count() > 3
                    assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                page.locator('#model').select_option('triangular')
                page.locator('#iterations').evaluate('(e) => { e.value=3; e.dispatchEvent(new Event("input", {bubbles:true})); }')
                page.wait_for_timeout(80)
                assert '(exact)' in page.locator('#bound').inner_text()
                if width > 800:
                    page.evaluate('document.getElementById("follow").checked=true; document.getElementById("examples").scrollIntoView({behavior:"instant"});')
                    page.wait_for_function('window.FundamentalMatrixNotebook.state.id === "scalar"')
                    lab = page.locator('.lab-sticky').bounding_box()
                    head = page.locator('.topbar').bounding_box()
                    assert lab['y'] >= head['height'] - 1
                page.evaluate('scrollTo({top:0,behavior:"instant"})')
                page.wait_for_timeout(100)
                if width in [1440, 390]:
                    page.screenshot(path=str(out / f'fundamental-matrix-{width}.png'))
                page.close()
            browser.close()
    finally:
        server.shutdown()
    assert not errors, errors
    assert not external, external
    checks = {'exactEngine': True, 'preservation': True, 'localLinks': True,
              'nativeMathML': True, 'desktopAndMobile': True, 'allExamples': True,
              'scrollFollowing': True, 'keyboardContents': True, 'offlinePage': True, 'httpLoaded': not args.inline_preview}
    (out / 'fundamental-matrix-tests.json').write_text(json.dumps(checks, indent=2) + '\n')
    print('PASS: exact engine, original proof data, book links, MathML, four viewport widths and notebook interactions.')

if __name__ == '__main__':
    main()
