#!/usr/bin/env python3
"""Exact Picard tests, standalone presentation, reader links, and browser checks."""
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
    ap.add_argument('--inline-preview', action='store_true', help='Use inline HTML only for sandbox previews; CI uses HTTP.')
    args = ap.parse_args()
    site, out = args.site.resolve(), args.report
    out.mkdir(parents=True, exist_ok=True)
    for name in ['test.cjs', 'test-nonlinear.cjs']:
        result = subprocess.run(['node', str(SOURCE / name)], check=True, capture_output=True, text=True)
        (out / f'fundamental-matrix-{name}.log').write_text(result.stdout)
    report = json.loads((site / 'reading/fundamental-matrix-edition.json').read_text())
    assert not report['newLeanProofsClaimed'] and not report['leanSourceModified']
    assert report['standalonePresentation'] and report['nonlinearExamples'] == ['growth', 'saturation']
    assert all(report['checks'].values())
    assert report['proofSourceCommit'] == json.loads((site / 'reading/manifest.json').read_text())['proofSourceCommit']
    assert fm.digest(site / fm.PAGE) == report['pageSha256']
    for name, expected in report['originalFileHashes'].items():
        p = site / name
        actual = hashlib.sha256(fm.ADDITION.sub('', p.read_text()).encode()).hexdigest() if name in report['changedReaderPages'] else fm.digest(p)
        assert actual == expected, f'Changed pre-existing content: {name}'
    html = (site / fm.PAGE).read_text()
    document = BeautifulSoup(html, 'html.parser')
    assert document.title.get_text().startswith('Fundamental Matrix')
    assert document.select_one('.brand')['href'] == '#top'
    for forbidden in ['computable analysis', 'computable-analysis', 'lean formalization', 'proof snapshot']:
        assert forbidden not in html.lower(), forbidden
    assert not document.select('.book-menu, #fm-book-contents, .book-return')
    assert len(document.select('math')) > 170 and not document.select('merror')
    for section in ['nonlinear', 'saturation']:
        assert len(document.select(f'#{section} math')) > 5
    ids = [t['id'] for t in document.select('[id]')]
    assert len(ids) == len(set(ids)), 'Duplicate HTML IDs'
    for a in document.select('a[href]'):
        link = urlsplit(a['href'])
        if link.scheme or link.netloc:
            continue
        assert not link.path, 'Standalone page must not require another book page.'
        if link.fragment:
            assert unquote(link.fragment) in ids
    for name in ['index.html', 'ch-differential-equations.html']:
        d = BeautifulSoup((site / name).read_text(), 'html.parser')
        assert d.select_one('#book-nav a[href="fundamental-matrix.html"]')
        assert d.select_one('article a[href="fundamental-matrix.html"]')
    class Quiet(SimpleHTTPRequestHandler):
        def log_message(self, *args):
            pass
    server = ThreadingHTTPServer(('127.0.0.1', 0), partial(Quiet, directory=str(site)))
    threading.Thread(target=server.serve_forever, daemon=True).start()
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
                    page.set_content(html, wait_until='load')
                else:
                    page.goto(origin + '/' + fm.PAGE, wait_until='networkidle')
                page.wait_for_function('window.FundamentalMatrixNotebook && document.getElementById("value").textContent.includes("≈")')
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1'), width
                assert 'Computable' not in page.locator('body').inner_text()
                for model in ['exponential', 'growth', 'saturation', 'scalar', 'oscillator', 'triangular', 'airy']:
                    page.locator('#model').select_option(model)
                    page.locator('#plus').click()
                    page.wait_for_timeout(80)
                    assert page.locator('#value').inner_text().startswith('≈ ')
                    assert page.locator('#plot path').count() > 3
                    assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                    nonlinear = model in ['growth', 'saturation']
                    assert page.locator('#data-details').is_hidden() == nonlinear
                    assert page.locator('#matrix-panel').evaluate('(e) => e.hidden') == nonlinear
                    if nonlinear:
                        assert page.locator('#iterations').get_attribute('max') == '7'
                        page.locator('#iterations').evaluate('(e) => { e.value=7; e.dispatchEvent(new Event("input", {bubbles:true})); }')
                        page.wait_for_timeout(80)
                        assert page.locator('#plus').is_disabled()
                        assert '127' in page.locator('#poly-note').text_content()
                        if model == 'saturation':
                            assert 'bracket' in page.locator('#bound-note').inner_text()
                page.locator('#model').select_option('triangular')
                assert page.locator('#iterations').get_attribute('max') == '36'
                page.locator('#iterations').evaluate('(e) => { e.value=3; e.dispatchEvent(new Event("input", {bubbles:true})); }')
                page.wait_for_timeout(80)
                assert '(exact)' in page.locator('#bound').inner_text()
                if width > 800:
                    page.evaluate('document.getElementById("follow").checked=true;')
                    for section,model in [('nonlinear','growth'),('saturation','saturation'),('examples','scalar')]:
                        page.evaluate('(id) => document.getElementById(id).scrollIntoView({behavior:"instant"})', section)
                        page.wait_for_function('(id) => window.FundamentalMatrixNotebook.state.id === id', arg=model)
                        lab = page.locator('.lab-sticky').bounding_box()
                        head = page.locator('.topbar').bounding_box()
                        assert lab['y'] >= head['height'] - 1
                    page.evaluate('document.getElementById("nonlinear").scrollIntoView({behavior:"instant"})')
                    page.wait_for_function('window.FundamentalMatrixNotebook.state.id === "growth"')
                    if width == 1440:
                        page.screenshot(path=str(out / 'fundamental-matrix-nonlinear.png'))
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
    checks = {'exactEngine': True, 'nonlinearEngine': True, 'preservation': True,
              'incomingBookLinks': True, 'standalonePresentation': True,
              'nativeMathML': True, 'desktopAndMobile': True, 'allSevenExamples': True,
              'nonlinearIterationLimits': True, 'nonlinearMatrixHidden': True,
              'scrollFollowing': True, 'offlinePage': True, 'httpLoaded': not args.inline_preview}
    (out / 'fundamental-matrix-tests.json').write_text(json.dumps(checks, indent=2) + '\n')
    print('PASS: exact linear/nonlinear iterations, preservation, standalone page, links, MathML, four viewports and notebook interactions.')

if __name__ == '__main__':
    main()
