#!/usr/bin/env python3
"""Check worked algebra, static reading layout, incoming links, and preservation."""
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
SECTIONS = ['iteration', 'oscillator', 'nonlinear', 'airy', 'matrix', 'forcing', 'convergence']

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--site', type=Path, required=True)
    ap.add_argument('--report', type=Path, default=Path('reader-edition-tests'))
    ap.add_argument('--inline-preview', action='store_true', help='Render local HTML without network navigation; CI uses HTTP.')
    args = ap.parse_args()
    site, out = args.site.resolve(), args.report
    out.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(['node', str(SOURCE / 'test-second-order.cjs')], check=True, capture_output=True, text=True)
    (out / 'fundamental-matrix-engine.log').write_text(result.stdout)
    report = json.loads((site / 'reading/fundamental-matrix-edition.json').read_text())
    assert not report['newLeanProofsClaimed'] and not report['leanSourceModified']
    assert not report['runtimeScripts'] and report['differentialOrder'] == 2
    assert all(report['checks'].values())
    assert report['proofSourceCommit'] == json.loads((site / 'reading/manifest.json').read_text())['proofSourceCommit']
    assert fm.digest(site / fm.PAGE) == report['pageSha256']
    for name, expected in report['originalFileHashes'].items():
        p = site / name
        actual = hashlib.sha256(fm.ADDITION.sub('', p.read_text()).encode()).hexdigest() if name in report['changedReaderPages'] else fm.digest(p)
        assert actual == expected, f'Changed pre-existing content: {name}'
    html = (site / fm.PAGE).read_text()
    document = BeautifulSoup(html, 'html.parser')
    assert document.title.get_text() == 'Fundamental Matrix — Second-order equations, step by step'
    assert 'computable analysis' not in html.lower() and 'computable-analysis' not in html.lower()
    assert 'formalization' not in document.get_text().lower()
    assert document.select_one('.brand')['href'] == '#top'
    assert not document.select('script,input,select,button,svg,canvas,iframe')
    assert not document.select('#lab,.lab-column,.lab-sticky,#plot,#model')
    assert len(document.select('math')) > 100 and not document.select('merror')
    assert [s['id'] for s in document.select('article > section')] == SECTIONS
    ids = [t['id'] for t in document.select('[id]')]
    assert len(ids) == len(set(ids)), 'Duplicate HTML IDs'
    for a in document.select('a[href]'):
        link = urlsplit(a['href'])
        if link.scheme or link.netloc:
            continue
        assert not link.path, 'The authored page should stand alone.'
        assert unquote(link.fragment) in ids, a['href']
    for name in ['index.html', 'ch-differential-equations.html']:
        d = BeautifulSoup((site / name).read_text(), 'html.parser')
        assert d.select_one('#book-nav a[href="fundamental-matrix.html"]')
        assert d.select_one('article a[href="fundamental-matrix.html"]')
        for link in d.select('a[href="fundamental-matrix.html"]'):
            assert 'interactive' not in link.get_text().lower()
    # Re-running the integration must not duplicate links or change the essay.
    before_page = fm.digest(site / fm.PAGE)
    subprocess.run(['python3', str(Path(__file__).with_name('fundamental_matrix.py')), '--site', str(site), '--revision', report['documentationRevision']], check=True, capture_output=True, text=True)
    assert fm.digest(site / fm.PAGE) == before_page
    assert json.loads((site / 'reading/fundamental-matrix-edition.json').read_text()) == report
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
            for width in [1440, 1024, 768, 390, 320]:
                page = browser.new_page(viewport={'width': width, 'height': 1000})
                page.on('pageerror', lambda error: errors.append(str(error)))
                page.on('request', lambda request: external.append(request.url) if not request.url.startswith(origin) else None)
                if args.inline_preview:
                    page.set_content(html, wait_until='load')
                else:
                    page.goto(origin + '/' + fm.PAGE, wait_until='networkidle')
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1'), width
                assert page.locator('script,input,select,button,svg,canvas').count() == 0
                assert page.locator('math[display="block"]').count() > 30
                assert page.locator('math[display="block"]').first.bounding_box()['height'] > 20
                assert page.locator('.topbar').evaluate('(e)=>getComputedStyle(e).position') == 'static'
                if width in [1440, 390]:
                    page.screenshot(path=str(out / f'fundamental-matrix-{width}.png'))
                page.locator('#contents a[href="#matrix"]').click()
                assert page.url.endswith('#matrix')
                assert page.locator('#matrix').bounding_box()['y'] >= 0
                for detail in page.locator('details').all():
                    detail.locator('summary').click()
                    assert detail.get_attribute('open') is not None
                    assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1'), width
                if width == 1440:
                    for ident in ['oscillator','nonlinear','matrix','forcing']:
                        page.locator('#'+ident).scroll_into_view_if_needed()
                        page.evaluate('(id)=>document.getElementById(id).scrollIntoView()', ident)
                        page.screenshot(path=str(out / f'fundamental-matrix-{ident}.png'))
                if width == 390:
                    page.evaluate('document.getElementById("forcing").scrollIntoView()')
                    page.screenshot(path=str(out / 'fundamental-matrix-forcing-mobile.png'))
                page.close()
            # Core content and optional proofs remain readable with JS disabled.
            context = browser.new_context(java_script_enabled=False, viewport={'width':390,'height':844})
            page = context.new_page()
            if args.inline_preview:
                page.set_content(html, wait_until='load')
            else:
                page.goto(origin + '/' + fm.PAGE)
            assert page.locator('#theorem').inner_text()
            page.locator('#independence summary').click()
            assert page.locator('#independence').get_attribute('open') is not None
            context.close()
            browser.close()
    finally:
        server.shutdown()
    assert not errors, errors
    assert not external, external
    checks = {'exactWorkedAlgebra': True, 'preservation': True, 'idempotentIntegration': True,
              'incomingBookLinks': True, 'standaloneSecondOrderText': True,
              'nativeMathML': True, 'fiveViewportWidths': True, 'noNotebookOrPlots': True,
              'noRuntimeScripts': True, 'worksWithoutJavaScript': True, 'httpLoaded': not args.inline_preview}
    (out / 'fundamental-matrix-tests.json').write_text(json.dumps(checks, indent=2) + '\n')
    print('PASS: worked second-order algebra, proof-data preservation, links, static layout and five viewport widths.')

if __name__ == '__main__':
    main()
