#!/usr/bin/env python3
"""Check exact calculations, chapter placement, rendered cards and prior artifacts."""
from __future__ import annotations
import argparse,functools,hashlib,http.server,json,shutil,threading
from fractions import Fraction as Q
from pathlib import Path
from bs4 import BeautifulSoup
from pi_flashcards import check_arithmetic,numerical_record,render_cards


def check(site):
    report=json.loads((site/'reading/catalogue-placement.json').read_text())
    edition=json.loads((site/'reading/analysis-edition.json').read_text())
    assert edition['documentationRevision']==report['documentationRevision']
    assert edition['formulaCount']==10 and not edition['homeTeaser']
    assert edition['newtonBinomialCard'] and edition['logContinuationCard']
    assert not edition['cosineQuadratureInCatalogue'] and not edition['newLeanProofsClaimed']
    chapter=BeautifulSoup((site/'ch-foundations.html').read_text(),'html.parser')
    other=chapter.find(id='rem:sources-of-raw-reals');gallery=chapter.select_one('#pi-computations')
    assert other.text=='1.2.2 Other examples' and other.find_next_sibling()==gallery
    assert gallery.find_previous(['h1','h2'])==other
    assert chapter.find(id='rem:algebraic-numbers-sqrt-two').find_next(id='rem:sources-of-raw-reals')==other
    assert len(gallery.select('.pi-formula-card'))==10
    assert not gallery.select('#pi-cosine, [data-animation="cosine"]')
    assert '\\cos(' not in gallery.get_text() and 'Cosine quadrature' not in gallery.get_text()
    assert gallery.select_one('#pi-segment h3').text=='Newton'
    assert r'\frac1{14336}' in gallery.select_one('#pi-segment > .formula').text
    assert r'\frac5{589824}' in gallery.select_one('#pi-segment > .formula').text
    assert gallery.select_one('#pi-logarithm > .formula').text==r'\[\frac{i\pi}{2}=\operatorname{Log}(i)\]'
    assert len(gallery.select('#pi-logarithm .pi-calculation-table tbody tr'))==4
    for key in ['pi-leibniz','pi-basel','pi-wallis']:
        formula=gallery.select_one('#'+key+' > .formula').text
        assert r'\cdots' in formula and r'\sum' not in formula and r'\prod' not in formula
    record=json.loads((site/'reading/pi-flashcards-calculation.json').read_text())
    assert record.pop('documentationRevision')==report['documentationRevision']
    check_arithmetic(record)
    expected=BeautifulSoup(render_cards(record),'html.parser')
    assert [str(c) for c in gallery.select('.pi-formula-card')]==[str(c) for c in expected.select('.pi-formula-card')]
    # Independently check the written continued-fraction prefixes.
    convergents=[]
    for count in range(1,5):
        denominator=Q(2)
        for j in range(count,1,-1):denominator=2+Q((2*j-1)**2)/denominator
        convergents.append(1+1/denominator)
    assert convergents==[Q(3,2),Q(15,13),Q(105,76),Q(315,263)]
    for link in gallery.select('a[href^="#"]'):assert chapter.find(id=link['href'][1:]),link['href']
    home=BeautifulSoup((site/'index.html').read_text(),'html.parser')
    assert not home.select('.pi-teaser, .pi-formula-card')
    assert home.select_one('.chapter-one-examples-link a')['href']=='ch-foundations.html#pi-computations'
    assert home.select_one('article h1 em').text=='Analysis'
    assert home.select_one('.book-subtitle').text=='An alternative foundation to Calculus'
    assert '0;url=ch-foundations.html#pi-computations' in (site/'pi-computations.html').read_text()
    worked=BeautifulSoup((site/'cosine.html').read_text(),'html.parser')
    assert worked.select_one('[data-animation="cosine"]')
    assert len(worked.select('.numerical-bounds tbody tr'))>=4
    for path,expected in report['protectedArtifacts'].items():
        assert hashlib.sha256((site/path).read_bytes()).hexdigest()==expected,path
    return report


def browser_test(site,out):
    from playwright.sync_api import sync_playwright
    out.mkdir(parents=True,exist_ok=True)
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start()
    base=f'http://127.0.0.1:{server.server_port}/';errors=[]
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts=dict(headless=True,args=['--no-sandbox'])
        if exe:opts['executable_path']=exe
        browser=p.chromium.launch(**opts)
        context=browser.new_context(viewport=dict(width=1500,height=1050))
        page=context.new_page();page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(base+'index.html',wait_until='domcontentloaded')
        assert not page.locator('.pi-teaser').count()
        page.locator('.chapter-one-examples-link a').click()
        page.wait_for_url('**/ch-foundations.html#pi-computations')
        page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
        page.evaluate('() => MathJax.startup.promise')
        assert page.locator('#pi-computations .pi-formula-card').count()==10
        assert not page.locator('#pi-cosine').count()
        # All details must also render, not only the short card fronts.
        page.locator('#pi-computations .pi-formula-details').evaluate_all('(elements)=>elements.forEach(e=>e.open=true)')
        page.evaluate('() => MathJax.typesetPromise([document.querySelector("#pi-computations")])')
        assert not page.locator('mjx-merror,[data-mjx-error]').count()
        assert '1.570796326794' in page.locator('#pi-logarithm').text_content()
        page.locator('#pi-segment').screenshot(path=str(out/'newton-card-desktop.png'))
        page.locator('#pi-logarithm').screenshot(path=str(out/'logarithm-card-desktop.png'))
        page.locator('#pi-computations .pi-formula-details').evaluate_all('(elements)=>elements.forEach(e=>e.open=false)')
        page.locator('[id="rem:sources-of-raw-reals"]').scroll_into_view_if_needed()
        page.screenshot(path=str(out/'other-examples-desktop.png'),full_page=False)
        page.set_viewport_size(dict(width=390,height=850))
        page.locator('#pi-logarithm summary').click()
        page.evaluate('() => MathJax.typesetPromise([document.querySelector("#pi-logarithm")])')
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        page.locator('#pi-logarithm').screenshot(path=str(out/'logarithm-card-mobile.png'))
        page.locator('#pi-segment summary').click()
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        page.locator('#pi-segment').screenshot(path=str(out/'newton-card-mobile.png'))
        page.goto(base+'pi-computations.html',wait_until='domcontentloaded')
        page.wait_for_url('**/ch-foundations.html#pi-computations')
        page.goto(base+'cosine.html',wait_until='domcontentloaded')
        assert page.locator('[data-animation="cosine"]').count()==1
        assert not errors,errors
        browser.close()
    server.shutdown()
    (out/'catalogue-placement-tests.json').write_text(json.dumps(dict(passed=True,formulaCount=10,
      correctSubsection=True,cosineReservedForWorkedComparison=True,newtonExpanded=True,
      logContinuationNumerics=True,exactRationalChecks=True,oldBookmarkRedirect=True,
      mobile=True,mathematicalRendering=True,errors=errors),indent=2)+'\n')


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,required=True)
    ap.add_argument('--report',type=Path,default=Path('reader-edition-tests'))
    ap.add_argument('--structural-only',action='store_true')
    args=ap.parse_args();check(args.site)
    if not args.structural_only:browser_test(args.site,args.report)
    print('PASS: ten expanded flashcards, exact logarithm bounds, Newton attribution, prior proof data, chapter placement'+
      (' (structural checks only)' if args.structural_only else ', rendered desktop/mobile and links'))
if __name__=='__main__':main()
