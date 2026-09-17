#!/usr/bin/env python3
"""Final-output guards for patterns, branches, bounds and reader rendering."""
from __future__ import annotations
import argparse,functools,hashlib,http.server,json,shutil,threading,os,mimetypes
from fractions import Fraction as Q
from pathlib import Path
from bs4 import BeautifulSoup
from pi_patterns import record,check_arithmetic,approximation,newton_data,error_label

def check(site):
    r=json.loads((site/'reading/pi-patterns.json').read_text())
    core=record();assert all(r[k]==v for k,v in core.items());check_arithmetic(core)
    chapter=BeautifulSoup((site/'ch-foundations.html').read_text(),'html.parser')
    gallery=chapter.select_one('#pi-computations')
    assert len(gallery.select('.pi-formula-card'))==11 and not gallery.select('#pi-cosine')
    assert chapter.find(id='rem:sources-of-raw-reals').find_next_sibling()==gallery
    assert 'Three ways to compute Log(i)' in gallery.select_one('#pi-logarithm').get_text()
    assert r['logarithmMethods']==['local-taylor','symmetric-log','machin']
    assert r['newtonFactored'] and r['machinCard'] and not r['usesNumericalPi'] and not r['newLeanProofsClaimed']
    for text in [r'1\cdot1\cdot3',r'2\cdot4\cdot6',r'(1/2)^7',r'2^{3k+1}k!']:
        assert text in gallery.select_one('#pi-segment').get_text(),text
    assert r'239' in gallery.select_one('#pi-machin').get_text()
    for a in gallery.select('a[href^="#"]'): assert chapter.find(id=a['href'][1:]),a['href']
    for row in r['comparisons']:
        mantissa,e=row['radiusDisplay'].split(' × 10^');assert Q(mantissa)*Q(10)**int(e)>=Q(row['radius'])
        if row['method']!='local-taylor': assert Q(row['real'])==0
    for n in (4,8,16,32):
        old=approximation('machin',n);later=approximation('machin',n+1)
        assert Q(later['radius'])<Q(old['radius'])
        assert max(Q(old['imaginaryBox'][0]),Q(later['imaginaryBox'][0]))<=min(Q(old['imaginaryBox'][1]),Q(later['imaginaryBox'][1]))
    for f,h in r['protectedArtifacts'].items():assert hashlib.sha256((site/f).read_bytes()).hexdigest()==h,f
    for f in ['analysis-edition.json','catalogue-placement.json']:
        meta=json.loads((site/'reading'/f).read_text());assert meta['formulaCount']==11 and meta['documentationRevision']==r['documentationRevision']
    assert 'class="pi-teaser"' not in (site/'index.html').read_text()
    return r

def browser_test(site,out,offline=False):
    from playwright.sync_api import sync_playwright
    out.mkdir(parents=True,exist_ok=True)
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/'
    errors=[]
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts={'headless':True,'args':['--no-sandbox']}
        if exe:opts['executable_path']=exe
        browser=p.chromium.launch(**opts);page=browser.new_page(viewport={'width':1500,'height':1050})
        page.on('pageerror',lambda e:errors.append(str(e)))
        if os.environ.get('MATHJAX_LOCAL'):
            prefix='https://cdn.jsdelivr.net/npm/mathjax@3/es5/'
            def local_mathjax(route):
                relative=route.request.url.split(prefix,1)[1].split('?',1)[0]
                file=Path(os.environ['MATHJAX_LOCAL'])/relative
                route.fulfill(path=str(file),content_type=mimetypes.guess_type(file)[0] or 'application/octet-stream',headers={'Access-Control-Allow-Origin':'*'})
            page.route(prefix+'**',local_mathjax)
        page.goto(base+'ch-foundations.html',wait_until='domcontentloaded')
        page.wait_for_selector('#pi-machin')
        if not offline:
            page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
            page.evaluate('() => MathJax.startup.promise')
        for viewport in [{'width':1500,'height':1050},{'width':390,'height':850}]:
            page.set_viewport_size(viewport);label='desktop' if viewport['width']>400 else 'mobile'
            for card in ['pi-segment','pi-machin','pi-logarithm']:
                page.locator('#'+card+' details').evaluate_all('(els)=>els.forEach(e=>e.open=true)')
                if not offline:page.evaluate('() => MathJax.typesetPromise([document.querySelector("#pi-computations")])')
                page.locator('#'+card).scroll_into_view_if_needed()
                assert not page.locator('mjx-merror,[data-mjx-error]').count()
                assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
                page.screenshot(path=str(out/(card+'-'+label+'.png')),full_page=False)
            assert page.locator('#pi-logarithm .pi-calculation-table tbody tr').count()==9
            assert page.locator('#pi-computations .pi-formula-card').count()==11
        page.goto(base+'cosine.html',wait_until='domcontentloaded')
        assert page.locator('[data-animation="cosine"]').count()==1
        assert not errors,errors;browser.close()
    server.shutdown()
    (out/'pi-pattern-tests.json').write_text(json.dumps(dict(passed=True,formulaCount=11,newtonFactored=True,machin=True,
        logarithmMethods=3,mathematicalRendering=not offline,structuralOnlyBrowser=offline,mobile=True,errors=errors),indent=2)+'\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,required=True);ap.add_argument('--report',type=Path,default=Path('reader-edition-tests'));ap.add_argument('--structural-only',action='store_true');a=ap.parse_args()
    check(a.site)
    if not a.structural_only:browser_test(a.site,a.report)
    print('PASS: factored Newton coefficients and recurrence, Machin, three branch-consistent logarithm computations, exact error boxes and original proof artifacts')
if __name__=='__main__':main()
