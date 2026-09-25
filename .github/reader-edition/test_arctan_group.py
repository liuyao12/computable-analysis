#!/usr/bin/env python3
"""Checks for the grouped arctangent card and preserved old fragments."""
from __future__ import annotations
import argparse, functools, hashlib, http.server, json, shutil, threading
from pathlib import Path
from bs4 import BeautifulSoup
from group_arctan import METHODS, TITLE_FORMULA

def check(site):
    record=json.loads((site/'reading/arctan-group.json').read_text())
    doc=BeautifulSoup((site/'ch-foundations.html').read_text(),'html.parser')
    gallery=doc.select_one('#pi-computations');group=gallery.select_one('#pi-arctan')
    assert doc.find(id='rem:sources-of-raw-reals').find_next_sibling()==gallery
    assert len(gallery.select('.pi-formula-card'))==7
    assert group.h3.text=='Arctangent'
    assert group.select_one(':scope > .formula').get_text()==r'\['+TITLE_FORMULA+r'\]'
    assert 'open' not in group.details.attrs
    assert [e['id'] for e in group.select('.pi-computation-method')]==METHODS
    assert not gallery.select('#pi-cosine')
    assert gallery.select_one('#pi-logarithm') and gallery.select_one('#pi-segment')
    machin=group.find(id='pi-machin');assert len(machin.select('.formula'))==1
    assert r'\arctan' in machin.text and r'\sum' not in machin.text and not machin.select('details')
    for link in gallery.select('a[href^="#"]'):assert doc.find(id=link['href'][1:]),link['href']
    ids=[n['id'] for n in doc.select('[id]')];assert len(ids)==len(set(ids))
    for f,h in record['protectedArtifacts'].items():assert hashlib.sha256((site/f).read_bytes()).hexdigest()==h,f
    for f in ['analysis-edition.json','catalogue-placement.json']:
        m=json.loads((site/'reading'/f).read_text())
        assert m['documentationRevision']==record['documentationRevision']
        assert m['formulaCount']==7 and m['underlyingRepresentationCount']==11 and m['arctangentGrouped']
    assert record['originalFormulasRetained'] and record['proofDataAndNumericsUnchanged']
    return record

def browser(site,out,offline=False):
    from playwright.sync_api import sync_playwright
    out.mkdir(parents=True,exist_ok=True)
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start()
    base=f'http://127.0.0.1:{server.server_port}/';errors=[]
    with sync_playwright() as p:
        exe=next((shutil.which(x) for x in ['google-chrome','chromium','chromium-browser'] if shutil.which(x)),None)
        options={'headless':True,'args':['--no-sandbox']}
        if exe:options['executable_path']=exe
        b=p.chromium.launch(**options);page=b.new_page(viewport={'width':1500,'height':1050})
        page.on('pageerror',lambda e:errors.append(str(e)))
        def visit(fragment):
            if not offline:
                # Different queries force a fresh document rather than a hash-only navigation.
                page.goto(base+'ch-foundations.html?group-test='+fragment+'#'+fragment,wait_until='domcontentloaded')
                return
            text=(site/'ch-foundations.html').read_text()
            doc=BeautifulSoup(text,'html.parser')
            for script in doc.select('script[src]'):script.decompose()
            for link in doc.select('link[rel="stylesheet"]'):
                f=site/link.get('href','')
                if f.is_file():
                    style=doc.new_tag('style');style.string=f.read_text();link.replace_with(style)
            page.evaluate('location.hash=""')
            page.set_content(str(doc),wait_until='domcontentloaded')
            page.evaluate('(key)=>{location.hash=key;window.dispatchEvent(new HashChangeEvent("hashchange"));}',fragment)
        visit('pi-arctan')
        if not offline:
            page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
            page.evaluate('() => MathJax.startup.promise')
        assert page.locator('.pi-formula-card').count()==7
        outer=page.locator('#pi-arctan > details')
        assert outer.get_attribute('open') is None
        outer.locator(':scope > summary').click()
        assert outer.get_attribute('open') is not None
        for size in [{'width':1500,'height':1050},{'width':390,'height':850}]:
            page.set_viewport_size(size);label='desktop' if size['width']>400 else 'mobile'
            page.locator('#pi-arctan details').evaluate_all('(els)=>els.forEach(e=>e.open=true)')
            if not offline:page.evaluate('() => MathJax.typesetPromise([document.querySelector("#pi-arctan")])')
            assert not page.locator('mjx-merror,[data-mjx-error]').count()
            assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
            page.locator('#pi-arctan').evaluate('(e)=>e.scrollIntoView({block:"start"})')
            page.screenshot(path=str(out/('arctan-group-'+label+'.png')))
            page.locator('#pi-machin').scroll_into_view_if_needed()
            assert page.locator('#pi-machin').is_visible()
            page.screenshot(path=str(out/('arctan-machin-'+label+'.png')))
        for key in ['pi-geometry','pi-leibniz','pi-brouncker','pi-machin','pi-arctan-integral']:
            visit(key)
            page.wait_for_function('document.querySelector("#pi-arctan > details").open')
            assert page.locator('#'+key).is_visible()
        visit('pi-log-one-plus-i')
        page.wait_for_function('document.querySelector("#pi-log-one-plus-i").open')
        assert page.locator('#pi-log-one-plus-i .log-one-table').is_visible()
        visit('pi-arctan')
        assert page.locator('#pi-arctan > details').get_attribute('open') is None
        page.evaluate('location.hash="pi-machin"')
        page.wait_for_function('document.querySelector("#pi-arctan > details").open')
        assert page.locator('#pi-machin').is_visible()
        assert not errors,errors
        b.close()
    server.shutdown()
    (out/'arctan-group-tests.json').write_text(json.dumps(dict(passed=True,flashcardCount=7,arctangentMethods=5,
       oldFragmentNavigation=True,machinUsesArctanOnly=True,mobile=True,mathematicalRendering=not offline,
       protectedProofsAndNumerics=True,errors=errors),indent=2)+'\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,required=True)
    ap.add_argument('--report',type=Path,default=Path('reader-edition-tests'));ap.add_argument('--offline',action='store_true')
    a=ap.parse_args();check(a.site);browser(a.site,a.report,a.offline)
    print('PASS: arctangent group, original formulas, Machin notation, fragment navigation, mobile and preserved artifacts'+(' (offline structural browser only)' if a.offline else ' and mathematical rendering'))
if __name__=='__main__':main()
