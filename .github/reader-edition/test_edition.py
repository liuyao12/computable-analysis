#!/usr/bin/env python3
"""Static, numeric and real-browser publication gates for the reader edition."""
from __future__ import annotations
import argparse, functools, hashlib, http.server, json, shutil, threading
from fractions import Fraction as Q
from pathlib import Path
from bs4 import BeautifulSoup
from PIL import Image
from playwright.sync_api import sync_playwright
from analysis_edition import FORMULAS, PROOF_SHA, SUBTITLE, example

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--site',type=Path,required=True)
    ap.add_argument('--report',type=Path,required=True);ap.add_argument('--static-only',action='store_true')
    args=ap.parse_args();site=args.site;out=args.report;out.mkdir(exist_ok=True,parents=True)
    doc=lambda f:BeautifulSoup((site/f).read_text(),'html.parser')
    info=json.loads((site/'reading/analysis-edition.json').read_text())
    assert info['proofSourceCommit']==PROOF_SHA and info['proofDeclarationsAndEdgesUnchanged']
    assert info['originalChapterOneTextPreserved'] and not info['newLeanProofsClaimed']
    for f,h in info['protectedArtifacts'].items():assert hashlib.sha256((site/f).read_bytes()).hexdigest()==h,f
    for f in ['index.html','ch-foundations.html','pi-computations.html','cosine.html','integral-families.html','cartwright.html']:
        s=doc(f);assert s.select_one('.brand em').text=='Analysis'
        assert s.select_one('.header-about').text==SUBTITLE
        assert s.select_one('a.pi-catalogue-navigation')['href']=='pi-computations.html'
        assert s.select_one('meta[name="documentation-revision"]')['content']==info['documentationRevision']
    home=doc('index.html');assert home.h1.get_text()=='Computable Analysis'
    assert home.select_one('.book-subtitle').text==SUBTITLE
    teaser=home.select_one('#pi-computations')
    assert '\\frac1\\pi=\\int_0^{1/2}\\cos(\\pi x)' in str(teaser)
    assert 'C(x)' not in str(teaser) and '\\cos(\\pi x)' in str(teaser)
    for f in ['pi-computations.html','ch-foundations.html']:
        s=doc(f);cards=s.select('#pi-computations .pi-formula-card')
        assert len(cards)==len(FORMULAS)==10
        assert not any('C(x)' in str(c) for c in cards)
        for a in s.select('#pi-computations a[href]'):
            target=a['href'].split('#')[0];assert (site/target).exists(),a['href']
    animation=info['cosineAnimation']
    assert animation['upperLimit']=='1/2' and animation['fixedEndpoint']
    assert animation['xPixelsPerUnit']==animation['yPixelsPerUnit']==300
    assert 2*animation['plotWidthPixels']==animation['plotHeightPixels']
    gif=site/'reading/animations/cosine.gif';assert Image.open(gif).n_frames==6
    assert hashlib.sha256(gif.read_bytes()).hexdigest()==animation['gifSha256']
    for row in animation['frames']+animation['table']:
        assert row==example(row['depth']) and row['upperLimit']=='1/2'
        lo,hi=map(Q,[row['lower'],row['upper']]);pl,ph=map(Q,[row['reciprocalLower'],row['reciprocalUpper']])
        assert max(lo,pl)<=min(hi,ph)
        l,h=map(Q,row['integralDisplay']);assert l<=lo<=hi<=h
    caption=doc('cosine.html').select_one('[data-animation="cosine"] figcaption').text
    assert '1/2' in caption and '1/3' not in caption
    if args.static_only:
        print('PASS: numeric, branding, gallery, protected-artifact and fixed-scale checks; browser not run')
        return
    handler=functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site))
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),handler)
    threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/'
    errors=[]
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts={'headless':True,'args':['--no-sandbox']}
        if exe:opts['executable_path']=exe
        browser=p.chromium.launch(**opts);page=browser.new_page(viewport={'width':1500,'height':1050})
        page.on('pageerror',lambda e:errors.append(str(e)))
        def load(file):
            page.goto(base+file,wait_until='domcontentloaded')
            page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
            page.evaluate('() => MathJax.startup.promise')
            assert page.locator('mjx-merror,[data-mjx-error]').count()==0,file
        load('index.html')
        assert page.locator('h1 em').text_content()=='Analysis'
        assert page.locator('#pi-computations mjx-container').count()==1
        page.screenshot(path=str(out/'home-desktop.png'),full_page=True)
        page.locator('#pi-computations a[href^="ch-foundations"]').click()
        page.wait_for_url('**/ch-foundations.html#pi-computations')
        assert page.locator('.pi-formula-card').count()==10
        page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
        page.evaluate('() => MathJax.startup.promise')
        assert page.locator('#pi-computations mjx-container').count()==10
        assert page.locator('#pi-computations mjx-merror,[data-mjx-error]').count()==0
        page.locator('#pi-computations').screenshot(path=str(out/'chapter-one-catalogue.png'))
        load('pi-computations.html')
        page.emulate_media(reduced_motion='reduce');load('pi-computations.html')
        img=page.locator('[data-animation="cosine"] img')
        page.wait_for_function('document.querySelector("[data-animation=cosine] img").naturalWidth===800')
        assert img.get_attribute('src').endswith('.png')
        page.locator('[data-animation-toggle]').click()
        assert img.get_attribute('src').endswith('.gif')
        for f in ['index.html','pi-computations.html','ch-foundations.html','cosine.html']:
            page.set_viewport_size({'width':390,'height':850});load(f)
            assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2'),f
            if f=='index.html':page.screenshot(path=str(out/'home-mobile.png'),full_page=True)
        page.set_viewport_size({'width':1500,'height':1050});load('cosine.html')
        page.locator('[data-proof-map="thm:c3-primitive"]').click()
        frame=page.frame_locator('#proof-frame')
        frame.locator('[data-node="thm:c3-primitive"]').wait_for(timeout=30000)
        assert frame.locator('[data-route]:visible').count()==4
        assert not errors,errors
        browser.close()
    server.shutdown()
    result=dict(passed=True,documentationRevision=info['documentationRevision'],proofSourceCommit=PROOF_SHA,
       homeTeaser=True,chapterOneCatalogue=10,branding=True,numericBounds=True,equalAxes=True,
       mobile=True,proofMapStillWorks=True,mathRenderingChecked=True,javascriptErrors=errors)
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
if __name__=='__main__':main()
