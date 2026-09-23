#!/usr/bin/env python3
"""Check the final squared-cosine reader, source audit and real browser behavior."""
import argparse, hashlib, json, shutil, threading
from fractions import Fraction as Q
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit
from bs4 import BeautifulSoup
from PIL import Image
from playwright.sync_api import sync_playwright
from cosine_square_edition import row, TITLE, PROOF_SHA

def main():
    p=argparse.ArgumentParser();p.add_argument('--site',type=Path,required=True);p.add_argument('--report',type=Path,required=True);p.add_argument('--static-only',action='store_true')
    args=p.parse_args();site=args.site.resolve();out=args.report;out.mkdir(parents=True,exist_ok=True)
    read=lambda f:json.loads((site/f).read_text())
    record=read('reading/cosine-square-edition.json');audit=read('reading/cosine-square-proofs.json')
    assert record['baseProofRevision']==PROOF_SHA and all(audit['checks'].values())
    for d in audit['declarations']:assert 'sorryAx' not in d['axioms']
    checked={d['name']:d['type'] for d in audit['declarations']}
    assert checked['ComputableAnalysis.CosineSquare.integral_via_symmetry']==checked['ComputableAnalysis.CosineSquare.integral_via_FTC']
    assert 'ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC' not in audit['symmetryClosure']
    assert 'ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC' in audit['ftcClosure']
    assert 'ComputableAnalysis.CosineSquare.symmetry_sum_error' not in audit['ftcClosure']
    for name,h in {**record['protectedArtifacts'],**record['artifacts']}.items():
        assert hashlib.sha256((site/name).read_bytes()).hexdigest()==h,name
    assert all(name.endswith('.html') or name=='reading/maps.json' for name in record['changedArtifacts'])
    doc=BeautifulSoup((site/'cosine.html').read_text(),'html.parser')
    assert doc.h1.get_text()==TITLE and len(doc.select('figure.math-animation'))==2
    assert doc.select_one('#symmetry') and doc.select_one('#ftc') and doc.select_one('#mean-square')
    assert 'first meeting' not in doc.get_text().lower()
    assert '3 checked routes' not in doc.get_text()
    assert not doc.select('[data-proof-map="thm:c3-primitive"]')
    old=BeautifulSoup((site/'cosine-primitive.html').read_text(),'html.parser')
    assert old.h1.get_text()=='The cosine primitive'
    assert old.select('[data-proof-map="thm:c3-primitive"]')
    assert read('reading/maps.json')['theorems']['thm:c3-primitive']['page']=='cosine-primitive.html'
    for f in ['cosine.html','cosine-square-proofs.html']:
        s=BeautifulSoup((site/f).read_text(),'html.parser')
        for a in s.select('a[href]'):
            href=urlsplit(a['href'])
            if not href.scheme and href.path:
                target=site/href.path
                assert target.is_file() or (target/'index.html').is_file(),a['href']
        for a in s.select('article a[href*="github.com"]'):
            assert '/blob/'+record['proofRevision']+'/' in a['href'] or '/blob/'+PROOF_SHA+'/' in a['href']
    for name,key,count in [('cosine-square','rectangleAnimation',4),('cosine-square-symmetry','symmetryAnimation',None)]:
        for ext,sha in record[key]['hashes'].items():
            path=site/'reading/animations'/f'{name}.{ext}'
            assert hashlib.sha256(path.read_bytes()).hexdigest()==sha
            im=Image.open(path);assert im.size==(800,640)
            if ext=='gif':assert im.n_frames==(count or record[key]['frames'])
    assert [r['stage'] for r in record['rectangleAnimation']['frames']]==[1,2,3,4]
    for r in record['illustrationTable']:
        assert r==row(r['stage'])
        lo,hi=Q(r['lower']),Q(r['upper']);a,b=map(Q,r['display'])
        assert a<=lo<=Q(1,4)<=hi<=b
    if args.static_only:
        print('PASS: theorem audit, independent proof closures, literal artifacts, stage values and source links')
        return
    class Quiet(SimpleHTTPRequestHandler):
        def log_message(self,*args):pass
    server=ThreadingHTTPServer(('127.0.0.1',0),partial(Quiet,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start()
    base=f'http://127.0.0.1:{server.server_port}/';errors=[]
    try:
        with sync_playwright() as pw:
            options={'headless':True,'args':['--no-sandbox']}
            exe=shutil.which('google-chrome') or shutil.which('chromium')
            if exe:options['executable_path']=exe
            browser=pw.chromium.launch(**options)
            for width in [1440,768,390,320]:
                page=browser.new_page(viewport={'width':width,'height':1000},reduced_motion='reduce')
                page.on('pageerror',lambda e:errors.append(str(e)))
                for f in ['cosine.html','cosine-square-proofs.html']:
                    page.goto(base+f,wait_until='networkidle')
                    page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
                    page.evaluate('() => MathJax.startup.promise')
                    assert page.locator('mjx-merror,[data-mjx-error]').count()==0,f
                    assert page.locator('article mjx-container').count()>5,f
                    assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2'),(f,width)
                    if f=='cosine.html':
                        for name in ['cosine-square','cosine-square-symmetry']:
                            figure=page.locator(f'[data-animation="{name}"]');img=figure.locator('img')
                            page.wait_for_function('(name)=>document.querySelector(`[data-animation="${name}"] img`).naturalWidth===800',arg=name)
                            assert img.get_attribute('src').endswith('.png')
                            figure.locator('button').click();assert img.get_attribute('src').endswith('.gif')
                            figure.locator('button').click();assert img.get_attribute('src').endswith('.png')
                    else:
                        for route in ['symmetry','ftc']:
                            page.locator(f'[data-square-route="{route}"]').click()
                            assert page.locator('[data-proof-route]:visible').count()==2
                            assert page.locator(f'[data-proof-route="{route}"]:visible').count()==2
                        page.locator('[data-square-route="all"]').click()
                        assert page.locator('[data-proof-route]:visible').count()==4
                    if width in [1440,390]:
                        page.evaluate('window.scrollTo({top:0,behavior:"instant"})')
                        page.screenshot(path=str(out/f'{Path(f).stem}-{width}.png'),full_page=True)
                page.close()
            page=browser.new_page(viewport={'width':390,'height':900})
            page.goto(base+'cosine-square-proofs.html?route=ftc',wait_until='networkidle')
            assert page.locator('[data-proof-route="symmetry"]:visible').count()==0
            page.goto(base+'cosine-primitive.html',wait_until='networkidle')
            page.locator('[data-proof-map="thm:c3-primitive"]').click()
            page.frame_locator('#proof-frame').locator('[data-node="thm:c3-primitive"]').wait_for(timeout=30000)
            browser.close()
    finally:server.shutdown()
    assert not errors,errors
    (out/'cosine-square-browser.json').write_text(json.dumps(dict(passed=True,widths=[1440,768,390,320],mathRendered=True,animationControls=True,proofRoutes=True,oldProofMap=True,revision=record['proofRevision']),indent=2)+'\n')
    print('PASS: desktop/mobile MathJax, both animation controls, proof routes, source links and supporting proof map')

if __name__=='__main__':main()
