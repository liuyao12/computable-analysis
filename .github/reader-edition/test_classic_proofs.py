#!/usr/bin/env python3
"""Test published navigation, preserved proof data and source-linked comparisons."""
import argparse,hashlib,json,re,shutil,threading
from functools import partial
from http.server import SimpleHTTPRequestHandler,ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright
from classic_proofs import LINKS,MATHLIB,MATHLIB_HASH,EULER_MATHLIB,SHOWCASE_PAGES

def main():
    p=argparse.ArgumentParser();p.add_argument('--site',required=True,type=Path);p.add_argument('--report',required=True,type=Path);p.add_argument('--static-only',action='store_true');a=p.parse_args()
    site=a.site.resolve();a.report.mkdir(parents=True,exist_ok=True)
    report=json.loads((site/'reading/classic-proofs-edition.json').read_text())
    assert all(report['checks'].values()) and report['newLeanProofsClaimed']
    assert report['mathlib']['revision']==MATHLIB and report['mathlib']['sha256']==MATHLIB_HASH
    for name,digest in {**report['protectedArtifacts'],**report['artifacts']}.items():
        assert hashlib.sha256((site/name).read_bytes()).hexdigest()==digest,name
    for name in report['navigationPages']:
        doc=BeautifulSoup((site/name).read_text(),'html.parser');nav=doc.select_one('#book-nav')
        for href,label in LINKS:
            matches=[el for el in nav.select('a[href]') if el['href'] in [href,'../'+href]]
            assert len(matches)==1 and matches[0].get_text()==label,(name,href)
            assert (site/name).parent.joinpath(matches[0]['href']).resolve().is_file(),(name,href)
        assert 'Worked examples' in nav.get_text()
    for name in [href for href,_ in LINKS]:
        doc=BeautifulSoup((site/name).read_text(),'html.parser')
        assert len(doc.select('#book-nav a.current'))==1
        assert doc.select_one('#book-nav a.current')['href']==name
        for el in doc.select('article a[href]'):
            u=urlsplit(el['href'])
            if not u.scheme and u.path:
                target=site/u.path
                assert target.is_file() or (target/'index.html').is_file(),el['href']
    assert report['pages']==SHOWCASE_PAGES
    for name in SHOWCASE_PAGES:
        doc=BeautifulSoup((site/name).read_text(),'html.parser')
        headings=doc.article.select('h2[id]')
        assert [h['id'] for h in headings[:2]]==['setup','theorem'],name
        statements=doc.select('.showcase-statement:not(.secondary-statement)')
        assert len(statements)==1 and statements[0].select_one('p'),name
        assert len(statements[0].get_text().split())>=25,name
        assert not statements[0].select('code,sup,sub'),name
        ids=[node['id'] for node in doc.select('[id]')]
        assert len(ids)==len(set(ids)),(name,'duplicate anchors')
        for anchor in ['setup','theorem']:
            assert doc.select_one(f'.on-this-page a[href="#{anchor}"]'),(name,anchor)
    for name in ['fuchs.html','painleve.html']:
        doc=BeautifulSoup((site/name).read_text(),'html.parser')
        assert 'Differential equations' in doc.select_one('#book-nav').get_text()
        assert doc.select_one('#theorem') and doc.select_one('#checked') and doc.select_one('#nearby')
        assert 'Remaining scope:' in doc.article.get_text()
        assert not re.search(r'<(?:sup|sub)\b',str(doc.article))
    assert 'do not prove the global Painlevé property' in (site/'painleve.html').read_text()
    cart=json.loads((site/'reading/cartwright-audit.json').read_text())
    assert cart['finalIrrationalityProved'] and all(cart['checks'].values())
    zeta=json.loads((site/'reading/zeta-real-edition.json').read_text())
    assert zeta['piSquaredIrrationalityPublished'] and not zeta['piSquaredIrrationalityIntegrated']
    basel=BeautifulSoup((site/'basel.html').read_text(),'html.parser')
    assert len(basel.select('[data-classic-proof]'))==6
    assert 'hasSum_zeta_two' in basel.get_text()
    assert not re.search(r'<(?:sup|sub)\b',(site/'basel.html').read_text())
    euler=json.loads((site/'reading/euler-proofs.json').read_text())
    assert euler['mathlibRevision']==EULER_MATHLIB and all(euler['checks'].values())
    assert len(euler['declarations'])==15 and euler['allPositiveEvenValuesProved']
    deps=(site/'reading/euler-dependencies.txt').read_text().splitlines()
    assert len(deps)==euler['dependencyCount']
    assert 'Real.tendsto_euler_sin_prod' in deps and 'EulerBasel.coefficient_error' in deps
    assert not any('hasSum_zeta' in name or 'bernoulliFourier' in name for name in deps)
    general=(site/'reading/euler-general-dependencies.txt').read_text().splitlines()
    assert len(general)==euler['generalDependencyCount']
    for required in ['EulerEven.hasSum_even_zeta','EulerEven.doubleTerm_summable','EulerEven.cotangentSeries_eq_bernoulli','Complex.tendsto_euler_sin_prod','tendsto_logDeriv_euler_sin_div']:
        assert required in general,required
    assert 'EulerBasel.total_eq' not in general
    assert not any('fourier' in name.lower() or 'hasSum_zeta' in name for name in general)
    euler_page=BeautifulSoup((site/'euler.html').read_text(),'html.parser')
    assert euler_page.select_one('#even-values') and euler_page.select_one('#bernoulli') and euler_page.select_one('#examples')
    assert 'hasSum_even_zeta' in euler_page.get_text()
    assert 'euler.html' in (site/'basel.html').read_text()
    assert not re.search(r'<(?:sup|sub)\b',(site/'euler.html').read_text())
    if a.static_only:
        print('PASS: showcase sidebar entries, active state, source links, preserved audits and honest theorem status');return
    class Quiet(SimpleHTTPRequestHandler):
        def log_message(self,*args):pass
    server=ThreadingHTTPServer(('127.0.0.1',0),partial(Quiet,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/';errors=[]
    try:
        with sync_playwright() as pw:
            opts=dict(headless=True,args=['--no-sandbox']);exe=shutil.which('google-chrome') or shutil.which('chromium')
            if exe:opts['executable_path']=exe
            browser=pw.chromium.launch(**opts)
            for width in [1440,390,320]:
                page=browser.new_page(viewport={'width':width,'height':1000});page.on('pageerror',lambda e:errors.append(str(e)))
                for name in SHOWCASE_PAGES:
                    page.goto(base+name,wait_until='networkidle');page.evaluate('() => MathJax.startup.promise')
                    assert page.locator('mjx-merror,[data-mjx-error]').count()==0,(name,width)
                    assert page.locator('.showcase-statement mjx-container').count()>0,(name,'statement math')
                    assert page.locator('#book-nav a[href="cartwright.html"] mjx-container').count()==1,(name,'navigation math')
                    assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2'),(name,width)
                    if name=='complex-analysis.html':
                        assert page.locator('.cauchy-example').count()==1
                        if width==1440:
                            reader=page.locator('main.reader').bounding_box()
                            example=page.locator('.cauchy-example').bounding_box()
                            assert example['x']>=reader['x']+reader['width'],(name,'side panel')
                        else:
                            assert page.locator('article > .cauchy-example').count()==1
                        for mode in ['coefficients','triangles','contour','solutions']:
                            page.locator(f'[data-example-view="{mode}"]').click()
                            page.wait_for_function('(m)=>document.querySelector(".cauchy-example").dataset.mode===m',arg=mode)
                            page.wait_for_function('document.querySelectorAll("#example-readout mjx-container").length>0')
                            assert page.locator('mjx-merror,[data-mjx-error]').count()==0,(name,mode)
                        page.locator('#example-circuit').evaluate('(e)=>{e.value="100";e.dispatchEvent(new Event("input",{bubbles:true}));}')
                        page.wait_for_function('document.querySelector("#circuit-label").textContent==="100%"')
                        vals=page.evaluate("""() => {
                          const a=window.CauchyExample;
                          const f=z=>({x:z.x/(z.x*z.x+z.y*z.y),y:-z.y/(z.x*z.x+z.y*z.y)});
                          const small=a.quadrature(a.square(.25),32,f);
                          const large=a.quadrature(a.square(1.5),32,f);
                          const reversed=a.quadrature(a.square(1).reverse(),32,f);
                          return {small,large,reversed,j:a.bessel({x:1,y:0}).j,half:a.continuedArgument({x:-1,y:0},-1,.5),full:a.continuedArgument({x:1,y:0},-1,1)};
                        }""")
                        assert abs(vals['half']+3.141592653589793)<1e-12 and abs(vals['full']+2*3.141592653589793)<1e-12
                        assert abs(vals['small']['y']-vals['large']['y'])<1e-12
                        assert abs(vals['small']['y']+vals['reversed']['y'])<1e-12
                        assert abs(vals['small']['y']-2*3.141592653589793)<.001
                        assert abs(vals['j']['x']-.7651976865579666)<1e-12 and abs(vals['j']['y'])<1e-12
                        page.locator('[data-example-view="coefficients"]').click()
                    if name=='basel.html':
                        for route in ['native','mathlib']:
                            page.locator(f'[data-classic-route="{route}"]').click()
                            assert page.locator('[data-classic-proof]:visible').count()==3
                            assert page.locator(f'[data-classic-proof="{route}"]:visible').count()==3
                        page.locator('[data-classic-route="all"]').click();assert page.locator('[data-classic-proof]:visible').count()==6
                    if width in [1440,390] and name!='cosine.html':
                        page.evaluate('window.scrollTo({top:0,behavior:"instant"})');page.screenshot(path=str(a.report/f'classics-{Path(name).stem}-{width}.png'),full_page=True)
                page.close()
            page=browser.new_page(viewport={'width':1440,'height':1000})
            page.goto(base+'basel.html?route=mathlib',wait_until='networkidle');assert page.locator('[data-classic-proof="native"]:visible').count()==0
            page.goto(base+'cartwright.html',wait_until='networkidle')
            page.locator('[data-proof-map="thm:cartwright-irrationality"]').click()
            page.frame_locator('#proof-frame').locator('[data-node="thm:cartwright-irrationality"]').wait_for(timeout=30000)
            page.goto(base+'leibniz-proofs.html',wait_until='networkidle')
            assert page.locator('body').inner_text().count('Mathlib')>0
            browser.close()
    finally:server.shutdown()
    assert not errors,errors
    (a.report/'classic-proofs-browser.json').write_text(json.dumps(dict(passed=True,revision=report['documentationRevision'],widths=[1440,390,320],navigationMath=True,baselRoutes=True,eulerAudited=True,cartwrightViewer=True,leibnizViewerPreserved=True),indent=2)+'\n')
    print('PASS: desktop/mobile navigation, LaTeX, Basel route controls and preserved Cartwright/Leibniz viewers')
if __name__=='__main__':main()
