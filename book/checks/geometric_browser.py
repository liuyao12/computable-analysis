#!/usr/bin/env python3
"""Exercise inline GIFs, reduced-motion controls and the folded declaration bundle."""
from pathlib import Path
import functools,http.server,json,shutil,threading
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]

def main():
    site=ROOT/'blueprint/web';out=ROOT/'comparison/reports/geometry-browser';out.mkdir(parents=True,exist_ok=True)
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/'
    errors=[]
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts={'headless':True,'args':['--no-sandbox']}
        if exe:opts['executable_path']=exe
        browser=p.chromium.launch(**opts);page=browser.new_page(viewport={'width':1500,'height':1100})
        page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(base+'proof-map.html?theorem=thm:c3-primitive',wait_until='domcontentloaded')
        page.wait_for_selector('[data-node="thm:c3-primitive"]')
        for view in ['all','0','1','2']:
            page.locator('[data-route="'+view+'"]').click();page.locator('#svg-holder[data-view="'+view+'"]').wait_for()
            assert not page.locator('[data-node="lem:c3-inverse"]').count()
            page.locator('[data-node="def:c3-trig"]').dispatch_event('click')
            assert page.locator('#map-detail h2').text_content()=='Sine and cosine'
            page.locator('.bundle-lean>summary').click()
            assert page.locator('.lean-card').count()==37
            assert 'ClosedArctanInverse' in page.locator('.lean-card code').first.text_content()
        for label,name in [('def:c3-arctan','arctan'),('def:c3-integrals','concave')]:
            page.locator('[data-node="'+label+'"]').dispatch_event('click')
            img=page.locator('.math-animation img');img.wait_for()
            page.wait_for_function("document.querySelector('.math-animation img').naturalWidth === 800")
            assert img.get_attribute('src').endswith(name+'.gif')
            toggle=page.locator('.math-animation button');toggle.click()
            assert img.get_attribute('src').endswith(name+'.png')
            toggle.click();assert img.get_attribute('src').endswith(name+'.gif')
            page.wait_for_timeout(700)
            page.screenshot(path=str(out/(name+'-panel.png')),full_page=True)
        page.locator('.formal-boundary>summary').click()
        assert 'not yet been formalized' in page.locator('.formal-boundary').text_content()
        page.emulate_media(reduced_motion='reduce')
        page.locator('[data-node="def:c3-arctan"]').dispatch_event('click')
        assert page.locator('.math-animation img').get_attribute('src').endswith('.png')
        page.set_viewport_size({'width':390,'height':850})
        assert page.evaluate('document.documentElement.scrollWidth <= innerWidth+2')
        page.screenshot(path=str(out/'mobile-arctan.png'),full_page=True)
        page.goto(base+'cosine.html',wait_until='domcontentloaded');page.wait_for_selector('[data-animation]')
        assert page.locator('[data-animation] img').get_attribute('src').endswith('.png')
        page.locator('[data-animation-toggle]').click()
        assert page.locator('[data-animation] img').get_attribute('src').endswith('.gif')
        assert not errors,errors
        browser.close()
    server.shutdown();(out/'results.json').write_text(json.dumps({'passed':True,'realGifs':2,'inverseFolded':True,'exactDeclarations':37,'reducedMotion':True,'mobile':True,'formalizationBoundaryVisible':True,'javascriptErrors':errors},indent=2)+'\n')
    print('PASS: geometric GIFs and static posters, pause/play, reduced motion, inverse bundle, explicit status, and mobile')
if __name__=='__main__':main()
