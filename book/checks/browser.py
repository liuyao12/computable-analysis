#!/usr/bin/env python3
"""Real browser checks of the book, margin links and mathematical graph panels."""
from __future__ import annotations
from pathlib import Path
import functools,http.server,json,shutil,threading
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]

def main():
    site=ROOT/'blueprint/web';reports=ROOT/'comparison/reports/book-browser';reports.mkdir(exist_ok=True,parents=True)
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/'
    errors=[]
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts={'headless':True,'args':['--no-sandbox']}
        if exe:opts['executable_path']=exe
        browser=p.chromium.launch(**opts);page=browser.new_page(viewport={'width':1500,'height':1100})
        page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(base,wait_until='domcontentloaded');page.wait_for_selector('article .chapter-pair')
        page.screenshot(path=str(reports/'book-desktop.png'),full_page=True)
        chapters = [f.name for f in site.glob('ch-*.html') if 'class="reader"' in f.read_text()] + ['cosine.html']
        for chapter in chapters:
            page.goto(base+chapter,wait_until='domcontentloaded')
            page.wait_for_function("window.MathJax && window.MathJax.startup && window.MathJax.startup.promise",timeout=60000)
            page.evaluate("() => MathJax.startup.promise")
            page.wait_for_selector('mjx-container',timeout=60000)
            assert page.locator('mjx-merror,[data-mjx-error]').count()==0,chapter
            if chapter in ['ch-foundations.html','ch-circle-sphere.html','cosine.html']:
                assert page.locator('[data-proof-map]').count()>=1
        link=page.locator('[data-proof-map="thm:c3-primitive"]');link.scroll_into_view_if_needed();link.click()
        page.locator('#proof-dialog').wait_for(state='visible')
        frame=page.frame_locator('#proof-frame');frame.locator('[data-node="thm:c3-primitive"]').wait_for(timeout=30000)
        assert frame.locator('.bundle-lean').get_attribute('open') is None
        assert frame.locator('#map-detail .math-body').count()==1
        frame.locator('.bundle-lean>summary').click()
        assert frame.locator('.lean-card').count()>=4
        exported=json.loads((site/'reading/maps.json').read_text())['bundles']['thm:c3-primitive']['declarations']
        expected=[d['kind']+' '+d['name']+' : '+d['type']+(' :=\n'+d['value'] if d.get('value') is not None else '') for d in exported]
        assert frame.locator('.lean-card code').all_text_contents()==expected
        for route in ['0','1','2','all']:
            frame.locator('[data-route="'+route+'"]').click()
            frame.locator('#svg-holder[data-view="'+route+'"]').wait_for()
            frame.locator('[data-node="thm:c3-primitive"]').wait_for(timeout=30000)
            assert frame.locator('[data-node="thm:c3-primitive"]').count()==1
        page.screenshot(path=str(reports/'theorem-map.png'),full_page=True)
        page.locator('#close-proof').click();assert not page.locator('#proof-dialog').is_visible()
        page.goto(base+'ch-foundations.html',wait_until='domcontentloaded');page.locator('[data-proof-map]').first.click()
        frame=page.frame_locator('#proof-frame');frame.locator('[data-node="conclusion"]').wait_for()
        assert 'not registered' in frame.locator('#map-subtitle').text_content()
        assert frame.locator('[data-route]:visible').count()==0
        page.locator('#close-proof').click()
        page.set_viewport_size({'width':390,'height':850});page.goto(base+'cosine.html',wait_until='domcontentloaded')
        page.wait_for_selector('mjx-container',timeout=60000)
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        page.locator('#menu-button').click();assert page.locator('#book-nav').is_visible();page.locator('#menu-button').click()
        page.screenshot(path=str(reports/'book-mobile.png'),full_page=True)
        page.locator('[data-proof-map]').click();frame=page.frame_locator('#proof-frame');frame.locator('[data-node="thm:c3-primitive"]').wait_for()
        frame.locator('[data-route="2"]').click();frame.locator('[data-node="thm:c3-primitive"]').wait_for()
        page.screenshot(path=str(reports/'map-mobile.png'),full_page=True)
        page.locator('#close-proof').click()
        page.goto(base+'cosine-primitive-graph.html',wait_until='domcontentloaded');page.wait_for_url('**/proof-map.html?theorem=thm:c3-primitive')
        assert not errors,errors
        browser.close()
    server.shutdown();(reports/'results.json').write_text(json.dumps({'passed':True,'errors':errors,'desktop':True,'mobile':True,'preservedChapterRendering':True,'exactLeanText':True,'theoremMarginMaps':True,'threeRoutes':True},indent=2))
    print('PASS: book navigation, mathematical rendering, theorem margin maps, all three routes, exact optional Lean text, editorial status, mobile, and old bookmarks')
if __name__=='__main__':main()
