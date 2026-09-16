#!/usr/bin/env python3
"""Exercise the revised map and all proof-route/validity distinctions."""
from pathlib import Path
import functools,http.server,json,shutil,threading
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]

def main():
    site=ROOT/'blueprint/web';out=ROOT/'comparison/reports/schedule-browser';out.mkdir(parents=True,exist_ok=True)
    handler=functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site))
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),handler)
    threading.Thread(target=server.serve_forever,daemon=True).start()
    base=f'http://127.0.0.1:{server.server_port}/';errors=[]
    model=json.loads((site/'reading/maps.json').read_text())
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts={'headless':True,'args':['--no-sandbox']}
        if exe:opts['executable_path']=exe
        browser=p.chromium.launch(**opts);page=browser.new_page(viewport={'width':1600,'height':1100})
        page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(base+'proof-map.html?theorem=thm:c3-primitive',wait_until='domcontentloaded')
        page.wait_for_selector('[data-node="thm:c3-primitive"]')
        for route in ['all','0','1','2','all']:
            page.locator('[data-route="'+route+'"]').click()
            page.locator('#svg-holder[data-view="'+route+'"]').wait_for()
            assert page.locator('#map-detail h2').text_content()=='Cosine primitive'
            assert page.locator('[data-edge-kind="statement"]').count()==4
            assert page.locator('[data-node="lem:c3-construction-valid"]').count()==1
            if route=='2':assert not page.locator('[data-edge="lem:c3-construction-valid->thm:c3-primitive"]').count()
        page.screenshot(path=str(out/'proof-structure.png'),full_page=True)
        for label in ['def:c3-integrals','def:c3-integral','lem:c3-construction-valid','lem:c3-endpoint-representation']:
            page.locator('[data-node="'+label+'"]').dispatch_event('click')
            page.locator('.bundle-lean>summary').click()
            expected=[d['kind']+' '+d['name']+' : '+d['type']+(' :=\n'+d['value'] if d.get('value') is not None else '') for d in model['bundles'][label]['declarations']]
            assert page.locator('.lean-card code').all_text_contents()==expected
        page.locator('[data-node="def:c3-integrals"]').dispatch_event('click')
        page.wait_for_function('window.MathJax && typeof MathJax.typesetPromise === "function"',timeout=60000)
        page.evaluate('() => MathJax.typesetPromise([document.querySelector("#map-detail")])')
        assert not page.locator('mjx-merror,[data-mjx-error]').count()
        page.screenshot(path=str(out/'schedule-construction.png'),full_page=True)
        page.set_viewport_size({'width':390,'height':850})
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        page.locator('[data-route="2"]').click();page.locator('#svg-holder[data-view="2"]').wait_for()
        page.screenshot(path=str(out/'map-mobile.png'),full_page=True)
        page.goto(base+'cosine.html',wait_until='domcontentloaded')
        page.locator('#the-chosen-schedule').wait_for()
        page.wait_for_selector('mjx-container',timeout=60000)
        assert not page.locator('mjx-merror,[data-mjx-error]').count()
        assert not errors,errors
        browser.close()
    server.shutdown();(out/'results.json').write_text(json.dumps({'passed':True,'allRouteViews':True,'validityNotFalselyUsedByMathlib':True,'exactLeanDeclarations':True,'mobile':True,'errors':errors},indent=2)+'\n')
    print('PASS: revised mathematical map, exact grouped statements, actual route dependencies, MathJax and mobile')
if __name__=='__main__':main()
