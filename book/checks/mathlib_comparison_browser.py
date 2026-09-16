#!/usr/bin/env python3
"""Verify every displayed number, expanded Mathlib panels, mobile and embedded maps."""
from pathlib import Path
import functools,http.server,json,shutil,threading
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]

def main():
    site=ROOT/'blueprint/web';out=ROOT/'comparison/reports/mathlib-map-browser';out.mkdir(parents=True,exist_ok=True)
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/'
    expected=json.loads((site/'reading/map-comparison.json').read_text());model=json.loads((site/'reading/maps.json').read_text());errors=[]
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        options={'headless':True,'args':['--no-sandbox']}
        if exe:options['executable_path']=exe
        browser=p.chromium.launch(**options);page=browser.new_page(viewport={'width':1600,'height':1100})
        page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(base+'proof-map.html?theorem=thm:c3-primitive',wait_until='domcontentloaded')
        page.wait_for_selector('[data-node="thm:c3-primitive"]',timeout=30000)
        page.locator('.pm-card').first.wait_for(timeout=30000)
        assert page.locator('.pm-card').count()==3 and page.locator('.pm-card').first.is_visible()
        for case in ['identity','validity','combined']:
            page.select_option('#pm-case',case)
            for baseline in ['full','statement-free','shared-free']:
                page.select_option('#pm-baseline',baseline)
                for route in expected['routeOrder']:
                    card=page.locator('[data-pm-route="'+route+'"]');row=expected['cases'][case]['routes'][route]['costs'][baseline]
                    assert int(card.locator('.pm-declarations').text_content().replace(',',''))==row['declarations']
                    assert int(card.locator('.pm-loc').text_content().replace(',',''))==row['codeLines']
        page.select_option('#pm-case','identity');page.select_option('#pm-baseline','full')
        page.screenshot(path=str(out/'comparison-in-map.png'),full_page=True)
        for route in ['0','1','2','all']:
            page.locator('[data-route="'+route+'"]').click();page.locator('#svg-holder[data-view="'+route+'"]').wait_for()
            assert page.locator('.pm-card').count()==3
            assert bool(page.locator('[data-node="thm:c3-mathlib-ftc"]').count())==(route in ['2','all'])
        for label in ['def:c3-mathlib-nonnegative','def:c3-mathlib-bochner','def:c3-mathlib-interval','thm:c3-mathlib-ftc']:
            page.locator('[data-node="'+label+'"]').dispatch_event('click')
            page.locator('.bundle-lean>summary').click()
            declared=model['bundles'][label]['declarations']
            texts=[d['kind']+' '+d['name']+' : '+d['type']+(' :=\n'+d['value'] if d['value'] is not None else '') for d in declared]
            assert page.locator('.lean-card code').all_text_contents()==texts
            assert page.locator('.lean-card.mathlib').count()==len(texts)
            page.wait_for_function('window.MathJax && typeof MathJax.typesetPromise === "function"',timeout=60000)
            page.evaluate('() => MathJax.typesetPromise([document.querySelector("#map-detail")])')
            assert not page.locator('mjx-merror,[data-mjx-error]').count()
        page.locator('[data-route="2"]').click();page.locator('#svg-holder[data-view="2"]').wait_for()
        page.locator('[data-node="thm:c3-mathlib-ftc"]').dispatch_event('click')
        page.screenshot(path=str(out/'mathlib-ftc.png'),full_page=True)
        page.locator('[data-edge="thm:c3-mathlib-ftc->lem:c3-mftc"]').dispatch_event('click')
        assert page.locator('#map-detail .role').text_content()=='USED IN A PROOF'
        assert 'FTC applied to the sine derivative' in page.locator('#map-detail').text_content()
        page.locator('#pm-more>summary').click();assert 'unmapped' in page.locator('#pm-breakdown').text_content()
        page.screenshot(path=str(out/'source-breakdown.png'),full_page=True)
        page.locator('#pm-more>summary').click();page.set_viewport_size({'width':390,'height':850})
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        assert page.locator('.pm-card').count()==3
        page.screenshot(path=str(out/'comparison-mobile.png'),full_page=True)
        page.locator('#pm-more>summary').click();assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        # The same comparison must be present in the theorem-side iframe.
        page.goto(base+'cosine.html',wait_until='domcontentloaded')
        page.locator('[data-proof-map="thm:c3-primitive"]').click()
        frame=page.frame_locator('#proof-frame');frame.locator('.pm-card').first.wait_for(timeout=30000)
        assert frame.locator('.pm-card').count()==3
        assert not errors,errors
        browser.close()
    server.shutdown();(out/'results.json').write_text(json.dumps({'passed':True,'nineAccountingViews':True,'exactStatements':True,'actualFTCEdge':True,'inlineComparison':True,'mobile':True,'iframe':True,'javascriptErrors':errors},indent=2)+'\n')
    print('PASS: inline numbers in every view, exact Mathlib integral/FTC statements, source coverage, LaTeX, mobile and theorem-side iframe')
if __name__=='__main__':main()
