#!/usr/bin/env python3
"""Verify completed proof maps and measurements in a browser.

--offline tests interactions without external MathJax; mathematical rendering
is then checked separately on the self-contained preview. The normal CI mode
requires MathJax and checks its completed rendering rather than guessing from
an element appearing while typesetting is still running.
"""
from __future__ import annotations
from pathlib import Path
import argparse, functools, http.server, json, shutil, threading
from playwright.sync_api import sync_playwright
ROOT = Path(__file__).resolve().parents[2]
TARGETS = ['thm:cartwright-moments', 'thm:cartwright-irrationality']

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--offline',action='store_true');args=ap.parse_args()
    site=ROOT/'blueprint/web';out=ROOT/'comparison/reports/cartwright-browser';out.mkdir(parents=True,exist_ok=True)
    model=json.loads((site/'reading/maps.json').read_text())
    metrics=json.loads((site/'reading/cartwright-comparison.json').read_text())
    handler=functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site))
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),handler)
    threading.Thread(target=server.serve_forever,daemon=True).start()
    base=f'http://127.0.0.1:{server.server_port}/';errors=[];combinations=0
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts={'headless':True,'args':['--no-sandbox']}
        if exe:opts['executable_path']=exe
        browser=p.chromium.launch(**opts)
        page=browser.new_page(viewport={'width':1600,'height':1100})
        page.on('pageerror',lambda e:errors.append(str(e)))
        if args.offline:page.route('https://cdn.jsdelivr.net/**',lambda r:r.abort())
        for target in TARGETS:
            page.goto(base+'proof-map.html?theorem='+target,wait_until='domcontentloaded')
            page.locator('[data-node="'+target+'"]').wait_for(timeout=30000)
            page.locator('.pm-card').first.wait_for()
            assert page.locator('.pm-card').count()==3
            for case in ['laws','moments','irrationality']:
                page.select_option('#pm-case',case)
                for baseline in ['full','statement-free','shared-free','after-cosine']:
                    page.select_option('#pm-baseline',baseline)
                    for route in metrics['routeOrder']:
                        card=page.locator('[data-pm-route="'+route+'"]')
                        got=lambda selector:int(card.locator(selector).text_content().replace(',',''))
                        expected=metrics['cases'][case]['routes'][route]['costs'][baseline]
                        assert got('.pm-declarations')==expected['declarations']
                        assert got('.pm-loc')==expected['codeLines']
                    combinations+=1
            for route in ['0','1','2','all']:
                page.locator('[data-route="'+route+'"]').click()
                page.locator('#svg-holder[data-view="'+route+'"]').wait_for()
                assert page.locator('[data-node="'+target+'"]').count()==1
                if route in ['0','1']:assert not page.locator('[data-node^="cw:mathlib"]').count()
                if route=='2':assert page.locator('[data-node="cw:mathlib-ftc"]').count()==1
            page.select_option('#pm-case','moments' if target==TARGETS[0] else 'irrationality')
            page.select_option('#pm-baseline','full')
            for label in ['cw:laws','cw:ftc','cw:bridge',target]:
                page.locator('[data-node="'+label+'"]').dispatch_event('click')
                page.locator('.bundle-lean>summary').click()
                expected=[d['kind']+' '+d['name']+' : '+d['type']+(' :=\n'+d['value'] if d.get('value') is not None else '')
                          for d in model['bundles'][label]['declarations']]
                assert page.locator('.lean-card code').all_text_contents()==expected
                if not args.offline:
                    page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
                    page.evaluate('() => MathJax.startup.promise.then(() => MathJax.typesetPromise([document.querySelector("#map-detail")]))')
                    assert not page.locator('mjx-merror,[data-mjx-error]').count()
            page.locator('[data-node="'+target+'"]').dispatch_event('click')
            page.screenshot(path=str(out/(target.split(':')[1]+'.png')),full_page=True)
        page.goto(base+'proof-map.html?theorem=thm:cartwright-plan',wait_until='domcontentloaded')
        page.locator('[data-node="thm:cartwright-irrationality"]').wait_for()
        assert 'planned' not in page.locator('#map-subtitle').text_content().lower()
        page.set_viewport_size({'width':390,'height':850})
        assert page.evaluate('document.documentElement.scrollWidth <= innerWidth+2')
        page.screenshot(path=str(out/'cartwright-mobile.png'),full_page=True)
        # Existing cosine report still mounts with its original default controls.
        page.goto(base+'proof-map.html?theorem=thm:c3-primitive',wait_until='domcontentloaded')
        page.locator('[data-node="thm:c3-primitive"]').wait_for();page.locator('.pm-card').first.wait_for()
        assert page.input_value('#pm-case')=='identity'
        assert page.locator('.pm-card').count()==3
        page.goto(base+'cartwright.html',wait_until='domcontentloaded')
        assert page.locator('[data-proof-map]').count()==2
        for target in TARGETS:
            page.locator('[data-proof-map="'+target+'"]').click()
            frame=page.frame_locator('#proof-frame')
            frame.locator('[data-node="'+target+'"]').wait_for()
            frame.locator('.pm-card').first.wait_for()
            assert frame.locator('.pm-card').count()==3
            page.locator('#close-proof').click()
        assert page.evaluate('document.documentElement.scrollWidth <= innerWidth+2')
        assert not errors,errors
        browser.close()
    server.shutdown()
    result={'passed':True,'accountingViews':combinations,'pairedStatements':2,'exactLeanCards':True,
        'oldCosineComparisonPreserved':True,'arithmeticPlanAliasCompleted':True,
        'desktop':True,'mobile':True,'theoremIframes':True,'javascriptErrors':errors,
        'mathjaxExternalRenderingChecked':not args.offline,'offlineInteractionMode':args.offline}
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: completed paired proof maps, exact code, all accounting views, native isolation, old cosine comparison, mobile and theorem iframes')
if __name__=='__main__':main()
