#!/usr/bin/env python3
"""Exercise all new maps/measurements; --mathjax-root uses local MathJax in offline CI."""
from pathlib import Path
import argparse,functools,http.server,json,shutil,threading
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]
TARGETS=['thm:wallis-integrals','thm:wallis-product','thm:beta-integral','thm:beta-normalization']

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--mathjax-root',type=Path);args=ap.parse_args()
    site=ROOT/'blueprint/web';out=ROOT/'comparison/reports/integral-portfolio-browser';out.mkdir(parents=True,exist_ok=True)
    maps=json.loads((site/'reading/maps.json').read_text());stats=json.loads((site/'reading/integral-portfolio-comparison.json').read_text())
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/';errors=[];views=0;cards=0
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts={'headless':True,'args':['--no-sandbox']}
        if exe:opts['executable_path']=exe
        browser=p.chromium.launch(**opts);page=browser.new_page(viewport={'width':1600,'height':1100})
        page.on('pageerror',lambda e:errors.append(str(e)))
        if args.mathjax_root:
            def local(route):
                url=route.request.url;rel=url.split('/es5/',1)[1].split('?',1)[0]
                file=args.mathjax_root/rel
                if file.is_file():route.fulfill(path=str(file))
                else:route.abort()
            page.route('https://cdn.jsdelivr.net/npm/mathjax@3/es5/**',local)
        for target in TARGETS:
            page.goto(base+'proof-map.html?theorem='+target,wait_until='domcontentloaded')
            page.locator('[data-node="'+target+'"]').wait_for(timeout=30000);page.locator('.pm-card').first.wait_for()
            assert page.locator('.pm-card').count()==2 and page.locator('[data-route]:visible').count()==3
            # All eight obligations and four accounting baselines: 32 views.
            if target==TARGETS[0]:
                for c in stats['cases']:
                    page.select_option('#pm-case',c)
                    for baseline in ['full','statement-free','shared-free','after-cartwright']:
                        page.select_option('#pm-baseline',baseline)
                        for r in stats['routeOrder']:
                            card=page.locator('[data-pm-route="'+r+'"]');expected=stats['cases'][c]['routes'][r]['costs'][baseline]
                            assert int(card.locator('.pm-declarations').text_content().replace(',',''))==expected['declarations']
                            assert int(card.locator('.pm-loc').text_content().replace(',',''))==expected['codeLines']
                        views+=1
            page.select_option('#pm-case',maps['theorems'][target]['comparison']['defaultCase']);page.select_option('#pm-baseline','full')
            for route in ['1','2','all']:
                page.locator('[data-route="'+route+'"]').click();page.locator('#svg-holder[data-view="'+route+'"]').wait_for()
                assert page.locator('[data-node="'+target+'"]').count()==1
                if route=='1':assert page.locator('[data-node^="ip:mathlib"]').count()==0
                if route=='2':assert page.locator('[data-node="ip:mathlib-ftc"]').count()==1
            for label in [e.get_attribute('data-node') for e in page.locator('[data-node]').all()]:
                page.locator('[data-node="'+label+'"]').dispatch_event('click')
                page.locator('.bundle-lean>summary').click()
                exact=maps['bundles'][label]['declarations'];cards+=len(exact)
                expected=[d['kind']+' '+d['name']+' : '+d['type']+(' :=\n'+d['value'] if d.get('value') is not None else '') for d in exact]
                assert page.locator('.lean-card code').all_text_contents()==expected
                page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
                page.evaluate('() => MathJax.startup.promise.then(() => MathJax.typesetPromise([document.querySelector("#map-detail")]))')
                assert not page.locator('mjx-merror,[data-mjx-error]').count(),label
            page.locator('[data-node="'+target+'"]').dispatch_event('click')
            page.screenshot(path=str(out/(target.split(':')[1]+'.png')),full_page=True)
        page.goto(base+'integral-families.html',wait_until='domcontentloaded')
        page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
        page.evaluate('() => MathJax.startup.promise')
        assert not page.locator('mjx-merror,[data-mjx-error]').count()
        page.screenshot(path=str(out/'chapter.png'),full_page=True)
        page.locator('[data-proof-map="thm:beta-integral"]').click()
        frame=page.frame_locator('#proof-frame');frame.locator('[data-node="thm:beta-integral"]').wait_for()
        assert frame.locator('.pm-card').count()==2
        page.locator('#close-proof').click()
        page.set_viewport_size({'width':390,'height':850});page.goto(base+'integral-families.html',wait_until='domcontentloaded')
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        page.screenshot(path=str(out/'chapter-mobile.png'),full_page=True)
        page.goto(base+'proof-map.html?theorem=thm:wallis-product',wait_until='domcontentloaded')
        page.locator('[data-node="thm:wallis-product"]').wait_for();page.locator('.pm-card').first.wait_for()
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        page.screenshot(path=str(out/'map-mobile.png'),full_page=True)
        assert not errors,errors
        browser.close()
    server.shutdown();(out/'results.json').write_text(json.dumps(dict(passed=True,accountingViews=views,routeViews=12,
        exactDeclarationCardOccurrences=cards,allNodeMathRendered=True,chapterRendered=True,theoremIframe=True,mobile=True,javascriptErrors=errors),indent=2)+'\n')
    print('PASS: four maps, 32 accounting views, twelve route views, exact Lean cards, all mathematical panels, chapter, iframe and mobile')
if __name__=='__main__':main()
