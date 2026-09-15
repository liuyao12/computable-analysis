#!/usr/bin/env python3
"""Browser regressions for standard blueprint boxes and route-sensitive Real fills."""
from __future__ import annotations
import argparse, functools, http.server, json, shutil, threading
from pathlib import Path
from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[2]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--site',type=Path,default=ROOT/'blueprint/web')
    parser.add_argument('--screenshots',type=Path,default=ROOT/'comparison/reports/browser')
    args=parser.parse_args(); args.screenshots.mkdir(parents=True,exist_ok=True)
    source=json.loads((args.site/'three-proofs/node-details.json').read_text())
    handler=functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(args.site.resolve()))
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),handler)
    threading.Thread(target=server.serve_forever,daemon=True).start()
    errors=[]
    with sync_playwright() as p:
        executable=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        kwargs={'headless':True,'args':['--no-sandbox']}
        if executable:kwargs['executable_path']=executable
        browser=p.chromium.launch(**kwargs)
        page=browser.new_page(viewport={'width':1440,'height':1100})
        page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(f'http://127.0.0.1:{server.server_port}/cosine-primitive-graph.html',wait_until='domcontentloaded')
        page.wait_for_function("document.querySelectorAll('#graph .node').length===16",timeout=60000)
        page.wait_for_function("document.querySelectorAll('#graph .node[data-foundation]').length===16")
        def node(label):return page.locator('#graph .node').filter(has=page.locator('title',has_text=label))
        def target():return node('thm:c3-primitive')
        # Native and bridge nodes are classified by actual transitive Real use.
        for label,detail in source.items():
            if label=='lem:c3-native-exp':continue
            assert node(label).get_attribute('data-foundation')==detail['classification'],label
        assert page.locator('#graph .node[data-foundation="mathlib"]').count()==6
        assert target().get_attribute('data-foundation')=='mixed'
        page.screenshot(path=str(args.screenshots/'dependency-backgrounds.png'),full_page=True)
        # Every visible mathematical node must display a real Lean declaration.
        for label in source:
            if label=='lem:c3-native-exp':continue
            node(label).click()
            modal=page.locator('[id="'+label+'_modal"]')
            modal.wait_for(state='visible')
            assert modal.get_attribute('role')=='dialog'
            assert modal.locator('.bp-lean-code code').inner_text().strip()
            assert modal.locator('.thm_thmcontent').is_visible()
            assert modal.locator('.bp-formal-source').get_attribute('href').startswith('https://github.com/')
            page.keyboard.press('Escape')
            assert not modal.is_visible()
        target().focus();page.keyboard.press('Enter')
        modal=page.locator('[id="thm:c3-primitive_modal"]')
        assert 'CosinePrimitive.Statement' in modal.locator('.bp-lean-code').inner_text()
        assert 'Equiv' in modal.locator('.bp-lean-code').inner_text()
        select=modal.locator('select[aria-label="Lean declaration"]')
        for name in ['viaInequalities','viaFTC','viaMathlib']:
            select.select_option('ComputableAnalysis.CosinePrimitive.'+name)
            assert name in modal.locator('.bp-lean-code').inner_text()
        select.select_option('ComputableAnalysis.CosinePrimitive.Statement')
        page.screenshot(path=str(args.screenshots/'lean-statement-box.png'),full_page=True)
        modal.locator('.dep-closebtn').click();assert not modal.is_visible()
        # The shared conclusion does NOT force the native routes to be shaded.
        for route,count,status in [('0',8,'native'),('1',9,'native'),('2',13,'mathlib'),('all',16,'mixed'),('companions',17,'mixed')]:
            page.locator('[data-view="'+route+'"]').click()
            page.wait_for_function('(n)=>document.querySelectorAll("#graph .node").length===n',arg=count,timeout=30000)
            page.wait_for_timeout(150)
            assert target().get_attribute('data-foundation')==status,(route,status)
            if route in ['0','1']:
                assert page.locator('#graph .node[data-foundation="mathlib"]').count()==0
            if route=='companions':assert node('lem:c3-native-exp').get_attribute('data-foundation')=='native'
        page.locator('[data-view="all"]').click()
        page.wait_for_function("document.querySelectorAll('#graph .node').length===16")
        page.set_viewport_size({'width':390,'height':850})
        page.reload(wait_until='domcontentloaded')
        page.wait_for_function("document.querySelectorAll('#graph .node[data-foundation]').length===16",timeout=60000)
        target().click();modal.wait_for(state='visible')
        assert modal.locator('.bp-lean-code').is_visible()
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        bounds=modal.locator('.dep-modal-content').bounding_box()
        assert bounds['x']>=0 and bounds['x']+bounds['width']<=392
        page.screenshot(path=str(args.screenshots/'mobile-statement-box.png'),full_page=True)
        assert not errors,errors
        browser.close()
    server.shutdown()
    (args.screenshots/'results.json').write_text(json.dumps({'passed':True,'javascriptErrors':errors,
        'checked':'all node statements; source links; mathematical text; proof selector; native/Mathlib/mixed fills; keyboard/close; mobile'},indent=2))
    print('PASS: Lean statement boxes, precise Real backgrounds, route-sensitive target, and mobile/keyboard interactions')

if __name__=='__main__':main()
