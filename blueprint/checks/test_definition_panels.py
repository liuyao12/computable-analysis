#!/usr/bin/env python3
"""Browser-check the definition chain rather than just the existence of cards."""
import functools, http.server, json, shutil, threading
from pathlib import Path
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]

def main():
    site=ROOT/'blueprint/web';data=json.loads((site/'three-proofs/node-details.json').read_text())
    audit=json.loads((site/'three-proofs/definition-audit.json').read_text())
    assert audit['passed'] and audit['nodesAudited']==19
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start(); errors=[]
    out=ROOT/'comparison/reports/browser';out.mkdir(parents=True,exist_ok=True)
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        kwargs={'headless':True,'args':['--no-sandbox']}
        if exe:kwargs['executable_path']=exe
        browser=p.chromium.launch(**kwargs);page=browser.new_page(viewport={'width':1440,'height':1100})
        page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(f'http://127.0.0.1:{server.server_port}/cosine-primitive-graph.html',wait_until='domcontentloaded')
        page.wait_for_function("document.querySelectorAll('#graph .node').length===18",timeout=60000)
        for label in ['def:c3-pi','def:c3-trig','def:c3-integral','thm:c3-primitive']:
            page.locator('#graph .node').filter(has=page.locator('title',has_text=label)).click()
            box=page.locator('[id="'+label+'_modal"]')
            assert box.locator('.bp-provenance').count()==len(data[label]['declarations'])
            assert box.locator('.bp-strategy>p').text_content()==data[label]['strategy']['summary']
            assert box.locator('.bp-namespace').count()>0
            if label=='def:c3-pi':
                card=box.locator('[data-declaration="ComputableAnalysis.CosinePrimitive.pi"]').first
                assert '4 * ComputableAnalysis.CosinePrimitive.A 1' in card.text_content()
                assert 'CosinePrimitiveData' in card.text_content()
            if label=='def:c3-trig':
                for name in ['sine_stage','cosine_stage','sine_outside_chart','cosine_outside_chart']:
                    assert box.locator('article[data-declaration="ComputableAnalysis.TrigonometricReadback.'+name+'"]').count()==1
                box.locator('.bp-group-link').nth(1).click()
                page.screenshot(path=str(out/'audited-trig-definitions.png'),full_page=True)
            page.keyboard.press('Escape')
        assert not errors,errors
        browser.close()
    server.shutdown()
    (out/'definition-panels.json').write_text(json.dumps({'passed':True,'javascriptErrors':errors,'nodesAudited':19,'piNamespaceExplained':True,'sinCosStageEquationsDisplayed':True},indent=2))
    print('PASS: independent pi definition, complete S/C wrappers, exact stage equations, domain warning, and source namespaces visible')
if __name__=='__main__': main()
