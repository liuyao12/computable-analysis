#!/usr/bin/env python3
"""Browser regression for the separate checked radical-evaluation map."""
from pathlib import Path
import functools,http.server,json,shutil,threading
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]

def main():
    site=ROOT/'blueprint/web';out=ROOT/'comparison/reports/dyadic-browser';out.mkdir(parents=True,exist_ok=True)
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/'
    errors=[]
    with sync_playwright() as p:
        executable=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        options={'headless':True,'args':['--no-sandbox']}
        if executable:options['executable_path']=executable
        browser=p.chromium.launch(**options);page=browser.new_page(viewport={'width':1500,'height':1100})
        page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(base+'dyadic-integral.html',wait_until='domcontentloaded')
        page.wait_for_selector('mjx-container',timeout=60000)
        assert not page.locator('mjx-merror,[data-mjx-error]').count()
        assert page.locator('.numerical-bounds tbody tr').count()==6
        assert '0.999904116' in page.locator('.numerical-bounds').text_content()
        page.screenshot(path=str(out/'radical-integral.png'),full_page=True)
        page.locator('[data-proof-map="thm:dyadic-product"]').click()
        frame=page.frame_locator('#proof-frame')
        frame.locator('[data-node="thm:dyadic-product"]').wait_for()
        assert not frame.locator('[data-route]:visible').count()
        assert frame.locator('[data-node="def:c3-integrals"]').count()==1
        assert frame.locator('[data-edge-kind="statement"]').count()==3
        for label in ['lem:dyadic-identities','lem:dyadic-values','thm:dyadic-product']:
            frame.locator('[data-node="'+label+'"]').dispatch_event('click')
            frame.locator('.bundle-lean>summary').click()
            exact=json.loads((site/'reading/maps.json').read_text())['bundles'][label]['declarations']
            text=[d['kind']+' '+d['name']+' : '+d['type']+(' :=\n'+d['value'] if d['value'] is not None else '') for d in exact]
            assert frame.locator('.lean-card code').all_text_contents()==text
        frame.locator('[data-edge="def:c3-pi->thm:dyadic-product"]').dispatch_event('click')
        assert frame.locator('#map-detail .role').text_content()=='USED IN THE STATEMENT'
        assert frame.locator('#map-detail h3').all_text_contents()==['Geometric π in the statement']
        frame.locator('[data-node="lem:dyadic-identities"]').dispatch_event('click')
        page.screenshot(path=str(out/'radical-map.png'),full_page=True)
        page.locator('#close-proof').click()
        page.set_viewport_size({'width':390,'height':850})
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        page.screenshot(path=str(out/'radical-mobile.png'),full_page=True)
        # An old arrow must not acquire witnesses from this separate map.
        page.goto(base+'proof-map.html?theorem=thm:c3-primitive',wait_until='domcontentloaded')
        page.wait_for_selector('[data-node="thm:c3-primitive"]')
        assert page.locator('[data-route]:visible').count()==4
        page.locator('[data-edge="def:c3-pi->thm:c3-primitive"]').dispatch_event('click')
        assert 'Dyadic evaluation proof' not in page.locator('#map-detail').text_content()
        assert not errors,errors
        browser.close()
    server.shutdown()
    (out/'results.json').write_text(json.dumps({'passed':True,'exactLeanCards':True,'singleCheckedMap':True,'oldProofRoutesUnchanged':True,'mobile':True,'javascriptErrors':errors},indent=2)+'\n')
    print('PASS: radical table, exact statement panels, correctly scoped map edges, old three routes and mobile rendering')
if __name__=='__main__':main()
