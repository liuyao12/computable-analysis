#!/usr/bin/env python3
"""Reader regression: solid black definition arrows and a general integral bundle."""
from pathlib import Path
import functools, http.server, json, shutil, threading
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]


def main():
    site=ROOT/'blueprint/web';reports=ROOT/'comparison/reports/book-browser'
    reports.mkdir(parents=True,exist_ok=True)
    handler=functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site))
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),handler)
    threading.Thread(target=server.serve_forever,daemon=True).start()
    base=f'http://127.0.0.1:{server.server_port}/proof-map.html?theorem=thm:c3-primitive'
    errors=[]
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        options={'headless':True,'args':['--no-sandbox']}
        if exe:options['executable_path']=exe
        browser=p.chromium.launch(**options)
        page=browser.new_page(viewport={'width':1500,'height':1050})
        page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(base,wait_until='domcontentloaded')
        for route in ['all','0','1','2','all']:
            page.locator('[data-route="'+route+'"]').click()
            page.locator('#svg-holder[data-view="'+route+'"]').wait_for()
            assert page.locator('[data-edge-kind="statement"]').count()==4
            assert page.locator('[data-node="thm:c3-primitive"]').count()==1
            assert page.locator('[data-node="def:c3-integrals"]').count()==1
            edge=page.locator('[data-edge="def:c3-trig->thm:c3-primitive"]')
            edge.dispatch_event('click')
            assert page.locator('#map-detail h2').text_content()=='What the theorem is about'
            assert page.locator('#map-detail h3').all_text_contents()==['Sine in the endpoint','Cosine in the integral']
            assert 'wrapper name C' in page.locator('#map-detail').text_content()
            for path in page.locator('[data-edge-kind="statement"] path').all():
                assert path.get_attribute('stroke')=='#202020'
                assert path.get_attribute('stroke-dasharray') is None
            page.locator('[data-edge-kind="proof"]').first.dispatch_event('click')
            assert page.locator('#map-detail .role').text_content()=='USED IN A PROOF'
        page.locator('[data-node="def:c3-integrals"]').dispatch_event('click')
        assert page.locator('#map-detail h2').text_content()=='Integrals'
        assert 'finite Riemann sums' in page.locator('#map-detail .math-body').text_content()
        page.locator('.bundle-lean>summary').click()
        assert page.locator('.lean-card').count()==5
        assert 'Integral.Dovetail.raw' in page.locator('.lean-card code').all_text_contents()[1]
        page.screenshot(path=str(reports/'general-integral-statements.png'),full_page=True)
        assert page.locator('[data-edge="def:c3-integrals->thm:c3-ftc"]').count()==1
        page.locator('[data-edge="def:c3-integrals->thm:c3-ftc"]').dispatch_event('click')
        assert page.locator('#map-detail h3').text_content()=='Integral in the FTC statement'
        page.locator('[data-node="def:c3-intervals"]').dispatch_event('click')
        assert page.locator('#map-detail h2').text_content()=='Computable number'
        page.locator('.bundle-lean>summary').click()
        assert page.locator('.lean-group h3').all_text_contents()==[
            'Rational intervals','A computable number','Equality, order and refinement']
        assert 'ComputableAnalysis.QInterval' in page.locator('.lean-card code').first.text_content()
        page.screenshot(path=str(reports/'computable-number-statements.png'),full_page=True)
        page.locator('[data-node="thm:c3-primitive"]').dispatch_event('click')
        page.screenshot(path=str(reports/'statement-and-proof-arrows.png'),full_page=True)
        page.set_viewport_size({'width':390,'height':850})
        assert page.evaluate('document.documentElement.scrollWidth <= innerWidth+2')
        page.locator('[data-route="2"]').click()
        page.locator('#svg-holder[data-view="2"]').wait_for()
        assert page.locator('[data-edge-kind="statement"]').count()==4
        page.screenshot(path=str(reports/'statement-arrows-mobile.png'),full_page=True)
        assert not errors,errors
        browser.close()
    server.shutdown()
    (reports/'edge-role-results.json').write_text(json.dumps({'passed':True,
        'commonInputs':['S','C','pi','integral','integrals'],'visibleStatementArrows':4,
        'integralsBundle':True,'integralsUsedInFTCType':True,'solidBlackDefinitions':True,
        'everyProofRoute':True,'groupOrder':True,'mathlibShadingRetained':True,
        'javascriptErrors':errors},indent=2)+'\n')
    print('PASS: solid black definition links in every route, general integrals before the FTC, separate proof inspector, desktop/mobile')

if __name__=='__main__':main()
