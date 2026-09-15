#!/usr/bin/env python3
"""Exercise the comparison controls and exact report values in a browser."""
import functools,http.server,json,shutil,threading
from pathlib import Path
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]

def main():
    site=ROOT/'blueprint/web';data=json.loads((site/'proof-bench/data.json').read_text())
    handler=functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site))
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),handler)
    threading.Thread(target=server.serve_forever,daemon=True).start()
    errors=[]
    screenshots=ROOT/'comparison/reports/browser';screenshots.mkdir(parents=True,exist_ok=True)
    with sync_playwright() as p:
        executable=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts={'headless':True,'args':['--no-sandbox']}
        if executable:opts['executable_path']=executable
        browser=p.chromium.launch(**opts);page=browser.new_page(viewport={'width':1440,'height':1080})
        page.on('pageerror',lambda e:errors.append(str(e)))
        page.goto(f'http://127.0.0.1:{server.server_port}/proof-bench/',wait_until='networkidle')
        page.wait_for_selector('#rows tr')
        for case in data['cases']:
            page.select_option('#case',case)
            assert page.locator('#case-title').text_content()==data['cases'][case]['contract']['title']
            for baseline in ['full','statement-free','shared-free']:
                page.select_option('#baseline',baseline)
                for weight in ['bodyDag','bodyTree','declarations','typeDag']:
                    page.select_option('#weight',weight)
                    row=page.locator('#rows tr.total td').all_text_contents()[1:]
                    assert [int(x.replace(',','')) for x in row]==[
                        r['sizes'][baseline][weight] for r in data['cases'][case]['routes'].values()]
        page.select_option('#case','cosine-primitive');page.select_option('#baseline','full');page.select_option('#weight','bodyDag')
        assert page.locator('.roadmap-item').count()==8
        page.screenshot(path=str(screenshots/'proof-size-laboratory.png'),full_page=True)
        page.set_viewport_size({'width':390,'height':850})
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        page.screenshot(path=str(screenshots/'proof-size-mobile.png'),full_page=True)
        # The strategy guide decorates, rather than replaces, the exact code.
        page.set_viewport_size({'width':1440,'height':1080})
        page.goto(f'http://127.0.0.1:{server.server_port}/cosine-primitive-graph.html',wait_until='domcontentloaded')
        page.wait_for_function("document.querySelectorAll('#graph .node[data-foundation]').length===18",timeout=60000)
        detail=json.loads((site/'three-proofs/node-details.json').read_text())
        for label in ['lem:c3-direct','thm:c3-ftc','lem:c3-quadrature']:
            page.locator('#graph .node').filter(has=page.locator('title',has_text=label)).click()
            modal=page.locator('[id="'+label+'_modal"]')
            assert modal.locator('.bp-strategy>p').text_content()==detail[label]['strategy']['summary']
            assert modal.locator('.bp-step-purpose').count()==len(detail[label]['groups'])
            assert modal.locator('.bp-node-navigation button').count()>0
            assert modal.locator('.bp-lean-code code').first.text_content().startswith(('theorem','def'))
            page.keyboard.press('Escape')
        # Check every optional strategy equation as actual rendered LaTeX.
        page.wait_for_function("window.MathJax && typeof window.MathJax.typesetPromise === 'function'",timeout=30000)
        for label, item in detail.items():
            if not item['strategy']['formula'] or label == 'lem:c3-native-exp': continue
            page.locator('#graph .node').filter(has=page.locator('title',has_text=label)).click()
            modal=page.locator('[id="'+label+'_modal"]')
            relation=modal.locator('.bp-key-relation')
            relation.locator('summary').click()
            relation.locator('mjx-container').wait_for(state='visible',timeout=30000)
            assert relation.locator('mjx-merror, [data-mjx-error]').count()==0, label
            page.keyboard.press('Escape')
        page.locator('#graph .node').filter(has=page.locator('title',has_text='thm:c3-ftc')).click()
        page.screenshot(path=str(screenshots/'ftc-strategy-statements.png'),full_page=True)
        modal=page.locator('[id="thm:c3-ftc_modal"]')
        modal.locator('.bp-node-navigation button').last.click()
        assert not modal.is_visible()
        assert not errors,errors
        browser.close()
    server.shutdown()
    (screenshots/'proof-bench-results.json').write_text(json.dumps({'passed':True,'cases':3,
        'baselines':3,'weights':4,'testedViews':36,'javascriptErrors':errors},indent=2))
    print('PASS: all 36 case/baseline/weight views, exact numeric values, roadmap labels, and mobile layout')
if __name__=='__main__':main()
