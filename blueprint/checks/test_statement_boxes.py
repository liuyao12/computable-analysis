#!/usr/bin/env python3
"""Browser regressions for grouped verbatim Lean declarations and Real shading."""
from __future__ import annotations
import argparse, functools, http.server, json, re, shutil, threading
from pathlib import Path
from playwright.sync_api import sync_playwright, expect

ROOT = Path(__file__).resolve().parents[2]

def exact_code(record):
    return (record['kind']+' '+record['name']+':\n'+record['type']+
            (' :=\n'+record['value'] if record['value'] is not None else ''))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--site',type=Path,default=ROOT/'blueprint/web')
    parser.add_argument('--screenshots',type=Path,default=ROOT/'comparison/reports/browser')
    args=parser.parse_args(); args.screenshots.mkdir(parents=True,exist_ok=True)
    source=json.loads((args.site/'three-proofs/node-details.json').read_text())
    exported={d['name']:d for d in json.loads((args.site/'three-proofs/blueprint-statements.json').read_text())['declarations']}
    summary=json.loads((args.site/'three-proofs/summary.json').read_text())
    assert summary['nodeDisplay']['version']==4 and summary['nodeDisplay']['groupedStatements']
    expected_occurrences=sum(len(d['declarations']) for d in source.values())
    assert summary['nodeDisplay']['declarationOccurrences']==expected_occurrences
    for label,item in source.items():
        names=[name for g in item['groups'] for name in g['names']]
        assert len(names)>=3 and len(names)==len(set(names)),label
        assert names==[d['name'] for d in item['declarations']],label
        for d in item['declarations']:
            assert all(d[k]==exported[d['name']][k] for k in ['name','kind','type','value'])
    handler=functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(args.site.resolve()))
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),handler)
    threading.Thread(target=server.serve_forever,daemon=True).start()
    errors=[];checked=0
    with sync_playwright() as p:
        executable=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        kwargs={'headless':True,'args':['--no-sandbox']}
        if executable:kwargs['executable_path']=executable
        browser=p.chromium.launch(**kwargs)
        context=browser.new_context(viewport={'width':1440,'height':1100},permissions=['clipboard-read','clipboard-write'])
        page=context.new_page()
        page.on('pageerror',lambda e:errors.append(str(e)))
        url=f'http://127.0.0.1:{server.server_port}/cosine-primitive-graph.html'
        page.goto(url,wait_until='domcontentloaded')
        page.wait_for_function("document.querySelectorAll('#graph .node[data-foundation]').length===16",timeout=60000)
        def node(label):return page.locator('#graph .node').filter(has=page.locator('title',has_text=label))
        def target():return node('thm:c3-primitive')
        def modal_for(label):return page.locator('[id="'+label+'_modal"]')
        def card_for(modal,name):return modal.locator('.bp-declaration-card[data-declaration="'+name+'"]')
        def assert_plain_labels():
            for text in page.locator('#graph .node text').all_text_contents():
                assert not re.search(r'[=∫≃↔πⁱ₀ᵗ]|:=|[SCIA]\(',text),text
        def inspect(label):
            nonlocal checked
            modal=modal_for(label);modal.wait_for(state='visible')
            detail=source[label]
            assert modal.locator('.bp-declaration-card').count()==len(detail['declarations'])
            assert modal.locator('.bp-declaration-group').count()==len(detail['groups'])
            assert modal.locator('select[aria-label="Lean declaration"]').count()==0
            assert not modal.locator('.bp-math-explanation').evaluate('(e)=>e.open')
            assert not modal.locator('.thm_thmcontent').is_visible()
            assert modal.locator('.dep-modal-content').evaluate('(e)=>e.scrollTop')==0
            bounds=modal.locator('.bp-lean-code').first.bounding_box()
            assert 0<=bounds['y']<page.viewport_size['height']/2,bounds
            for d in detail['declarations']:
                card=card_for(modal,d['name'])
                assert card.locator('code').text_content()==exact_code(d),d['name']
                assert card.locator('code').get_attribute('data-declaration')==d['name']
                assert card.get_attribute('data-foundation')==('mathlib' if d['realDependencyPath'] else 'native')
                assert card.locator('.bp-formal-source').get_attribute('href')==d['sourceUrl']
                assert card.locator('.bp-companion-note').count()==int(d['displayOnly'])
                checked+=1
            return modal
        # Every broad node exposes multiple exact declarations at once.
        for label,detail in source.items():
            if label=='lem:c3-native-exp':continue
            assert node(label).get_attribute('data-foundation')==detail['classification'],label
            node(label).click();modal=inspect(label)
            modal.locator('.bp-group-link').last.click()
            assert modal.locator('.bp-declaration-group').last.bounding_box()['y']<page.viewport_size['height']
            modal.locator('.bp-math-explanation>summary').click()
            assert modal.locator('.thm_thmcontent').is_visible()
            page.keyboard.press('Escape');assert not modal.is_visible()
        assert_plain_labels()
        assert page.locator('#graph .node[data-foundation="mathlib"]').count()==6
        # The common proposition and all three proofs are present together.
        target().focus();page.keyboard.press('Enter');modal=inspect('thm:c3-primitive')
        stem='ComputableAnalysis.CosinePrimitive.'
        for short,status in [('Statement','native'),('viaInequalities','native'),('viaFTC','native'),('viaMathlib','mathlib')]:
            assert card_for(modal,stem+short).get_attribute('data-foundation')==status
        first=source['thm:c3-primitive']['declarations'][0]
        modal.locator('.bp-copy').first.click()
        expect(modal.locator('.bp-copy').first).to_have_text('Copied')
        assert page.evaluate('navigator.clipboard.readText()')==exact_code(first)
        page.screenshot(path=str(args.screenshots/'grouped-proposition.png'),full_page=True)
        modal.locator('.bp-group-link').nth(1).click()
        page.screenshot(path=str(args.screenshots/'three-proof-statements.png'),full_page=True)
        modal.locator('.dep-closebtn').click()
        node('def:c3-trig').click();inspect('def:c3-trig')
        page.screenshot(path=str(args.screenshots/'grouped-sine-cosine.png'),full_page=True)
        page.keyboard.press('Escape')
        for route,count,status in [('0',8,'native'),('1',9,'native'),('2',13,'mathlib'),('all',16,'mixed'),('companions',17,'mixed')]:
            page.locator('[data-view="'+route+'"]').click()
            page.wait_for_function('(n)=>document.querySelectorAll("#graph .node[data-foundation]").length===n',arg=count,timeout=30000)
            page.wait_for_timeout(200)
            assert target().get_attribute('data-foundation')==status
            assert_plain_labels()
            target().click();modal=inspect('thm:c3-primitive')
            highlights=modal.locator('.selected-route')
            assert highlights.count()==int(route in ['0','1','2'])
            if route in ['0','1','2']:
                assert highlights.get_attribute('data-declaration')==source['thm:c3-primitive']['anchors'][int(route)]
            page.keyboard.press('Escape')
            if route in ['0','1']:
                assert page.locator('#graph .node[data-foundation="mathlib"]').count()==0
            if route=='companions':
                node('lem:c3-native-exp').click();inspect('lem:c3-native-exp');page.keyboard.press('Escape')
        page.locator('[data-view="all"]').click()
        page.wait_for_function("document.querySelectorAll('#graph .node').length===16")
        page.locator('#graph .edge').first.click()
        assert page.locator('#proof-edge-dialog').is_visible()
        assert page.locator('#proof-edge-content li').count()>=2
        page.locator('#proof-edge-close').click()
        page.set_viewport_size({'width':390,'height':850})
        page.reload(wait_until='domcontentloaded')
        page.wait_for_function("document.querySelectorAll('#graph .node[data-foundation]').length===16",timeout=60000)
        target().click();modal=inspect('thm:c3-primitive')
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        bounds=modal.locator('.dep-modal-content').bounding_box()
        assert bounds['x']>=0 and bounds['x']+bounds['width']<=392
        page.screenshot(path=str(args.screenshots/'mobile-grouped-statements.png'),full_page=True)
        modal.locator('.bp-group-link').nth(1).click()
        card_for(modal,stem+'viaMathlib').locator('.bp-copy').click()
        expect(card_for(modal,stem+'viaMathlib').locator('.bp-copy')).to_have_text('Copied')
        m=next(d for d in source['thm:c3-primitive']['declarations'] if d['name']==stem+'viaMathlib')
        assert page.evaluate('navigator.clipboard.readText()')==exact_code(m)
        page.keyboard.press('Escape')
        assert not errors,errors
        browser.close()
    server.shutdown()
    (args.screenshots/'results.json').write_text(json.dumps({'passed':True,'javascriptErrors':errors,
        'groupedDeclarations':expected_occurrences,'cardsChecked':checked,
        'checked':'all grouped cards match exported Lean text; no single-statement selector; group navigation and copy; individual Real badges; proof route highlighting; unchanged graph; keyboard/mobile'},indent=2))
    print(f'PASS: {expected_occurrences} grouped declarations, exact exported code, copy/navigation, individual Real dependencies, and mobile')

if __name__=='__main__':main()
