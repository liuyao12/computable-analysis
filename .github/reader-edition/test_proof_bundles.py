#!/usr/bin/env python3
"""Check source inventories, route unions, graph coverage and browser interaction."""
import argparse,json,re,shutil,threading
from functools import partial
from http.server import SimpleHTTPRequestHandler,ThreadingHTTPServer
from pathlib import Path
from bs4 import BeautifulSoup
from proof_bundles import build_catalogue,decode_record,measure,source_record,union_measure,verify_sources


def validate(site):
    c=json.loads((site/'reading/proof-bundles.json').read_text())
    assert c==build_catalogue(site,c['documentationRevision'])
    m=json.loads((site/'reading/maps.json').read_text());ids={g['id'] for g in c['graphs']}
    assert set(m['theorems'])<=ids
    assert len(ids)==len(c['graphs'])==36
    for g in c['graphs']:
        ns={n['id']:n for n in g['nodes']};assert len(ns)==len(g['nodes'])
        routes={r['id'] for r in g['routes']};assert len(routes)>=2
        assert any('Mathlib' in r['name'] for r in g['routes']),g['id']
        seen=set()
        while len(seen)<len(ns):
            additions={k for k in ns if k not in seen and all(e['source'] in seen for e in g['edges'] if e['target']==k)}
            assert additions,('cycle',g['id']);seen|=additions
        for n in ns.values():
            assert set(n['routes'])<=routes and n['routes'],n
            assert n['loc']['unmeasuredSources']==0,n['id']
            if n['status']=='pending':assert n['loc']['codeLines'] is None and not n['sources']
            else:assert n['loc']['codeLines'] is not None,n['id']
        for r in g['routes']:
            included=[n for n in ns.values() if r['id'] in n['routes']]
            assert r['loc']==union_measure(included,c['sources'])
            measured=[n['loc']['codeLines'] for n in included if n['loc']['codeLines'] is not None]
            if measured:assert max(measured)<=r['loc']['codeLines']<=sum(measured)
        d=BeautifulSoup((site/g['page']).read_text(),'html.parser')
        link=d.select_one('[data-bundled-theorem="'+g['id']+'"] a');assert link and link['href']=='proof-bundles.html?theorem='+g['id']
    zeros=next(g for g in c['graphs'] if g['id']=='showcase:zeta-zeros')
    reflection=next(n for n in zeros['nodes'] if n['id']=='reflection')
    assert reflection['loc']['codeLines']==41
    assert zeros['loc']['pendingBundles']==5
    # Source spans must count after lexical comment removal and de-duplicate overlaps.
    record=source_record(b'/- comment\n nested /- text -/\n-/\ndef one := 1\n\ndef two := "-- literal" -- trailing\n')
    assert decode_record(record)=={4,6}
    refs=[dict(url='source',start=4,end=6),dict(url='source',start=6,end=6)]
    assert measure(refs,{'source':record})['codeLines']==2
    assert measure([dict(url='missing',start=None,end=None)],{})['codeLines'] is None
    euler=next(g for g in c['graphs'] if g['id']=='showcase:basel')
    route=next(r for r in euler['routes'] if r['id']=='mathlib')
    assert route['loc']['codeLines']==next(n for n in euler['nodes'] if n['id']=='fourier')['loc']['codeLines']
    assert not (site/'proof-bundles.html').read_text().count('__')
    return c


def main():
    p=argparse.ArgumentParser();p.add_argument('--site',required=True,type=Path);p.add_argument('--report',required=True,type=Path);p.add_argument('--static-only',action='store_true');p.add_argument('--verify-sources',action='store_true');a=p.parse_args();site=a.site.resolve();a.report.mkdir(parents=True,exist_ok=True);c=validate(site)
    if a.verify_sources:verify_sources(c)
    if not a.static_only:
        from playwright.sync_api import sync_playwright
        server=ThreadingHTTPServer(('127.0.0.1',0),partial(SimpleHTTPRequestHandler,directory=str(site)));threading.Thread(target=server.serve_forever,daemon=True).start();base='http://127.0.0.1:'+str(server.server_port)+'/'
        try:
            with sync_playwright() as playwright:
                options=dict(headless=True,args=['--no-sandbox'])
                executable=shutil.which('google-chrome') or shutil.which('chromium') or shutil.which('chromium-browser')
                if executable:options['executable_path']=executable
                browser=playwright.chromium.launch(**options)
                page=browser.new_page(viewport={'width':1440,'height':1000})
                page.goto(base+'proof-bundles.html?theorem=showcase:zeta-zeros',wait_until='networkidle')
                assert page.locator('.bundle-node').count()==8
                page.locator('[data-node="reflection"]').click();assert '41 file LOC' in page.locator('#bundle-detail').inner_text()
                page.locator('[data-bundle-route="sign"]').click();assert page.locator('[data-node="reflection"]').count()==0
                page.reload(wait_until='networkidle');assert page.locator('[data-bundle-route="sign"]').get_attribute('aria-pressed')=='true'
                for g in c['graphs']:
                    page.select_option('#bundle-theorem',g['id']);assert page.locator('.bundle-node').count()==len(g['nodes']),g['id'];assert page.locator('.bundle-error').count()==0
                    for r in g['routes']:
                        page.locator('[data-bundle-route="'+r['id']+'"]').click();assert page.locator('.bundle-node').count()==sum(r['id'] in n['routes'] for n in g['nodes'])
                    page.locator('.bundle-node').first.focus();page.keyboard.press('Enter');assert page.locator('.bundle-node[aria-pressed="true"]').count()==1
                page.select_option('#bundle-theorem','showcase:basel');page.locator('[data-bundle-route="mathlib"]').click();assert 'Shared lines counted once' in page.locator('#bundle-total').inner_text()
                for width in [1440,390,320]:
                    page.set_viewport_size({'width':width,'height':900});assert page.evaluate('document.documentElement.scrollWidth-innerWidth')<=2
                    assert page.locator('mjx-merror,[data-mjx-error]').count()==0
                    page.screenshot(path=str(a.report/('proof-bundles-'+str(width)+'.png')),full_page=True)
                browser.close()
        finally:server.shutdown()
    print('PASS: 36 theorem graphs, complete source measurements, route de-duplication, pending scope and viewer coverage')
if __name__=='__main__':main()
