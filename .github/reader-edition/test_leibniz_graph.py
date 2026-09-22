#!/usr/bin/env python3
"""Check preservation and exercise the mathematical map in desktop/mobile browsers."""
import argparse
import hashlib
import importlib.util
import json
import shutil
import threading
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright

spec=importlib.util.spec_from_file_location('leibniz_graph',Path(__file__).with_name('leibniz_graph.py'))
graph=importlib.util.module_from_spec(spec);spec.loader.exec_module(graph)

def main():
    p=argparse.ArgumentParser();p.add_argument('--site',type=Path,required=True);p.add_argument('--report',type=Path,default=Path('reader-edition-tests'))
    args=p.parse_args();site=args.site.resolve();out=args.report;out.mkdir(parents=True,exist_ok=True)
    report=json.loads((site/'reading/leibniz-graph-publication.json').read_text())
    model=json.loads((site/'reading/leibniz-graph.json').read_text());graph.validate(model)
    assert all(report['checks'].values()) and not report['newLeanProofsClaimed']
    assert graph.digest(site/'ch-infinite-series.html')==report['chapterSha256']
    for name,sha in {**report['artifactHashes'],**report['protectedArtifactHashes']}.items():assert graph.digest(site/name)==sha,name
    assert graph.install(site,report['documentationRevision'])==report
    document=BeautifulSoup((site/graph.PAGE).read_text(),'html.parser')
    assert len(document.select('.reading article'))==17
    for a in document.select('a[href]'):
        href=urlsplit(a['href'])
        if not href.scheme and href.path:assert (site/href.path).is_file(),a['href']
    class Quiet(SimpleHTTPRequestHandler):
        def log_message(self,*args):pass
    server=ThreadingHTTPServer(('127.0.0.1',0),partial(Quiet,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start()
    origin=f'http://127.0.0.1:{server.server_port}'
    errors=[];external=[]
    try:
        with sync_playwright() as pw:
            options={'headless':True,'args':['--no-sandbox']}
            executable=shutil.which('google-chrome') or shutil.which('chromium')
            if executable:options['executable_path']=executable
            browser=pw.chromium.launch(**options)
            for width in [1440,1024,768,390,320]:
                page=browser.new_page(viewport={'width':width,'height':1100})
                page.on('pageerror',lambda e:errors.append(str(e)))
                page.on('request',lambda r:external.append(r.url) if not r.url.startswith(origin) else None)
                page.goto(origin+'/'+graph.PAGE,wait_until='networkidle')
                assert page.locator('.node').count()==17
                assert page.locator('.edge').count()==22
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1'),width
                # Labels must fit within the actual rendered node rectangles.
                assert page.locator('.node').evaluate_all('nodes => nodes.every(n => {const r=n.querySelector("rect").getBBox();return [...n.querySelectorAll("text")].every(t=>{const b=t.getBBox();return b.x>=0 && b.y>=0 && b.x+b.width<=r.width && b.y+b.height<=r.height;});})'),f'Clipped node text at {width}'
                if width==1440:page.screenshot(path=str(out/'leibniz-graph-desktop.png'),full_page=True)
                for route,sink in [('0','computational'),('1','taylor'),('2','mathlib')]:
                    page.locator(f'button[data-route="{route}"]').click()
                    expected=[n for n in model['nodes'] if int(route) in n['routes']]
                    assert page.locator('.node').count()==len(expected)
                    assert page.locator(f'.node[data-node="{sink}"]').get_attribute('aria-pressed')=='true'
                    if route!='2':assert page.locator('.node[data-family="mathlib"]').count()==0
                    # Each bundle opens an explanation and pinned source links.
                    for n in expected:
                        page.locator(f'.node[data-node="{n["id"]}"]').click()
                        assert page.locator('#detail-content h2').inner_text()==n['title']
                        assert page.locator('#detail-content .source-list a').count()==len(n['refs'])
                    assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                page.locator('button[data-route="all"]').click()
                node=page.locator('.node[data-node="finite"]');node.focus();page.keyboard.press('Enter')
                assert page.locator('#detail-content h2').inner_text()=='Finite geometric algebra'
                if width==1440:page.screenshot(path=str(out/'leibniz-graph-bundle.png'),full_page=True)
                page.locator('#reset-selection').click();assert page.locator('.node.selected').count()==0
                page.locator('button[data-route="1"]').click()
                if width==390:
                    page.evaluate('scrollTo(0,0)');page.screenshot(path=str(out/'leibniz-graph-mobile.png'),full_page=True)
                page.close()
            context=browser.new_context(java_script_enabled=False,viewport={'width':390,'height':844})
            page=context.new_page();page.goto(origin+'/'+graph.PAGE)
            page.locator('#reading-outline>summary').click();assert page.locator('#outline-mathlib').is_visible()
            assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
            context.close();browser.close()
    finally:server.shutdown()
    assert not errors,errors
    assert not external,external
    checks=dict(artifactHashes=True,priorProofMapsPreserved=True,chapterOutsideDiagramPreserved=True,idempotentPublication=True,allThreeRoutes=True,allBundlesSelectable=True,keyboardSelection=True,nodeTextFits=True,fiveViewportWidths=True,noExternalRuntimeDependencies=True,noJavaScriptOutline=True)
    (out/'leibniz-graph-tests.json').write_text(json.dumps(checks,indent=2)+'\n')
    print('PASS: preservation, 17 bundles, 3 proof routes, keyboard access, source links and five viewport widths')

if __name__=='__main__':main()
