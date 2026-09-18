#!/usr/bin/env python3
"""Verify the final chapter, exact Lean cards, finite stage data and proof paths."""
from __future__ import annotations
import argparse,functools,hashlib,http.server,json,re,shutil,threading
from fractions import Fraction as Q
from pathlib import Path
from bs4 import BeautifulSoup
from rational_geometry import FANS,QUARTER,G,C,GROUPS

def check(site):
    info=json.loads((site/'reading/rational-geometry-edition.json').read_text())
    audit=json.loads((site/'reading/rational-geometry.json').read_text())
    model=json.loads((site/'reading/maps.json').read_text())
    assert all(audit['checks'].values()) and all('sorryAx' not in r['axioms'] for r in audit['audits'])
    assert info['integralDefinitionsUnchanged'] and info['earlierTheoremEntriesUnchanged']
    doc=BeautifulSoup((site/'ch-circle-sphere.html').read_text(),'html.parser')
    h2=doc.select('.main-text h2');titles=[x.get_text() for x in h2]
    assert titles[:4]==['2.1 A quarter-circle computation','2.2 Area from ordered rational vectors',
      '2.3 Polygons and the choice of starting vertex','2.4 The geometric meaning of the computation']
    assert titles[4]=='2.5 Circumference and sector length'
    assert len(doc.select('#fig\\:rational-parameter-line'))==1
    assert 'signed area' not in doc.get_text().lower()
    ids=[x['id'] for x in doc.select('[id]')];assert len(ids)==len(set(ids))
    for link in doc.select('.on-this-page a'):assert doc.find(id=link['href'][1:])
    marker=doc.find(id='rational-geometry-original-tail')
    after=BeautifulSoup(''.join(str(x) for x in marker.next_siblings),'html.parser')
    before=BeautifulSoup(info['originalTail'],'html.parser')
    for d in [before,after]:
        for h in d.find_all('h2'):h.string=re.sub(r'^2\.\d+\s*','',h.get_text())
    assert str(before)==str(after),'Later mathematical material changed'
    for file,sha in info['protectedArtifacts'].items():
        assert hashlib.sha256((site/file).read_bytes()).hexdigest()==sha,file
    nodes={n['id']:n for n in audit['nodes']}
    for e in info['newEdgeWitnesses']:
        w=e['witness']
        for dep,user in zip(w,w[1:]):assert dep in nodes[user]['typeRefs']+nodes[user]['bodyRefs']
        if e['kind']=='proof':assert w[-2] in nodes[w[-1]]['bodyRefs']
        if e['kind']=='statement':assert w[-2] in nodes[w[-1]]['typeRefs']
    exact={d['name']:d for d in audit['declarations']}
    for key in GROUPS:
        for d in model['bundles'][key]['declarations']:
            assert all(d[x]==exact[d['name']][x] for x in ['kind','type','value','ownerModule'])
    for target in [FANS,QUARTER]:
        assert model['theorems'][target]['verifiedGraph'] and not model['theorems'][target]['checkedComparison']
        assert model['theorems'][target]['proofSourceCommit']==info['newProofSourceCommit']
        assert doc.select_one('[data-proof-map="'+target+'"]')
    # Recompute the short raw stages independently using the displayed finite formulas.
    prev=None
    for row in audit['stages']:
        n=row['stage'];N=2**n;lo=hi=Q(0)
        for j in range(N):
            u,v=Q(j,N),Q(j+1,N)
            lo+=(v-u)*(1+u*v)/((1+u*u)*(1+v*v))
            hi+=(v-u)/(1+u*v)
        assert lo==Q(row['lower']) and hi==Q(row['upper']) and hi-lo==Q(row['gap'])
        assert 0<=hi-lo<=Q(1,4**n)
        if prev:assert prev[0]<=lo<=hi<=prev[1]
        prev=lo,hi
    print('PASS: chapter order, cyclic polygons, literal Lean stages, exact declaration cards, witnessed dependencies and preserved later content')

def browser(site,output,offline):
    from playwright.sync_api import sync_playwright
    output.mkdir(parents=True,exist_ok=True)
    class QuietHandler(http.server.SimpleHTTPRequestHandler):
        def log_message(self,*args):pass
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(QuietHandler,directory=str(site)))
    threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/'
    model=json.loads((site/'reading/maps.json').read_text());errors=[]
    with sync_playwright() as p:
        exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
        opts={'headless':True,'args':['--no-sandbox']}
        if exe:opts['executable_path']=exe
        b=p.chromium.launch(**opts);page=b.new_page(viewport={'width':1500,'height':1050})
        page.on('pageerror',lambda e:errors.append(str(e)))
        if offline:
            page.route('**/*',lambda route:route.continue_() if route.request.url.startswith(base) else route.abort())
        page.goto(base+'ch-circle-sphere.html',wait_until='domcontentloaded')
        if not offline:
            page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
            page.evaluate('() => MathJax.startup.promise')
        assert not page.locator('mjx-merror,[data-mjx-error]').count()
        page.screenshot(path=str(output/'chapter-opening.png'),full_page=False)
        page.locator('[id="'+FANS+'"]').scroll_into_view_if_needed()
        page.screenshot(path=str(output/'polygon-theorem.png'),full_page=False)
        page.locator('[data-proof-map="'+FANS+'"]').click()
        frame=page.frame_locator('#proof-frame');frame.locator('[data-node="'+FANS+'"]').wait_for()
        assert not frame.locator('[data-route]:visible').count()
        frame.locator('.bundle-lean>summary').click()
        expected=[d['kind']+' '+d['name']+' : '+d['type']+(' :=\n'+d['value'] if d.get('value') is not None else '') for d in model['bundles'][FANS]['declarations']]
        assert frame.locator('.lean-card code').all_text_contents()==expected
        page.screenshot(path=str(output/'polygon-proof-map.png'),full_page=False)
        page.locator('#close-proof').click()
        page.set_viewport_size({'width':390,'height':850});page.locator('[id="'+QUARTER+'"]').scroll_into_view_if_needed()
        assert page.evaluate('document.documentElement.scrollWidth<=innerWidth+2')
        page.screenshot(path=str(output/'quarter-circle-mobile.png'),full_page=False)
        page.goto(base+'proof-map.html?theorem='+QUARTER,wait_until='domcontentloaded')
        page.wait_for_selector('[data-node="'+QUARTER+'"]')
        page.locator('[data-node="geo:validity"]').dispatch_event('click')
        assert 'does not use the new polygonal interpretation' in page.locator('#map-detail').text_content()
        assert not errors,errors
        b.close()
    server.shutdown()
    (output/'rational-geometry-tests.json').write_text(json.dumps(dict(passed=True,mathematicalRendering=not offline,
        nativeTheoremPanels=True,twoCheckedMaps=True,mobile=True,errors=errors),indent=2)+'\n')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--site',type=Path,required=True);p.add_argument('--report',type=Path,default=Path('reader-edition-tests'));p.add_argument('--structural-only',action='store_true');p.add_argument('--offline',action='store_true');a=p.parse_args();check(a.site)
    if not a.structural_only:browser(a.site,a.report,a.offline)
