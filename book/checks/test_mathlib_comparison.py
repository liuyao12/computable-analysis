#!/usr/bin/env python3
"""Check inline sizes, source coverage, precise Mathlib layers and unchanged proofs."""
from pathlib import Path
import hashlib,json,sys
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[2];SITE=ROOT/'blueprint/web'
sys.path.insert(0,str(ROOT/'book'))
from expand_mathlib_map import GROUPS,NONNEG,BOCHNER,INTERVAL,FTC,TARGET,build_comparison,witness

def verify():
    model=json.loads((SITE/'reading/maps.json').read_text())
    raw=json.loads((ROOT/'comparison/reports/proof-bench-raw.json').read_text());nodes={n['id']:n for n in raw['nodes']}
    bench=json.loads((SITE/'proof-bench/data.json').read_text())
    comparison=json.loads((SITE/'reading/map-comparison.json').read_text())
    fresh=build_comparison(raw,bench,nodes)
    assert fresh==comparison,'Numbers must be computed from the fixed proof roots, not hard-coded for the UI'
    expansion=model['mathlibExpansion'];assert all(expansion['checks'].values())
    assert hashlib.sha256((SITE/'proof-bench/data.json').read_bytes()).hexdigest()==expansion['benchmarkSha256']
    rows=comparison['cases']['identity']['routes']
    assert [rows[r]['costs']['full']['declarations'] for r in comparison['routeOrder']]==[5596,5674,42849]
    assert [rows[r]['costs']['full']['codeLines'] for r in comparison['routeOrder']]==[8955,9124,81510]
    for case in comparison['cases'].values():
        for row in case['routes'].values():
            for value in row['costs'].values():
                assert value['mappedDeclarations']+value['unmappedDeclarations']==value['declarations']
                assert sum(o['codeLines'] for o in value['origins'].values())==value['codeLines']
                assert sum(o['declarations'] for o in value['origins'].values())==value['declarations']
    # The combined cost is a union, not a sum charging shared foundations twice.
    for r in comparison['routeOrder']:
        full=lambda c:comparison['cases'][c]['routes'][r]['costs']['full']
        assert full('combined')['declarations']<=full('identity')['declarations']+full('validity')['declarations']
        assert full('combined')['codeLines']<=full('identity')['codeLines']+full('validity')['codeLines']
    exact={d['name']:d for d in json.loads((SITE/'reading/mathlib-map-statements.json').read_text())['declarations']}
    for key in GROUPS:
        b=model['bundles'][key];assert b['classification']=='mathlib'
        assert [n for g in b['groups'] for n in g['names']]==[d['name'] for d in b['declarations']]
        for d in b['declarations']:
            assert all(d[k]==exact[d['name']][k] for k in ['name','kind','type','value','ownerModule'])
            assert d['realDependencyPath'] and '/51e6992efd06126df61a496bebf8f49482a4e129/' in d['sourceUrl']
    for edge in expansion['witnesses']:
        p=edge['witness'];mode=edge['referenceMode']
        assert p==witness(nodes,p[-1],p[0],mode)
        for dep,user in zip(p,p[1:]):
            assert dep in nodes[user]['typeRefs']+nodes[user]['bodyRefs']
            if mode=='definitions':assert dep in nodes[user]['bodyRefs'] and nodes[user]['kind'] in ['definition','opaque']
        if mode=='proof':assert p[-2] in nodes[p[-1]]['bodyRefs']
        if mode=='type':assert p[-2] in nodes[p[-1]]['typeRefs']
    for view,file in model['theorems'][TARGET]['views'].items():
        doc=BeautifulSoup((SITE/file).read_text(),'html.parser')
        assert len(doc.select('[data-node="'+TARGET+'"]'))==1
        assert len(doc.select('[data-edge-kind="statement"]'))==4
        for key in GROUPS:assert bool(doc.select_one('[data-node="'+key+'"]'))==(view in ['all','2','companions'])
        if view in ['all','2','companions']:
            for source,target in [(NONNEG,BOCHNER),(BOCHNER,INTERVAL),(INTERVAL,FTC),(FTC,'lem:c3-mftc')]:
                assert doc.select_one('[data-edge="'+source+'->'+target+'"]')
        if view=='2':assert not doc.select_one('[data-edge="lem:c3-construction-valid->'+TARGET+'"]')
    assert witness(nodes,'integral_cos',"intervalIntegral.integral_deriv_eq_sub'",'proof')
    # The cosine primitive is NOT used to establish the quadrature correspondence.
    assert witness(nodes,'MathlibComparison.cosine_integral_represents','MathlibComparison.mathlib_cosine_primitive') is None
    page=(SITE/'proof-map.html').read_text()
    assert 'reading/map-comparison.css' in page and 'reading/map-comparison.js' in page
    print('PASS: paired declarations/LOC with coverage, correct dependency unions, exact Mathlib statements, actual FTC use, native routes and proof measurements unchanged')
if __name__=='__main__':verify()
