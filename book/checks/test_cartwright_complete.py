#!/usr/bin/env python3
"""Full theorem status must be supported by actual closed Lean proofs."""
from pathlib import Path
from collections import deque
import hashlib,json,sys
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[2];SITE=ROOT/'blueprint/web'
sys.path.insert(0,str(ROOT/'book'))
from complete_cartwright import EVAL,FINAL,OLD,N,A,BUNDLES,closure,comparison,source_index,source_union

def main():
    maps=json.loads((SITE/'reading/maps.json').read_text());report=json.loads((SITE/'reading/cartwright-audit.json').read_text())
    raw=json.loads((ROOT/'comparison/reports/cartwright-complete.json').read_text());nodes={n['id']:n for n in raw['nodes']}
    exact={d['name']:d for d in raw['declarations']};comp=json.loads((SITE/'reading/cartwright-comparison.json').read_text())
    assert report['status']=='complete' and report['finalIrrationalityProved'] and report['momentIdentityProved']
    assert all(raw['checks'].values()) and len(raw['roots'])==9
    for row in raw['roots']:
        ds=closure(nodes,[row['root']]);assert 'sorryAx' not in row['axioms']
        if row['route']!='mathlib':assert not any(nodes[n]['module'].startswith('Mathlib') for n in ds)
        for other in raw['roots']:
            if other['case']==row['case'] and other['route']!=row['route']:assert other['root'] not in ds
    # The shared integer layer is genuinely calculus-free; importing a file with
    # analytic neighbours does not substitute for actual-reference inspection.
    for name in raw['arithmetic']:
        ds=closure(nodes,[name]);assert 'Real' not in ds and 'ComputableAnalysis.RealRaw' not in ds
    for label in BUNDLES:
        b=maps['bundles'][label];assert b['proofStatus']=='checked'
        assert [n for g in b['groups'] for n in g['names']]==[d['name'] for d in b['declarations']]
        for d in b['declarations']:
            assert all(d[k]==exact[d['name']][k] for k in ['kind','type','value','ownerModule'])
    for target in [EVAL,FINAL]:
        entry=maps['theorems'][target];assert entry['checkedComparison'] and entry['verifiedGraph']
        assert not entry.get('outlineGraph')
        for view,path in entry['views'].items():
            svg=BeautifulSoup((SITE/path).read_text(),'html.parser')
            assert len(svg.select('[data-node="'+target+'"]'))==1
            assert not any('planned' in n.get_text().lower() for n in svg.select('[data-node]'))
            for e in svg.select('[data-edge]'):
                a,b=e['data-edge'].split('->')
                records=[x for x in maps['witnesses'] if x.get('map')==target and x['source']==a and x['target']==b and (view=='all' or x['route'] is None or str(x['route'])==view)]
                assert records,(target,view,a,b)
                for x in records:
                    w=x['witness'];assert len(w)>=2
                    for dep,user in zip(w,w[1:]):
                        assert dep in nodes[user]['typeRefs']+nodes[user]['bodyRefs']
                        if x['kind']=='statement':assert nodes[user]['kind']=='def' and dep in nodes[user]['bodyRefs']
                    if x['kind']=='proof':assert w[-2] in nodes[w[-1]]['bodyRefs']
            if view in ['0','1']:assert not any(n['data-node'].startswith('cw:mathlib') for n in svg.select('[data-node]'))
    assert maps['theorems'][OLD]['aliasOf']==FINAL
    assert comp==comparison(raw,nodes,maps['sourceCommit'])
    for case in comp['cases'].values():
        for r in case['routes'].values():
            for v in r['costs'].values():
                assert v['mappedDeclarations']+v['unmappedDeclarations']==v['declarations']
                assert sum(o['declarations'] for o in v['origins'].values())==v['declarations']
                assert sum(o['codeLines'] for o in v['origins'].values())==v['codeLines']
    for path,expected in report['unchangedArtifacts'].items():assert hashlib.sha256((SITE/path).read_bytes()).hexdigest()==expected
    page=BeautifulSoup((SITE/'cartwright.html').read_text(),'html.parser')
    assert len(page.select('[data-proof-map]'))==2
    assert {a['data-proof-map'] for a in page.select('[data-proof-map]')}=={EVAL,FINAL}
    assert 'not a completed formal proof' not in page.get_text()
    assert not (ROOT/'ComputableAnalysis/CartwrightViaFinite.lean').read_text().find('import ComputableAnalysis.CartwrightMomentFTC')>=0
    print('PASS: nine closed proofs, exact grouped statements, independent routes, shared arithmetic, witnessed diagrams, source-coverage accounting, preserved earlier examples')
if __name__=='__main__':main()
