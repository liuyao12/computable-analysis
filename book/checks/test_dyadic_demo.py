#!/usr/bin/env python3
"""Check the new map against stored Lean references and independent rational numerics."""
from pathlib import Path
from fractions import Fraction as Q
from unittest.mock import patch
import ast,hashlib,json,sys,xml.etree.ElementTree as ET
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[2];SITE=ROOT/'blueprint/web'
sys.path.insert(0,str(ROOT/'book'))
import dyadic_numerics as num

def verify():
    maps=json.loads((SITE/'reading/maps.json').read_text())
    audit=json.loads((SITE/'reading/dyadic-evaluation.json').read_text())
    assert all(audit['checks'].values())
    assert all('sorryAx' not in a['axioms'] for a in audit['audits'])
    target='thm:dyadic-product';entry=maps['theorems'][target]
    assert entry['verifiedGraph'] and not entry['checkedComparison'] and entry['sink']==target
    assert len(maps['theorems'])==13 and sum(t['checkedComparison'] for t in maps['theorems'].values())==1
    assert maps['theorems']['thm:c3-primitive']['checkedComparison']
    nodes={n['id']:n for n in audit['nodes']};decls={d['name']:d for d in audit['declarations']}
    edges=[e for e in maps['witnesses'] if e.get('map')==target]
    assert len(edges)==17 and sum(e['kind']=='statement' for e in edges)==3
    for e in edges:
        for dep,user in zip(e['witness'],e['witness'][1:]):
            assert dep in nodes[user]['bodyRefs']+nodes[user]['typeRefs']
            if e['kind']=='statement':
                assert nodes[user]['kind']=='def' and dep in nodes[user]['bodyRefs']
        if e['kind']=='proof':assert e['witness'][-2] in nodes[e['witness'][-1]]['bodyRefs']
    svg=ET.parse(SITE/entry['views']['all'])
    visible=[e.get('data-node') for e in svg.iter() if e.get('data-node')]
    assert len(visible)==12 and visible.count(target)==1 and 'def:c3-integrals' in visible
    for label in visible:
        b=maps['bundles'][label]
        if not label.startswith(('lem:dyadic','def:dyadic','def:radical','lem:radical','lem:cosine-endpoints','thm:dyadic')):continue
        assert [n for g in b['groups'] for n in g['names']]==[d['name'] for d in b['declarations']]
        for d in b['declarations']:
            assert all(d[k]==decls[d['name']][k] for k in ['name','kind','type','value','ownerModule'])
    for path,sha in maps['dyadicEvaluation']['unchangedArtifacts'].items():
        assert hashlib.sha256((SITE/path).read_bytes()).hexdigest()==sha
    assert not maps['dyadicEvaluation']['illustrationIsLeanStageExecution']
    manifest=json.loads((SITE/'reading/dyadic-numerics.json').read_text())
    assert not manifest['leanStageExecution']
    previous=None
    for row in manifest['rows']:
        assert row==num.product_row(row['depth'])
        lo,hi=map(Q,row['product']);assert lo<1<hi
        if previous:assert previous[0]<=lo<=hi<=previous[1]
        previous=lo,hi
        for key in ['integral','pi','product']:
            a,b=map(Q,row[key]);da,db=map(Q,row[key+'Display'])
            assert da<=a<=b<=db
        assert row['cells']==2**row['depth']
    assert manifest['rows'][-1]['productDisplay']==['0.999904116','1.000095875']
    for a,b in [(Q(0),Q(0)),(Q(1,2),Q(1,2)),(Q(2),Q(3)),(Q(1,7),Q(1,3))]:
        lo,hi=num.sqrt_box(a,b,16);assert lo**2<=a<=b<=hi**2
    for d in range(1,8):
        grid=num.radical_grid(d);old=num.radical_grid(d-1)
        assert grid[0]==(Q(1),Q(1)) and grid[-1]==(Q(0),Q(0))
        assert grid[::2]==old
        assert all(a<=b for a,b in grid)
        assert all(grid[i+1][1]<=grid[i][0] for i in range(len(grid)-1))
    # Dynamic separation: neither factor may call the other factor's routine.
    with patch.object(num,'geometric_pi',side_effect=AssertionError('pi used by cosine')):
        num.radical_grid.cache_clear();num.integral_box(7)
    with patch.object(num,'radical_grid',side_effect=AssertionError('cosine used by pi')):
        num.geometric_pi.cache_clear();num.geometric_pi(128)
    tree=ast.parse((ROOT/'book/dyadic_numerics.py').read_text())
    assert not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in ['sin','cos','tan','atan','pi'] for n in ast.walk(tree))
    page=BeautifulSoup((SITE/'dyadic-integral.html').read_text(),'html.parser')
    assert page.select_one('[data-proof-map="'+target+'"]')
    assert len(page.select('.numerical-bounds tbody tr'))==6
    assert 'not the literal stage outputs' in page.get_text()
    assert 'dyadic-integral.html' in (SITE/'cosine.html').read_text()
    print('PASS: 12 bundles, 17 witnessed edges, 3 definition-only statement inputs; exact Lean cards; original graphs/metrics unchanged; independent radical and polygon bounds')
if __name__=='__main__':verify()
