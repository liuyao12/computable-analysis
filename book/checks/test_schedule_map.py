#!/usr/bin/env python3
"""Guard proof-role accuracy rather than simply graph appearance."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[2];SITE=ROOT/'blueprint/web'
sys.path.insert(0,str(ROOT/'book'))
from refine_cosine_map import path,ROOTS,VALIDS,VALID,END,TARGET,SCHEDULE

def verify():
    data=json.loads((SITE/'reading/maps.json').read_text())
    extra=json.loads((SITE/'reading/schedule-declarations.json').read_text())
    raw=json.loads((ROOT/'comparison/reports/proof-bench-raw.json').read_text())
    nodes={n['id']:n for n in raw['nodes']};nodes.update({n['id']:n for n in extra['nodes']})
    assert all(extra['checks'].values())
    report=data['schedulePresentation'];assert report['noIntegrabilityPredicateIntroduced']
    assert data['bundles'][TARGET]['title']=='Cosine primitive'
    assert 'three proofs' not in data['bundles'][TARGET]['mathHtml'].lower()
    assert data['bundles']['def:c3-integrals']['title']=='Integral construction'
    assert data['bundles']['def:c3-integral']['title']=='Chosen cosine construction'
    assert report['genericScheduledBoundsAreContextOnly'] and report['mathlibValidityIsSeparate']
    new=[e for e in report['newEdgeWitnesses']]
    for e in new:
        w=e['witness'];assert w[-2] in nodes[w[-1]]['bodyRefs']
        for dep,user in zip(w,w[1:]):assert dep in nodes[user]['typeRefs']+nodes[user]['bodyRefs']
    for root in ROOTS:
        assert path(nodes,root,SCHEDULE+'valid') is None
        assert path(nodes,root,SCHEDULE+'equivalent') is None
    assert path(nodes,ROOTS[0],VALIDS[0]) and path(nodes,ROOTS[1],VALIDS[1])
    assert path(nodes,ROOTS[2],VALIDS[2]) is None
    exact={d['name']:d for d in extra['declarations']}
    for key in [VALID,END]:
        b=data['bundles'][key]
        assert [n for g in b['groups'] for n in g['names']]==[d['name'] for d in b['declarations']]
        for d in b['declarations']:
            assert all(d[k]==exact[d['name']][k] for k in ['name','kind','type','value'])
    for view,file in data['theorems'][TARGET]['views'].items():
        doc=BeautifulSoup((SITE/file).read_text(),'html.parser')
        assert doc.select_one('[data-node="'+VALID+'"]')
        target=doc.select('[data-node="'+TARGET+'"]');assert len(target)==1
        assert 'three proofs' not in target[0].get_text().lower()
        assert len(doc.select('[data-edge-kind="statement"]'))==4
        if view=='2':
            assert not doc.select_one('[data-edge="'+VALID+'->'+TARGET+'"]')
            assert doc.select_one('[data-edge="'+END+'->'+TARGET+'"]')
        elif view in ['0','1']:assert doc.select_one('[data-edge="'+VALID+'->'+TARGET+'"]')
        for e in doc.select('[data-edge-kind="statement"]'):
            assert e.find('path')['stroke']=='#202020'
            assert not e.find('path').get('stroke-dasharray')
    assert hashlib.sha256((SITE/'proof-bench/data.json').read_bytes()).hexdigest()==report['proofMetricsFileSha256']
    assert 'id="the-chosen-schedule"' in (SITE/'cosine.html').read_text()
    print('PASS: supplied-schedule context, literal chosen program, separate validity, exact statements and proof-body edges; unchanged benchmark')
if __name__=='__main__':verify()
