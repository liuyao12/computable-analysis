#!/usr/bin/env python3
"""Reference witnesses, matched contracts, true union accounting and preserved work."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import gzip,hashlib,json,math,sys
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[2];SITE=ROOT/'blueprint/web'
sys.path[:0]=[str(ROOT/'book'),str(ROOT/'blueprint/checks')]
from add_integral_portfolio import TARGETS,ROUTES,OPTIONS,witness,comparison
from build_proof_bench import closure

def verify():
    maps=json.loads((SITE/'reading/maps.json').read_text())
    stats=json.loads((SITE/'reading/integral-portfolio-comparison.json').read_text())
    report=maps['integralPortfolio']
    with gzip.open(SITE/'reading/integral-portfolio.json.gz','rt') as f:raw=json.load(f)
    nodes={n['id']:n for n in raw['nodes']};declarations={d['name']:d for d in raw['declarations']}
    assert all(raw['checks'].values()) and len(raw['roots'])==16
    assert report['families']==stats['families']==2 and len(stats['cases'])==8
    assert stats['sourceCommit']==maps['sourceCommit']==report['sourceCommit']
    # Recompute accounting without accepting the displayed totals as premises.
    expected=comparison(raw,nodes,stats['sourceCommit'])
    assert stats==expected
    for case,title in OPTIONS:
        roots=[x for x in raw['roots'] if x['case']==case];assert len(roots)==2
        for root in roots:
            assert 'sorryAx' not in root['axioms']
            deps=closure(nodes,[root['root']])
            assert all(other['root'] not in deps for other in roots if other!=root)
            if root['route']=='ftc':assert all(not nodes[n]['module'].startswith('Mathlib') for n in deps)
    for target in TARGETS:
        entry=maps['theorems'][target];assert entry['checkedComparison'] and entry['verifiedGraph'] and entry['sink']==target
        assert set(entry['views'])=={'all','1','2'} and set(entry['routeButtons'])=={'1','2'}
        witnesses=[e for e in maps['witnesses'] if e.get('map')==target]
        for e in witnesses:
            w=e['witness'];assert w and e['label']
            for dep,user in zip(w,w[1:]):
                assert dep in nodes[user]['typeRefs']+nodes[user]['bodyRefs']
                if e['kind']=='statement':assert nodes[user]['kind'] in ('def','definition','opaque') and dep in nodes[user]['bodyRefs']
            if e['kind']=='proof':assert w[-2] in nodes[w[-1]]['bodyRefs']
            assert w[0] in maps['bundles'][e['source']]['anchors']
            assert w[-1] in maps['bundles'][e['target']]['anchors']
        for view,file in entry['views'].items():
            doc=BeautifulSoup((SITE/file).read_text(),'html.parser')
            ids={e['data-node'] for e in doc.select('[data-node]')}
            assert len(doc.select('[data-node="'+target+'"]'))==1
            assert 'ip:rationals' in ids
            if view=='1':assert not any(n.startswith('ip:mathlib') or n.endswith('-bridge') for n in ids)
            if view=='2':assert 'ip:ftc' not in ids and 'ip:mathlib-ftc' in ids
            if 'beta' in target:assert not {'ip:geometry','ip:mathlib-trig'} & ids
            adjacency=defaultdict(set);degree={n:0 for n in ids}
            for e in doc.select('[data-edge]'):
                a,b=e['data-edge'].split('->');adjacency[a].add(b);degree[b]+=1
                paths=[w for w in witnesses if w['source']==a and w['target']==b and (view=='all' or w['route'] is None or str(w['route'])==view)]
                assert paths
                if e['data-edge-kind']=='statement':
                    assert e.find('path')['stroke']=='#202020' and not e.find('path').get('stroke-dasharray')
            assert not adjacency[target]
            q=[n for n,d in degree.items() if d==0];count=0
            while q:
                n=q.pop();count+=1
                for child in adjacency[n]:
                    degree[child]-=1
                    if not degree[child]:q.append(child)
            assert count==len(ids)
            for key in ids:
                bundle=maps['bundles'][key]
                assert [n for g in bundle['groups'] for n in g['names']]==[d['name'] for d in bundle['declarations']]
                for d in bundle['declarations']:
                    if key in ['ip:rationals','ip:mathlib-real']:continue # retained original checked bundle
                    assert all(d[k]==declarations[d['name']][k] for k in ['name','kind','type','value','ownerModule'])
    for file,digest in report['unchangedArtifacts'].items():assert hashlib.sha256((SITE/file).read_bytes()).hexdigest()==digest
    examples=json.loads((SITE/'reading/integral-native-examples.json').read_text())
    for row in examples['wallisBounds']:
        n=row['n'];v=Q(1)
        for j in range(1,n+1):v*=Q((2*j)**2,(2*j-1)*(2*j+1))
        assert Q(row['lower'])==2*v and Q(row['upper'])==2*v*Q(2*n+2,2*n+1)
        assert float(Q(row['lower']))<math.pi<float(Q(row['upper'])) # independent smoke check only
    for row in examples['betaOutputs']:
        m,n=row['m'],row['n'];v=Q(math.factorial(m)*math.factorial(n),math.factorial(m+n+1))
        assert Q(row['rationalValue'])==v and Q(row['lower'])<=v<=Q(row['upper'])
    page=BeautifulSoup((SITE/'integral-families.html').read_text(),'html.parser')
    assert {e['data-proof-map'] for e in page.select('[data-proof-map]')}==set(TARGETS)
    print('PASS: sixteen paired roots, four acyclic maps, exact statements, witnessed roles, no beta trigonometry, independent numerical executions and cumulative counts')
if __name__=='__main__':verify()
