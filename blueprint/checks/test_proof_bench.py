#!/usr/bin/env python3
"""Independent accounting regressions for the matched-statement suite."""
from __future__ import annotations
import json,unittest
from pathlib import Path
from build_proof_bench import closure, totals, source_union, origin, ROOT, WEIGHTS, ORIGINS

class AccountingTests(unittest.TestCase):
    def test_shared_dag_is_counted_once(self):
        def n(refs):return {'typeRefs':[],'bodyRefs':refs,'module':'ComputableAnalysis.Test',
            'bodyDag':2,'bodyTree':3,'typeDag':1,'typeTree':1}
        nodes={'r':n(['a','b']),'a':n(['c']),'b':n(['c']),'c':n([])}
        ds=closure(nodes,['r']);self.assertEqual(ds,{'r','a','b','c'})
        self.assertEqual(totals(ds,nodes)['bodyDag'],8)
    def test_origin_order(self):
        self.assertEqual(origin('MathlibComparison.Example'),'bridge')
        self.assertEqual(origin('Mathlib.Example'),'mathlib')
        self.assertEqual(origin('ComputableAnalysis.Example'),'native')
    def test_source_union(self):
        r={'a':('x',1,3),'b':('x',2,4)};c={'x':['one','','three','four']}
        self.assertEqual(source_union({'a','b','missing'},r,c),{'nonblankCodeLines':3,
            'mappedDeclarations':2,'unmappedDeclarations':1,'availableSourceFiles':1})
    def test_missing_reference_fails(self):
        with self.assertRaises(ValueError):closure({},['missing'])

def main():
    result=unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(AccountingTests))
    if not result.wasSuccessful():raise SystemExit(1)
    report=json.loads((ROOT/'blueprint/web/proof-bench/data.json').read_text())
    raw=json.loads((ROOT/'comparison/reports/proof-bench-raw.json').read_text())
    nodes={n['id']:n for n in raw['nodes']}
    assert len(raw['roots'])==8 and len(report['cases'])==3
    assert all(report['checks'].values())
    for case,c in report['cases'].items():
        ds={route:closure(nodes,[r['root']]) for route,r in c['routes'].items()}
        shared=set.intersection(*ds.values())
        types=set().union(*(closure(nodes,nodes[r['root']]['typeRefs']) for r in c['routes'].values()))
        for route,r in c['routes'].items():
            assert 'sorryAx' not in r['axioms']
            if r['native']:assert not any(nodes[x]['module'].startswith('Mathlib') for x in ds[route])
            for key,ss in [('full',ds[route]),('statement-free',ds[route]-types),('shared-free',ds[route]-shared)]:
                got=r['sizes'][key];expect=totals(ss,nodes)
                assert all(got[k]==expect[k] for k in ['declarations',*WEIGHTS,'origins'])
                assert got['source']['mappedDeclarations']+got['source']['unmappedDeclarations']==len(ss)
                for weight in ['declarations',*WEIGHTS]:
                    assert sum(got['origins'][o][weight] for o in ORIGINS)==got[weight]
            for other in c['routes'].values():
                if other['root']!=r['root']:assert other['root'] not in ds[route]
    for route,p in report['portfolio'].items():
        running=set()
        assert p['order']==['cosine-primitive','cosine-validity']
        for step in p['steps']:
            now=closure(nodes,[report['cases'][step['case']]['routes'][route]['root']])
            assert step['added']['declarations']==len(now-running)
            running|=now
            assert step['union']['declarations']==len(running)
        assert p['total']['bodyDag']==sum(nodes[n]['bodyDag'] for n in running)
        assert sum(s['added']['bodyDag'] for s in p['steps'])==p['total']['bodyDag']
    assert len(report['roadmap'])==8 and all(x['status']=='planned' for x in report['roadmap'])
    print('PASS: matched-case accounting, baselines, origin partitions, source coverage, marginal/union costs, planned status')
if __name__=='__main__':main()
