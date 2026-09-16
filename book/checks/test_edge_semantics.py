#!/usr/bin/env python3
"""Audit statement-only arrows and colored proof-body entry separately."""
from pathlib import Path
import json, sys, unittest
from bs4 import BeautifulSoup
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'book'))
from proof_semantics import INPUTS, STATEMENT, TARGET, COLORS, NEUTRAL, reference_path

class PathTests(unittest.TestCase):
    def test_definition_path_does_not_consume_a_theorem(self):
        nodes = {
            'statement': {'kind':'definition','bodyRefs':['proof'], 'typeRefs':[]},
            'proof': {'kind':'theorem','bodyRefs':['hidden'], 'typeRefs':[]},
            'hidden': {'kind':'definition','bodyRefs':[], 'typeRefs':[]},
        }
        self.assertIsNone(reference_path(nodes, 'statement', 'hidden', definitions_only=True))
        self.assertEqual(reference_path(nodes, 'statement', 'hidden'), ['hidden','proof','statement'])

    def test_type_reference_is_not_proof_body_use(self):
        nodes = {
            'proof': {'kind':'theorem','bodyRefs':[], 'typeRefs':['input']},
            'input': {'kind':'definition','bodyRefs':[], 'typeRefs':[]},
        }
        self.assertIsNone(reference_path(nodes, 'proof', 'input', body_entry=True))
        nodes['proof']['bodyRefs'] = ['input']
        self.assertEqual(reference_path(nodes,'proof','input',body_entry=True), ['input','proof'])


def verify(site=ROOT/'blueprint/web'):
    data=json.loads((site/'reading/maps.json').read_text())
    raw=json.loads((ROOT/'comparison/reports/proof-bench-raw.json').read_text())
    nodes={n['id']:n for n in raw['nodes']}
    info=data['edgeSemantics']
    assert info['statementDefinitionsVerified'] and info['proofBodyEntryVerified']
    assert info['oneAcyclicSinkInEveryView'] and info['unchangedProofTermsAndMetrics']
    bundle=data['bundles']['def:c3-intervals']
    assert bundle['title']=='Computable number'
    assert [g['title'] for g in bundle['groups']]==['Rational intervals','A computable number','Equality, order and refinement']
    assert bundle['groups'][0]['names'][0]=='ComputableAnalysis.QInterval'
    statements=[e for e in data['witnesses'] if e['kind']=='statement']
    assert len(statements)==4 and {e['input'] for e in statements}=={'S','C','pi','integral'}
    for e in statements:
        assert e['route'] is None and e['witness'][-1]==STATEMENT and e['target']==TARGET
        for dep,user in zip(e['witness'],e['witness'][1:]):
            assert nodes[user]['kind'] in ('definition','opaque')
            assert dep in nodes[user]['bodyRefs']
    for e in data['witnesses']:
        if e['kind']=='proof':
            assert e['route'] in (0,1,2)
            assert STATEMENT not in e['witness']
            assert e['witness'][-2] in nodes[e['witness'][-1]]['bodyRefs']
    visible_sources={s for s,_,_ in INPUTS}
    for view,path in data['theorems'][TARGET]['views'].items():
        document=BeautifulSoup((site/path).read_text(),'html.parser')
        assert len(document.select('[data-node="'+TARGET+'"]'))==1
        edges=document.select('[data-edge]')
        statement_edges=[e for e in edges if e['data-edge-kind']=='statement']
        assert {e['data-edge'].split('->')[0] for e in statement_edges}==visible_sources
        for e in statement_edges:
            assert e['data-edge'].endswith('->'+TARGET)
            path=e.find('path');assert path.get('stroke-dasharray')
            assert path.get('stroke')==NEUTRAL
        for e in edges:
            color=e.find('path').get('stroke')
            if e['data-edge-kind']=='proof':
                assert color in COLORS
                if view in ('0','1','2'):assert color==COLORS[int(view)]
            else:assert color==NEUTRAL
    # The UI revision must not alter existing numerical or proof-size reports.
    previous=site/'reference/proof-bench/data.json'
    assert (site/'proof-bench/data.json').read_bytes()==previous.read_bytes()
    print('PASS: computable-number bundle sequence; four definition-only inputs on three neutral arrows; body-witnessed proof colors; one sink in every route; unchanged metrics')

if __name__=='__main__':
    result=unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(PathTests))
    if not result.wasSuccessful():raise SystemExit(1)
    verify()
