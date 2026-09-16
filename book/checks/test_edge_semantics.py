#!/usr/bin/env python3
"""Audit statement-only arrows and colored proof-body entry separately."""
from pathlib import Path
import json, sys, unittest
from bs4 import BeautifulSoup
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'book'))
from proof_semantics import INPUTS, STATEMENT, TARGET, COLORS, NEUTRAL, INTEGRALS, FTC, INTEGRAL_RAW, FTC_DECL, reference_path

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
        self.assertEqual(reference_path(nodes, 'proof', 'input', definitions_only=True, type_entry=True), ['input','proof'])
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
    assert len(statements)==5 and {e['input'] for e in statements}=={'S','C','pi','integral','integrals'}
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
    generic=data['bundles'][INTEGRALS]
    assert generic['title']=='Integrals' and len(generic['declarations'])==5
    assert INTEGRAL_RAW in generic['anchors']
    original=data['bundles']['def:c3-integral']
    assert set(d['name'] for d in generic['declarations']).isdisjoint(d['name'] for d in original['declarations'])
    # Moving the five cards must neither modify nor discard any exported statement.
    exported={d['name']:d for d in json.loads((site/'three-proofs/blueprint-statements.json').read_text())['declarations']}
    for d in generic['declarations']:
        assert all(d[k]==exported[d['name']][k] for k in ['name','kind','type','value'])
    assert generic['mathHtml'] and 'finite Riemann sums' in generic['mathHtml']
    ftc_edges=[e for e in data['witnesses'] if e['source']==INTEGRALS and e['target']==FTC]
    assert len(ftc_edges)==1 and ftc_edges[0]['typeEntry']
    witness=ftc_edges[0]['witness']
    assert witness[0]==INTEGRAL_RAW and witness[-1]==FTC_DECL
    assert witness[-2] in nodes[FTC_DECL]['typeRefs']
    assert info['solidBlackDefinitionArrows'] and info['naturalRankConstrainedLayout']
    visible_sources={s for s,_,_ in INPUTS}
    for view,path in data['theorems'][TARGET]['views'].items():
        document=BeautifulSoup((site/path).read_text(),'html.parser')
        assert len(document.select('[data-node="'+TARGET+'"]'))==1
        assert len(document.select('[data-node="'+INTEGRALS+'"]'))==1
        assert document.select_one('[data-edge="'+INTEGRALS+'->def:c3-integral"]')
        if view in ['all','1','companions']:
            edge=document.select_one('[data-edge="'+INTEGRALS+'->'+FTC+'"]')
            assert edge and edge['data-edge-kind']=='construction'
            assert edge.find('path')['stroke']==NEUTRAL
        edges=document.select('[data-edge]')
        statement_edges=[e for e in edges if e['data-edge-kind']=='statement']
        assert {e['data-edge'].split('->')[0] for e in statement_edges}==visible_sources
        for e in statement_edges:
            assert e['data-edge'].endswith('->'+TARGET)
            path=e.find('path');assert not path.get('stroke-dasharray')
            assert path.get('stroke')==NEUTRAL
        for e in edges:
            color=e.find('path').get('stroke')
            if e['data-edge-kind']=='proof':
                assert color in COLORS
                if view in ('0','1','2'):assert color==COLORS[int(view)]
            else:assert color==NEUTRAL
    previous=site/'reference/proof-bench/data.json'
    assert (site/'proof-bench/data.json').read_bytes()==previous.read_bytes()
    print('PASS: computable-number bundle sequence; five definition-only inputs on four solid-black arrows; general integrals in the FTC type; body-witnessed proof colors; one sink in every route; unchanged metrics')

if __name__=='__main__':
    result=unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(PathTests))
    if not result.wasSuccessful():raise SystemExit(1)
    verify()
