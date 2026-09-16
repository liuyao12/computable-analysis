#!/usr/bin/env python3
"""Check the diagram's exact mathematics and the boundary of the presentation."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import hashlib,json,sys
from PIL import Image
import xml.etree.ElementTree as ET
ROOT=Path(__file__).resolve().parents[2];SITE=ROOT/'blueprint/web'

def verify():
    maps=json.loads((SITE/'reading/maps.json').read_text());details=maps['bundles']
    assert 'lem:c3-inverse' not in details
    trig=details['def:c3-trig'];assert trig['title']=='Sine and cosine'
    assert 'ComputableAnalysis.ClosedArctanInverse.provider' in trig['anchors']
    assert any(d['name']=='ComputableAnalysis.ClosedArctanInverse.raw' for d in trig['declarations'])
    source=json.loads((SITE/'three-proofs/node-details.json').read_text())
    before=Counter((d['name'],d['type'],str(d.get('value'))) for b in source.values() for d in b['declarations'])
    after=Counter((d['name'],d['type'],str(d.get('value'))) for b in details.values() for d in b['declarations'])
    assert before==after,'Folding must neither rewrite, duplicate nor drop a Lean declaration'
    assert maps['geometricPresentation']['piDefinition']=='4 A(1)'
    assert maps['geometricPresentation']['concaveOnlyLeanConstructorImplemented'] is False
    assert '4A(1)' in details['def:c3-pi']['mathHtml']
    assert details['def:c3-arctan']['illustration']['id']=='arctan'
    assert details['def:c3-integrals']['illustration']['id']=='concave'
    assert 'not yet been formalized' in details['def:c3-integrals']['formalizationBoundary']
    for b in details.values():
        assert [n for g in b['groups'] for n in g['names']]==[d['name'] for d in b['declarations']]
    for view,file in maps['theorems']['thm:c3-primitive']['views'].items():
        doc=ET.parse(SITE/file)
        visible=[e for e in doc.iter() if e.get('data-node')]
        assert not any(e.get('data-node')=='lem:c3-inverse' for e in visible)
        assert sum(e.get('data-node')=='thm:c3-primitive' for e in visible)==1
        for node in visible:
            labels=[''.join(e.itertext()) for e in node.iter() if e.tag.rsplit('}',1)[-1]=='text']
            assert not any('Native' in text for text in labels if 'exponential' not in text)
        for e in doc.iter():
            if not e.get('data-edge'):continue
            a,b=e.get('data-edge').split('->');assert a!=b
            assert any(w['source']==a and w['target']==b for w in maps['witnesses'])
    path=SITE/'reading/animations';r=json.loads((path/'manifest.json').read_text())
    for n in ['arctan','concave']:
        im=Image.open(path/(n+'.gif'));assert im.n_frames==6 and im.size==(800,640)
        for filename in [n+'.gif',n+'.png']:assert hashlib.sha256((path/filename).read_bytes()).hexdigest()==r['files'][filename]
    for row in r['arctan']:
        assert Q(row['u'])==Q(2,3) and list(map(Q,row['point']))==[Q(5,13),Q(12,13)]
    for name in ['arctan','concave']:
        rows=r[name]
        for a,b in zip(rows,rows[1:]):assert Q(a['lower'])<=Q(b['lower'])<=Q(b['upper'])<=Q(a['upper'])
    for row in r['concave']:
        assert Q(row['lower'])<=Q(5,6)<=Q(row['upper'])
        assert Q(row['gap'])==Q(1,8*row['cells']**2)
    print('PASS: exact rational sector/polygon bounds; concave area bounds; real GIF frames; inverse folded with exact cards and witnesses; formalization status explicit')

if __name__=='__main__':verify()
