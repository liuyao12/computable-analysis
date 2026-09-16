#!/usr/bin/env python3
"""Regression tests for exact geometry, independent numerics and proof preservation."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import ast, hashlib, json, math, sys
from PIL import Image
import xml.etree.ElementTree as ET
ROOT=Path(__file__).resolve().parents[2];SITE=ROOT/'blueprint/web'
sys.path.insert(0,str(ROOT/'book'))
from numerical_examples import Clock, directed, example, rectangle_bounds, sector_bounds, point

def verify():
    maps=json.loads((SITE/'reading/maps.json').read_text());details=maps['bundles']
    assert 'lem:c3-inverse' not in details
    trig=details['def:c3-trig'];assert trig['title']=='Sine and cosine'
    assert 'ComputableAnalysis.ClosedArctanInverse.provider' in trig['anchors']
    assert any(d['name']=='ComputableAnalysis.ClosedArctanInverse.raw' for d in trig['declarations'])
    source=json.loads((SITE/'three-proofs/node-details.json').read_text())
    cards=lambda bundles:Counter((d['name'],d['type'],str(d.get('value'))) for b in bundles.values() for d in b['declarations'])
    assert cards(source)==cards(details),'No changed, missing or duplicated Lean cards'
    info=maps['geometricPresentation']
    assert info['piDefinition']=='4 A(1)' and info['verticalSubdivisionProjected']
    assert info['integralExposition']=='Increasing or decreasing integrands'
    assert info['independentCosineNumerics'] and not info['numericDriverIsLeanStageExecution']
    assert '4A(1)' in details['def:c3-pi']['mathHtml']
    for node,name in [('def:c3-arctan','arctan'),('def:c3-integrals','cosine'),('thm:c3-primitive','cosine'),('lem:c3-concavity','secants')]:
        assert details[node]['illustration']['id']==name
    assert 'Lipschitz bound is needed' in details['def:c3-integrals']['mathHtml']
    assert 'shrinks to zero' in details['lem:c3-concavity']['mathHtml']
    for b in details.values():
        assert [n for g in b['groups'] for n in g['names']]==[d['name'] for d in b['declarations']]
    for file in maps['theorems']['thm:c3-primitive']['views'].values():
        doc=ET.parse(SITE/file);visible=[e for e in doc.iter() if e.get('data-node')]
        assert not any(e.get('data-node')=='lem:c3-inverse' for e in visible)
        assert sum(e.get('data-node')=='thm:c3-primitive' for e in visible)==1
        for e in doc.iter():
            if e.get('data-edge'):
                a,b=e.get('data-edge').split('->');assert a!=b
                assert any(w['source']==a and w['target']==b for w in maps['witnesses'])
    path=SITE/'reading/animations';r=json.loads((path/'manifest.json').read_text())
    for name in ['arctan','cosine','secants']:
        im=Image.open(path/(name+'.gif'));assert im.n_frames==6 and im.size==(800,640)
        for suffix in ['gif','png']:
            file=name+'.'+suffix
            assert hashlib.sha256((path/file).read_bytes()).hexdigest()==r['files'][file]
        rows=r[name]
        for a,b in zip(rows,rows[1:]):assert Q(a['lower'])<=Q(b['lower'])<=Q(b['upper'])<=Q(a['upper'])
    assert not (path/'concave.gif').exists()
    for row in r['arctan']:
        n=row['subarcs'];u=Q(row['u']);assert u==Q(2,3)
        vertical=[list(map(Q,p)) for p in row['verticalPoints']]
        projected=[list(map(Q,p)) for p in row['projectedPoints']]
        assert vertical==[[Q(0),j*u/n] for j in range(n+1)]
        assert row['projectionOrigin']==['-1','0']
        for (_,v),(x,y) in zip(vertical,projected):
            assert x*x+y*y==1 and y==v*(x+1) and [x,y]==list(point(v))
        bounds=[sector_bounds(j*u/n,(j+1)*u/n) for j in range(n)]
        assert sum(l for l,h in bounds)==Q(row['lower'])
        assert sum(h for l,h in bounds)==Q(row['upper'])
    for row in r['secants']:
        h=Q(row['h']);assert Q(row['lower'])==Q(-1,2)-h/2
        assert Q(row['upper'])==Q(-1,2)+h/2
    for row in r['cosine']+r['cosineTable']:
        actual,_=example(row['cells']);assert actual==row
        for key,up in [('lower',False),('upper',True),('endpointLower',False),('endpointUpper',True)]:
            text=row[key+'Display'];val=Q(text.replace('−','-'))
            assert text==directed(Q(row[key]),upper=up)
            assert val>=Q(row[key]) if up else val<=Q(row[key])
        # Independent floating-point sanity check is TEST ONLY, not a source
        # of the produced enclosures or a mathematical proof.
        value=math.sin(math.pi/3)/math.pi
        assert float(Q(row['lower']))<value<float(Q(row['upper']))
        assert float(Q(row['endpointLower']))<value<float(Q(row['endpointUpper']))
    clock=Clock(128)
    for x in [Q(0),Q(1,100),Q(1,6),Q(1,3),Q(49,100),Q(1,2)]:
        lo,hi=clock.inverse(x)
        assert float(lo)-1e-15<=math.tan(math.pi*float(x)/2)<=float(hi)+1e-15
    # Constant, decreasing affine and decreasing step examples need no derivative.
    for fn,value in [(lambda x:Q(-2),Q(-2)),(lambda x:1-x,Q(1,2)),(lambda x:Q(x<Q(1,2)),Q(1,2))]:
        lo,hi,_=rectangle_bounds(lambda x:(fn(x),fn(x)),Q(1),8)
        assert lo<=value<=hi
    tree=ast.parse((ROOT/'book/numerical_examples.py').read_text())
    funcs={n.name:n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef)}
    names=lambda fn:{getattr(n,'id',getattr(n,'attr','')) for n in ast.walk(funcs[fn])}
    assert not {'sine','endpoint_bounds','example'} & names('rectangle_bounds')
    assert not {'rectangle_bounds','example'} & names('endpoint_bounds')
    assert not any(isinstance(n,(ast.Import,ast.ImportFrom)) and 'math' in ast.unparse(n) for n in ast.walk(tree))
    chapter=(SITE/'cosine.html').read_text()
    assert 'COSINE_NUMERICAL_TABLE' not in chapter and '0.2755015' in chapter
    print('PASS: equal vertical subdivisions and exact projection rays; independent outward-rounded cosine bounds; monotone integration vs secant derivatives; all Lean cards and witnesses preserved')
if __name__=='__main__':verify()
