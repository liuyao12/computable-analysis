"""Generate the stateful positive-orthant ball computation for Chapter 2.

Only the axis-simplex/unit-cube initialization takes whole-body volumes.
Refinements add visible inner pyramids and subtract outer caps. Independent
whole-polytope verification belongs to check_polyhedra.py, not this evaluator.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
from rational_polytopes import dot
from orthant_ball import OrthantBallComputation, is_axis
ROOT=Path(__file__).parent

def decimal_down(value,places=6):
    scale=10**places;num=value.numerator*scale//value.denominator
    return f'{num//scale}.{num%scale:0{places}d}'

def decimal_up(value,places=6):
    scale=10**places;num=-(-value.numerator*scale//value.denominator)
    return f'{num//scale}.{num%scale:0{places}d}'

def model(polytope,cached_volume):
    return dict(vertices=[[str(q) for q in p] for p in polytope.vertices],
        faces=polytope.mesh3(),edges=sorted({tuple(sorted((a,b))) for f in polytope.facets() for a,b in zip(f.vertices,f.vertices[1:]+f.vertices[:1])}),volume=str(cached_volume))

def encode_update(update):
    result={k:str(update[k]) for k in ['innerIncrement','outerDecrement']}
    result['point']=[str(q) for q in update['point']]
    for name in ['innerSimplices','outerCapSimplices']:
        result[name]=[[[str(q) for q in p] for p in simplex] for simplex in update[name]]
    return result

def snapshot(computation,previous):
    samples=computation.samples;planes=computation.halfspaces
    inner,outer=computation.inner,computation.outer
    lo,hi=computation.lower,computation.upper;m=computation.denominator
    assert all(dot(p,p)==1 and all(x>=0 for x in p) for p in samples)
    assert len([1 for a,b in planes if b==0])==3
    assert sum(is_axis(a) for a,b in planes if b==1)==3
    assert all(dot(a,x)<=b for a,b in planes for x in outer.vertices)
    assert all(dot(a,x)<=b for a,b in planes for x in inner.vertices)
    assert 0<lo<hi
    alpha=1-Q(4,m*m)
    if alpha>0:
        assert all(f.offset>=0 and alpha*alpha*sum(max(a,0)**2 for a in f.normal)<=f.offset**2 for f in inner.facets())
        assert all(dot(x,x)<=1/(alpha*alpha) for x in outer.vertices)
        assert all(dot(f.normal,tuple(alpha*alpha*x for x in p))<=f.offset for f in inner.facets() for p in outer.vertices)
    return dict(stage=computation.stage,mesh=m,samples=len(samples),tangents=len(samples),coordinatePlanes=3,
        axisTangents=3,inner=model(inner,lo),outer=model(outer,hi),
        halfspaces=[dict(normal=[str(q) for q in a],offset=str(b),kind='coordinate' if b==0 else 'tangent') for a,b in planes],
        decimalLower=decimal_down(8*lo),decimalUpper=decimal_up(8*hi),
        orthantDecimalLower=decimal_down(lo),orthantDecimalUpper=decimal_up(hi),
        wholeBallLower=str(8*lo),wholeBallUpper=str(8*hi),gap=str(8*(hi-lo)),
        previousOrthantBounds=None if previous is None else [str(q) for q in previous],
        updates=[encode_update(u) for u in computation.last_updates],
        innerAdded=str(sum((u['innerIncrement'] for u in computation.last_updates),Q(0))),
        outerRemoved=str(sum((u['outerDecrement'] for u in computation.last_updates),Q(0))),
        alpha=str(alpha) if alpha>0 else None)

if __name__=='__main__':
    stages=[];computation=OrthantBallComputation(3);previous=None
    for k in range(5):
        if k:
            previous=(computation.lower,computation.upper);computation.refine()
        s=snapshot(computation,previous);stages.append(s)
        print(k,s['mesh'],s['samples'],s['decimalLower'],s['decimalUpper'],flush=True)
    data=dict(construction='positive orthant; origin in inner hull; all axis tangents and coordinate planes included',
        evaluator='persistent dyadic refinement; add visible inner pyramids and subtract outer caps; no whole-body volume recomputation after initialization',
        arithmetic='Exact Python Fraction; no floating-point geometric decisions or volume computation',
        dimension=3,symmetryFactor=8,orientation='standard ambient; every volume simplex has positive determinant',
        semanticScope='specific rational interval computation; no general volume definition for regions bounded by surfaces',
        checks=['rational unit and nonnegative boundary coordinates','recursive coordinate-face samples','all three axis tangents included',
            'persistent facet and clipping updates','positive determinant increment and cap simplices','nested exact rational bounds',
            'every outer vertex satisfies every tangent and coordinate inequality','quantitative polytope containments when alpha positive'],stages=stages)
    (ROOT/'polyhedra.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    render=[]
    for s in stages:
        item={k:s[k] for k in ['stage','mesh','samples','tangents','coordinatePlanes','axisTangents','decimalLower','decimalUpper','orthantDecimalLower','orthantDecimalUpper','gap','innerAdded','outerRemoved']}
        item['addedPoints']=len(s['updates'])
        for side in ['inner','outer']:
            item[side]=dict(vertices=[[float(Q(q)) for q in p] for p in s[side]['vertices']],faces=s[side]['faces'],edges=s[side]['edges'],volume=s[side]['volume'])
        render.append(item)
    (ROOT/'polyhedra-data.js').write_text('window.rationalBallStages='+json.dumps(render,separators=(',',':'))+';\n')
