"""Independent verification of the saved incremental rational certificates.

Unlike the stage evaluator, this checker recomputes whole-polytope volumes
from saved vertices. It does not define volume for regions bounded by surfaces.
"""
from pathlib import Path
from fractions import Fraction as Q
import json
from rational_polytopes import ConvexPolytope, point, simplex_volume, dot, mean, _normal
from orthant_ball import boundary_samples, is_axis
ROOT=Path(__file__).parent

def check():
    data=json.loads((ROOT/'polyhedra.json').read_text());assert data['symmetryFactor']==8
    previous=None;previous_samples=set();updates_checked=0;simplices_checked=0
    for stage in data['stages']:
        models={side:ConvexPolytope.from_vertices(stage[side]['vertices']) for side in ['inner','outer']}
        for side,poly in models.items():
            assert poly.volume()==Q(stage[side]['volume']),(stage['stage'],side,'fresh volume mismatch')
            vertices=tuple(point(p) for p in stage[side]['vertices']);center=mean(vertices)
            edges={};used=set()
            for face in stage[side]['faces']:
                points=[vertices[i] for i in face];normal=_normal(points);offset=dot(normal,points[0])
                assert all(dot(normal,p)<=offset for p in vertices)
                assert simplex_volume((center,)+tuple(points))>0
                used.update(face)
                for a,b in zip(face,face[1:]+face[:1]):edges[a,b]=edges.get((a,b),0)+1
            assert all(n==1 and edges.get((b,a))==1 for (a,b),n in edges.items())
            assert len(used)-len(edges)//2+len(stage[side]['faces'])==2
        samples={p for p in models['inner'].vertices if any(p)}
        assert samples==set(boundary_samples(3,stage['mesh']))
        assert all(dot(p,p)==1 and all(x>=0 for x in p) for p in samples)
        planes=[(point(h['normal']),Q(h['offset'])) for h in stage['halfspaces']]
        assert {a for a,b in planes if b==1}==samples
        assert sum(is_axis(a) for a,b in planes if b==1)==3
        assert sum(b==0 for a,b in planes)==3
        assert all(dot(a,x)<=b for a,b in planes for x in models['outer'].vertices)
        lo,hi=Q(stage['inner']['volume']),Q(stage['outer']['volume'])
        assert Q(stage['decimalLower'])<=8*lo<=8*hi<=Q(stage['decimalUpper'])
        assert stage['samples']==len(samples) and stage['tangents']==len(samples)
        if previous is None:
            assert (lo,hi)==(Q(1,6),Q(1));assert not stage['updates']
        else:
            assert stage['previousOrthantBounds']==[str(q) for q in previous]
            assert previous_samples<=samples
            new_points=[point(u['point']) for u in stage['updates']]
            assert len(new_points)==len(set(new_points)) and set(new_points)==samples-previous_samples
            current_planes=[(a,b) for a,b in planes if b==0 or a in previous_samples]
            inner_sum=Q(0);outer_sum=Q(0);current_samples=set(previous_samples)
            for update in stage['updates']:
                p=point(update['point']);deltas=[]
                for name in ['innerSimplices','outerCapSimplices']:
                    simplices=[tuple(point(v) for v in simplex) for simplex in update[name]]
                    volumes=[simplex_volume(s) for s in simplices]
                    assert all(v>0 for v in volumes)
                    simplices_checked+=len(volumes);deltas.append(sum(volumes,Q(0)))
                    if name=='innerSimplices':
                        assert all(s[0]==p and all(v in current_samples or not any(v) for v in s[1:]) for s in simplices)
                    else:
                        vertices={v for simplex in simplices for v in simplex}
                        assert all(dot(a,v)<=b for a,b in current_planes for v in vertices)
                        assert all(dot(p,v)>=1 for v in vertices)
                        cap=ConvexPolytope.from_vertices(vertices,dimension=3)
                        assert cap.volume()==sum(volumes,Q(0))
                assert deltas==[Q(update['innerIncrement']),Q(update['outerDecrement'])]
                inner_sum+=deltas[0];outer_sum+=deltas[1]
                current_samples.add(p);current_planes.append((p,Q(1)));updates_checked+=1
            assert inner_sum==Q(stage['innerAdded']) and outer_sum==Q(stage['outerRemoved'])
            assert lo==previous[0]+inner_sum and hi==previous[1]-outer_sum
            assert previous[0]<=lo<=hi<=previous[1]
        if stage['alpha'] is not None:
            a=Q(stage['alpha'])
            assert all(f.offset>=0 and a*a*sum(max(q,0)**2 for q in f.normal)<=f.offset**2 for f in models['inner'].facets())
            assert all(dot(x,x)<=1/(a*a) for x in models['outer'].vertices)
        previous=(lo,hi);previous_samples=samples
    print(f'PASS: {len(data["stages"])} stages; {updates_checked} incremental point updates; {simplices_checked} positive determinant pieces; independent exact whole-polytope and cap checks; all axis tangents retained; no float arithmetic')
if __name__=='__main__':check()
