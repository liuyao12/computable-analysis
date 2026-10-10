from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
ROOT=Path(__file__).parent

def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def det(a,b,c):return dot(a,cross(b,c))
def plane(v,face):
 a,b,c=(v[i] for i in face);normal=cross(sub(b,a),sub(c,a));return normal,dot(normal,a)
def hull(v):
 seed=None
 for ids in combinations(range(len(v)),4):
  a,b,c,d=(v[i] for i in ids)
  if det(sub(b,a),sub(c,a),sub(d,a)):
   seed=ids;break
 assert seed
 center=tuple(sum(v[i][j] for i in seed)/4 for j in range(3))
 faces=[]
 for face in combinations(seed,3):
  normal,b=plane(v,face)
  if dot(normal,center)>b:face=(face[0],face[2],face[1])
  faces.append(face)
 for i,p in enumerate(v):
  if i in seed:continue
  visible=[]
  for face in faces:
   normal,b=plane(v,face)
   if dot(normal,p)>b:visible.append(face)
  if not visible:continue
  horizon={}
  for a,b,c in visible:
   for x,y in [(a,b),(b,c),(c,a)]:
    if (y,x) in horizon:del horizon[y,x]
    else:horizon[x,y]=True
  removed=set(visible);faces=[f for f in faces if f not in removed]
  faces.extend((x,y,i) for x,y in horizon)
 # Exact supporting-halfspace and oriented closed-mesh certificate.
 edges={};used=set()
 for face in faces:
  normal,b=plane(v,face);assert b>0
  assert all(dot(normal,p)<=b for p in v)
  a,c,d=face;used.update(face)
  for x,y in [(a,c),(c,d),(d,a)]:edges[x,y]=edges.get((x,y),0)+1
 assert all(n==1 and edges.get((y,x))==1 for (x,y),n in edges.items())
 assert len(used)-len(edges)//2+len(faces)==2
 volume=sum(det(v[a],v[b],v[c]) for a,b,c in faces)/6
 assert volume>0
 return faces,volume

def samples(m):
 axes=[tuple(F(s if j==i else 0) for j in range(3)) for i in range(3) for s in [-1,1]]
 if not m:return axes
 out=set(axes)
 for j in range(-m,m+1):
  for k in range(-m,m+1):
   u,w=F(j,m),F(k,m);s=u*u+w*w;d=1+s
   p=(2*u/d,2*w/d,(1-s)/d)
   for sign in [-1,1]:out.add((p[0],p[1],sign*p[2]))
 return axes+sorted(out-set(axes))

def make(m):
 points=samples(m);assert all(dot(p,p)==1 for p in points)
 inner,lo=hull(points)
 polar=set()
 for a,b,c in inner:
  p,q,r=points[a],points[b],points[c];den=det(p,q,r)
  x=tuple((cross(q,r)[i]+cross(r,p)[i]+cross(p,q)[i])/den for i in range(3))
  assert all(dot(x,p)<=1 for p in points);polar.add(x)
 outerPoints=sorted(polar);outer,hi=hull(outerPoints)
 assert lo<hi
 scale=10**6;dl=lo.numerator*scale//lo.denominator;du=-(-hi.numerator*scale//hi.denominator)
 return dict(mesh=m,samples=len(points),inner=dict(vertices=[[str(q) for q in p] for p in points],faces=inner,volume=str(lo)),outer=dict(vertices=[[str(q) for q in p] for p in outerPoints],faces=outer,volume=str(hi)),decimalLower=f'{dl/scale:.6f}',decimalUpper=f'{du/scale:.6f}',gap=str(hi-lo))

if __name__=='__main__':
 stages=[]
 for m in [0,1,2,4,8]:
  s=make(m);stages.append(s);print(m,s['samples'],s['decimalLower'],s['decimalUpper'],flush=True)
 for a,b in zip(stages,stages[1:]):
  assert F(a['inner']['volume'])<=F(b['inner']['volume'])
  assert F(b['outer']['volume'])<=F(a['outer']['volume'])
 data=dict(arithmetic='Exact Python Fraction; no floating-point hull decisions or volume computation',checks=['unit sphere identities','all supporting halfspaces','paired oriented mesh edges','Euler characteristic','every polar vertex satisfies every tangent inequality','nested exact volume bounds'],stages=stages)
 (ROOT/'polyhedra.json').write_text(json.dumps(data,separators=(',',':')))
 render=[]
 for s in stages:
  item={k:s[k] for k in ['mesh','samples','decimalLower','decimalUpper','gap']}
  for side in ['inner','outer']:
   item[side]=dict(s[side]);item[side]['vertices']=[[float(F(q)) for q in p] for p in s[side]['vertices']]
  render.append(item)
 (ROOT/'polyhedra-data.js').write_text('window.rationalBallStages='+json.dumps(render,separators=(',',':'))+';\n')
