"""Finite convex polytopes over Fraction, with exact triangulated volume.

Vertex presentations allow degenerate and empty bodies. Halfspace conversion
requires a supplied strict rational interior point and certifies boundedness.
Every volume simplex is oriented in the standard ambient orientation.
The module uses no floating-point geometric decisions.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations
from math import factorial

class UnboundedPolytope(ValueError):
    pass

def rational(value):
    if not isinstance(value, (int, str, Q)):
        raise TypeError('Coordinates must be integers, rational strings, or Fraction')
    return Q(value)

def point(values):
    return tuple(rational(x) for x in values)

def sub(a, b):
    return tuple(x-y for x,y in zip(a,b))

def dot(a, b):
    return sum((x*y for x,y in zip(a,b)), Q(0))

def determinant(rows):
    """Gaussian elimination over Q; determinant of the empty matrix is one."""
    a=[list(point(r)) for r in rows];n=len(a)
    if any(len(r)!=n for r in a):raise ValueError('Square matrix required')
    value=Q(1)
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]),None)
        if pivot is None:return Q(0)
        if pivot!=j:a[j],a[pivot]=a[pivot],a[j];value=-value
        p=a[j][j];value*=p
        for i in range(j+1,n):
            ratio=a[i][j]/p
            for k in range(j+1,n):a[i][k]-=ratio*a[j][k]
    return value

def rank(rows):
    if not rows:return 0
    a=[list(point(r)) for r in rows];h=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(h,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[h],a[pivot]=a[pivot],a[h];p=a[h][j]
        for i in range(h+1,len(a)):
            ratio=a[i][j]/p
            for k in range(j,len(a[0])):a[i][k]-=ratio*a[h][k]
        h+=1
        if h==len(a):break
    return h

def simplex_volume(vertices):
    """Volume with the orientation specified by the ordered vertices."""
    vertices=tuple(point(v) for v in vertices)
    d=len(vertices)-1
    if d<0 or any(len(v)!=d for v in vertices):raise ValueError('Simplex dimension mismatch')
    # Rows instead of columns give the same determinant.
    return determinant([sub(v,vertices[0]) for v in vertices[1:]])/factorial(d)

def standard_orientation(vertices):
    vertices=list(vertices);value=simplex_volume(vertices)
    if not value:raise ValueError('Degenerate simplex in full-dimensional triangulation')
    if value<0:vertices[-1],vertices[-2]=vertices[-2],vertices[-1]
    assert simplex_volume(vertices)>0
    return tuple(vertices)

def mean(vertices):
    return tuple(sum((v[j] for v in vertices),Q(0))/len(vertices) for j in range(len(vertices[0])))

def _normal(points):
    d=len(points[0]);rows=[sub(p,points[0]) for p in points[1:]]
    return tuple((-1)**j*determinant([r[:j]+r[j+1:] for r in rows]) for j in range(d))

def _normalized(normal,offset):
    scale=abs(next(x for x in normal if x))
    return tuple(x/scale for x in normal),offset/scale

def _polygon(points):
    """Indices of the counterclockwise planar hull, omitting collinear points."""
    ids=sorted(range(len(points)),key=lambda i:points[i])
    def turn(i,j,k):
        a,b=sub(points[j],points[i]),sub(points[k],points[i])
        return a[0]*b[1]-a[1]*b[0]
    def chain(indices):
        out=[]
        for i in indices:
            while len(out)>1 and turn(out[-2],out[-1],i)<=0:out.pop()
            out.append(i)
        return out
    return chain(ids)[:-1]+chain(reversed(ids))[:-1]

@dataclass(frozen=True)
class Facet:
    normal: tuple
    offset: Q
    vertices: tuple

def _enumerated_facets(vertices,d):
    found={}
    for ids in combinations(range(len(vertices)),d):
        ps=[vertices[i] for i in ids];normal=_normal(ps)
        if not any(normal):continue
        b=dot(normal,ps[0]);sides=[dot(normal,p)-b for p in vertices]
        if any(s>0 for s in sides) and any(s<0 for s in sides):continue
        if all(s==0 for s in sides):continue
        if any(s>0 for s in sides):normal=tuple(-x for x in normal);b=-b
        normal,b=_normalized(normal,b)
        face=tuple(i for i,p in enumerate(vertices) if dot(normal,p)==b)
        found[face]=Facet(normal,b,face)
    return tuple(found.values())

def _facets3(vertices):
    # Incremental hull locates supporting planes. Coplanar triangles and
    # collinear edges are rebuilt as exact facet polygons before consumption.
    seed=[0];basis=[]
    for i in range(1,len(vertices)):
        row=sub(vertices[i],vertices[0])
        if rank(basis+[row])>len(basis):basis.append(row);seed.append(i)
        if len(seed)==4:break
    if len(seed)!=4:raise ValueError('Full dimension required')
    center=mean([vertices[i] for i in seed]);triangles=[]
    def plane(face):
        ps=[vertices[i] for i in face];normal=_normal(ps);return normal,dot(normal,ps[0])
    for f in combinations(seed,3):
        normal,b=plane(f)
        if dot(normal,center)>b:f=(f[0],f[2],f[1])
        triangles.append(f)
    for i,p in enumerate(vertices):
        if i in seed:continue
        visible=[f for f in triangles if dot(plane(f)[0],p)>plane(f)[1]]
        if not visible:continue
        horizon={}
        for a,b,c in visible:
            for x,y in [(a,b),(b,c),(c,a)]:
                if (y,x) in horizon:del horizon[y,x]
                else:horizon[x,y]=True
        removed=set(visible);triangles=[f for f in triangles if f not in removed]
        triangles.extend((a,b,i) for a,b in horizon)
    found={}
    for f in triangles:
        normal,b=plane(f)
        if not any(normal):continue
        assert all(dot(normal,p)<=b for p in vertices),'Hull support failure'
        normal,b=_normalized(normal,b)
        ids=tuple(i for i,p in enumerate(vertices) if dot(normal,p)==b)
        drop=next(i for i,x in enumerate(normal) if x)
        projected=[vertices[i][:drop]+vertices[i][drop+1:] for i in ids]
        polygon=tuple(ids[i] for i in _polygon(projected))
        # Orient each polygon so its normal is outward in ambient coordinates.
        if dot(_normal([vertices[i] for i in polygon[:3]]),normal)<0:polygon=tuple(reversed(polygon))
        found[(normal,b)]=Facet(normal,b,polygon)
    facets=tuple(found.values());edges={};used=set()
    for f in facets:
        assert dot(f.normal,center)<f.offset
        used.update(f.vertices)
        for a,b in zip(f.vertices,f.vertices[1:]+f.vertices[:1]):edges[a,b]=edges.get((a,b),0)+1
    assert all(n==1 and edges.get((b,a))==1 for (a,b),n in edges.items()),'Facet boundary is not closed'
    assert len(used)-len(edges)//2+len(facets)==2,'Facet Euler certificate failure'
    adjacent={i:set() for i in used}
    for a,b in edges:adjacent[a].add(b)
    reached={next(iter(used))};todo=list(reached)
    while todo:
        for j in adjacent[todo.pop()]-reached:reached.add(j);todo.append(j)
    assert reached==used,'Disconnected hull boundary'
    return facets

@dataclass
class ConvexPolytope:
    dimension: int
    vertices: tuple
    _facet_cache: tuple = None

    @classmethod
    def from_vertices(cls,vertices,dimension=None):
        vertices=tuple(sorted(set(point(p) for p in vertices)))
        if dimension is None:
            if not vertices:raise ValueError('Supply the dimension for an empty body')
            dimension=len(vertices[0])
        if dimension<0 or any(len(p)!=dimension for p in vertices):raise ValueError('Dimension mismatch')
        return cls(dimension,vertices)

    def full_dimension(self):
        return bool(self.vertices) and rank([sub(v,self.vertices[0]) for v in self.vertices[1:]])==self.dimension

    def facets(self):
        if not self.full_dimension():return ()
        if self._facet_cache is not None:return self._facet_cache
        d=self.dimension;v=self.vertices
        if d==0:result=()
        elif d==1:
            result=(Facet((Q(-1),),-v[0][0],(0,)),Facet((Q(1),),v[-1][0],(len(v)-1,)))
        elif d==3:result=_facets3(v)
        else:result=_enumerated_facets(v,d)
        self._facet_cache=result
        return result

    @classmethod
    def from_halfspaces(cls,halfspaces,interior):
        """Convert a bounded rational H-presentation, certifying boundedness.

        Each constraint is (normal, offset) and means normal dot x <= offset.
        The caller supplies a strict rational interior point. An unbounded
        body raises UnboundedPolytope rather than producing a fake volume.
        """
        interior=point(interior);d=len(interior);constraints=[];polar=[]
        for normal,offset in halfspaces:
            normal=point(normal);offset=rational(offset)
            if len(normal)!=d:raise ValueError('Halfspace dimension mismatch')
            if not any(normal):
                if offset<0:raise ValueError('Infeasible zero-normal constraint')
                continue
            slack=offset-dot(normal,interior)
            if slack<=0:raise ValueError('Supplied point is not strictly interior')
            constraints.append((normal,offset));polar.append(tuple(x/slack for x in normal))
        if d==0:return cls.from_vertices([()],dimension=0)
        dual=cls.from_vertices(polar,dimension=d)
        if not dual.full_dimension():raise UnboundedPolytope('Constraint normals do not span a bounded body')
        facets=dual.facets()
        if any(f.offset<=0 for f in facets):raise UnboundedPolytope('The recession cone is nontrivial')
        vertices={tuple(interior[i]+f.normal[i]/f.offset for i in range(d)) for f in facets}
        assert all(dot(a,x)<=b for x in vertices for a,b in constraints)
        return cls.from_vertices(vertices,dimension=d)

    def facet_simplices(self,face):
        """Rational simplices of one boundary facet, before ambient orientation."""
        d=self.dimension;v=self.vertices
        if d==1:return ((v[face.vertices[0]],),)
        if d==3:
            return tuple((v[face.vertices[0]],v[b],v[c])
                for b,c in zip(face.vertices[1:-1],face.vertices[2:]))
        drop=next(i for i,x in enumerate(face.normal) if x)
        projected=[v[i][:drop]+v[i][drop+1:] for i in face.vertices]
        def lift(p):
            value=(face.offset-sum((face.normal[i]*p[i if i<drop else i-1]
                for i in range(d) if i!=drop),Q(0)))/face.normal[drop]
            return p[:drop]+(value,)+p[drop:]
        return tuple(tuple(lift(p) for p in simplex)
            for simplex in ConvexPolytope.from_vertices(projected).triangulate())

    def triangulate(self):
        """Canonical ambient orientation; every emitted simplex has positive determinant."""
        d=self.dimension;v=self.vertices
        if not self.full_dimension():return ()
        if d==0:return (((),),)
        if d==1:return ((v[0],v[-1]),)
        center=mean(v)
        return tuple(standard_orientation((center,)+simplex)
            for face in self.facets() for simplex in self.facet_simplices(face))

    def add_vertex(self,new_point):
        """Extend the hull and return only the new pyramid simplices.

        The 3D boundary is updated along its horizon, reusing old facet planes.
        Other dimensions enumerate the new boundary but still compute volume
        solely from the visible-facet pyramids, never from the enlarged body.
        """
        new_point=point(new_point);d=self.dimension
        if len(new_point)!=d or not self.full_dimension():raise ValueError('Full-dimensional starting hull required')
        visible=[f for f in self.facets() if dot(f.normal,new_point)>f.offset]
        if not visible:return self,()
        added=tuple(standard_orientation((new_point,)+simplex)
            for f in visible for simplex in self.facet_simplices(f))
        if d!=3:return ConvexPolytope.from_vertices(self.vertices+(new_point,)),added
        v=self.vertices+(new_point,);k=len(v)-1;center=mean(self.vertices)
        horizon={}
        for f in visible:
            for a,b in zip(f.vertices,f.vertices[1:]+f.vertices[:1]):
                if (b,a) in horizon:del horizon[b,a]
                else:horizon[a,b]=True
        groups={}
        def register(normal,offset,ids):
            normal,offset=_normalized(normal,offset)
            groups.setdefault((normal,offset),set()).update(ids)
        for f in self.facets():
            side=dot(f.normal,new_point)-f.offset
            if side<=0:register(f.normal,f.offset,f.vertices+((k,) if side==0 else ()))
        for a,b in horizon:
            ids=(a,b,k);normal=_normal([v[i] for i in ids])
            if not any(normal):continue
            offset=dot(normal,v[a])
            if dot(normal,center)>offset:normal=tuple(-x for x in normal);offset=-offset
            register(normal,offset,ids)
        facets=[]
        for (normal,offset),ids in groups.items():
            ids=tuple(sorted(ids));drop=next(i for i,x in enumerate(normal) if x)
            projected=[v[i][:drop]+v[i][drop+1:] for i in ids]
            polygon=tuple(ids[i] for i in _polygon(projected))
            if len(polygon)<3:continue
            if dot(_normal([v[i] for i in polygon[:3]]),normal)<0:polygon=tuple(reversed(polygon))
            facets.append(Facet(normal,offset,polygon))
        return ConvexPolytope(d,v,tuple(facets)),added

    def clip(self,normal,offset):
        """Cut the current body by one rational halfspace; return kept body and cap.

        In 3D, clip and reuse the existing facet polygons. In other dimensions,
        retain old vertices and exact crossings of old edges. Neither route
        recomputes the volume of the kept body.
        """
        normal=point(normal);offset=rational(offset);d=self.dimension
        if len(normal)!=d or not self.full_dimension():raise ValueError('Full-dimensional starting body required')
        distances=[dot(normal,p)-offset for p in self.vertices]
        empty=ConvexPolytope.from_vertices([],dimension=d)
        if all(q<=0 for q in distances):return self,empty
        if all(q>=0 for q in distances):
            boundary=[p for p,q in zip(self.vertices,distances) if q==0]
            return ConvexPolytope.from_vertices(boundary,dimension=d),self
        if d!=3:
            facets=self.facets();edges=[]
            for i,j in combinations(range(len(self.vertices)),2):
                shared=[f.normal for f in facets if dot(f.normal,self.vertices[i])==f.offset
                    and dot(f.normal,self.vertices[j])==f.offset]
                if rank(shared)==d-1:edges.append((i,j))
            crossing=[]
            for i,j in edges:
                a,b=distances[i],distances[j]
                if a*b<0:
                    ratio=a/(a-b)
                    crossing.append(tuple(x+ratio*(y-x) for x,y in zip(self.vertices[i],self.vertices[j])))
            kept=[p for p,q in zip(self.vertices,distances) if q<=0]+crossing
            cap=[p for p,q in zip(self.vertices,distances) if q>=0]+crossing
            return ConvexPolytope.from_vertices(kept,dimension=d),ConvexPolytope.from_vertices(cap,dimension=d)
        crossing=set();kept_faces=[];cap_faces=[]
        def clipped_polygon(face,keep_negative):
            polygon=[self.vertices[i] for i in face.vertices];out=[]
            for a,b in zip(polygon,polygon[1:]+polygon[:1]):
                da,db=dot(normal,a)-offset,dot(normal,b)-offset
                if (da<=0 if keep_negative else da>=0):out.append(a)
                if da*db<0:
                    ratio=da/(da-db)
                    cut=tuple(x+ratio*(y-x) for x,y in zip(a,b))
                    out.append(cut);crossing.add(cut)
                if da==0:crossing.add(a)
            return out
        for face in self.facets():
            kept_faces.append((face.normal,face.offset,clipped_polygon(face,True)))
            cap_faces.append((face.normal,face.offset,clipped_polygon(face,False)))
        kept_faces.append((normal,offset,list(crossing)))
        cap_faces.append((tuple(-x for x in normal),-offset,list(crossing)))
        def build(face_data):
            cleaned=[]
            for a,b,points in face_data:
                points=tuple(sorted(set(points)))
                if len(points)<3:continue
                drop=next(i for i,x in enumerate(a) if x)
                ids=_polygon([p[:drop]+p[drop+1:] for p in points])
                if len(ids)<3:continue
                polygon=tuple(points[i] for i in ids)
                if dot(_normal(polygon[:3]),a)<0:polygon=tuple(reversed(polygon))
                a,b=_normalized(a,b);cleaned.append((a,b,polygon))
            vertices=tuple(sorted({p for _,_,polygon in cleaned for p in polygon}))
            lookup={p:i for i,p in enumerate(vertices)}
            facets=tuple(Facet(a,b,tuple(lookup[p] for p in polygon)) for a,b,polygon in cleaned)
            return ConvexPolytope(d,vertices,facets)
        return build(kept_faces),build(cap_faces)

    def volume(self,orientation=1):
        if orientation not in (-1,1):raise ValueError('Orientation must be one or negative one')
        return orientation*sum((simplex_volume(s) for s in self.triangulate()),Q(0))

    def mesh3(self):
        if self.dimension!=3 or not self.full_dimension():raise ValueError('A full-dimensional 3D body is required')
        return tuple((f.vertices[0],b,c) for f in self.facets()
            for b,c in zip(f.vertices[1:-1],f.vertices[2:]))
