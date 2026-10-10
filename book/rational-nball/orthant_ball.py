"""Rational positive-orthant ball approximations in every finite dimension."""
from functools import lru_cache
from itertools import product
from fractions import Fraction as Q
from rational_polytopes import ConvexPolytope, dot

@lru_cache(maxsize=None)
def boundary_samples(dimension,denominator):
    if dimension<1 or denominator<1:raise ValueError('Positive dimension and subdivision denominator required')
    if dimension==1:return ((Q(1),),)
    points=set()
    for indices in product(range(denominator+1),repeat=dimension-1):
        # The identical grid is used for every chart coordinate. Restrict its
        # Cartesian product to the rational parameter ball before mapping it.
        if sum(j*j for j in indices)>denominator*denominator:continue
        t=tuple(Q(j,denominator) for j in indices);s=dot(t,t)
        points.add(tuple(2*x/(1+s) for x in t)+((1-s)/(1+s),))
    # Coordinate faces need their own rational samples. This prevents a dyadic
    # grid's sparse points on sum(t_i^2)=1 from leaving the flat-face hull fixed.
    for face in range(dimension):
        for p in boundary_samples(dimension-1,denominator):
            points.add(p[:face]+(Q(0),)+p[face:])
    assert all(all(x>=0 for x in p) and dot(p,p)==1 for p in points)
    return tuple(sorted(points))

def is_axis(p):
    return sum(x==1 for x in p)==1 and all(x in (0,1) for x in p)

def orthant_polytopes(dimension,denominator):
    """Reference construction of one stage; the persistent evaluator refines instead."""
    if dimension<0:raise ValueError('Nonnegative dimension required')
    if dimension==0:
        body=ConvexPolytope.from_vertices([()]);return (),(),body,body
    samples=boundary_samples(dimension,denominator)
    origin=tuple(Q(0) for _ in range(dimension))
    inner=ConvexPolytope.from_vertices((origin,)+samples)
    tangents=tuple((p,Q(1)) for p in samples)
    coordinates=tuple((tuple(Q(-1) if i==j else Q(0) for j in range(dimension)),Q(0))
        for i in range(dimension))
    constraints=tangents+coordinates
    interior=tuple(Q(1,2*dimension) for _ in range(dimension))
    outer=ConvexPolytope.from_halfspaces(constraints,interior)
    return samples,constraints,inner,outer

def ball_volume_bounds(dimension,stage):
    """Stage zero uses denominator one; returned endpoints bound the whole ball."""
    if stage<0:raise ValueError('Nonnegative stage required')
    computation=OrthantBallComputation(dimension)
    for _ in range(stage):computation.refine()
    return computation.bounds()

@lru_cache(maxsize=None)
def new_boundary_samples(dimension,denominator):
    """Only the newly introduced dyadic chart grid and face-grid points."""
    if dimension<1:return ()
    if denominator<1 or denominator&(denominator-1):raise ValueError('Dyadic subdivision required')
    if dimension==1:return ((Q(1),),) if denominator==1 else ()
    points=set()
    for indices in product(range(denominator+1),repeat=dimension-1):
        if denominator>1 and all(j%2==0 for j in indices):continue
        if sum(j*j for j in indices)>denominator*denominator:continue
        t=tuple(Q(j,denominator) for j in indices);s=dot(t,t)
        points.add(tuple(2*x/(1+s) for x in t)+((1-s)/(1+s),))
    for face in range(dimension):
        for p in new_boundary_samples(dimension-1,denominator):points.add(p[:face]+(Q(0),)+p[face:])
    return tuple(sorted(points))

class OrthantBallComputation:
    """A persistent nested rational interval computation, not a preassigned volume.

    Initialize once at the axis simplex/unit cube. Each refinement adds visible
    inner pyramids and subtracts outer caps, keeping all axis tangents.
    """
    def __init__(self,dimension):
        samples,self.halfspaces,self.inner,self.outer=orthant_polytopes(dimension,1)
        self.dimension=dimension;self.stage=0;self.denominator=1;self.samples=set(samples)
        self.lower=self.inner.volume();self.upper=self.outer.volume()
        self.last_updates=()

    def refine(self):
        from rational_polytopes import simplex_volume
        denominator=2*self.denominator
        new_points=tuple(p for p in new_boundary_samples(self.dimension,denominator) if p not in self.samples)
        updates=[]
        for p in new_points:
            self.inner,added=self.inner.add_vertex(p)
            increment=sum((simplex_volume(s) for s in added),Q(0))
            self.outer,cap=self.outer.clip(p,Q(1))
            cap_simplices=cap.triangulate()
            decrement=cap.volume()
            self.lower+=increment;self.upper-=decrement
            assert increment>=0 and decrement>=0 and self.lower<=self.upper
            updates.append(dict(point=p,innerIncrement=increment,outerDecrement=decrement,
                innerSimplices=added,outerCapSimplices=cap_simplices))
        self.samples.update(new_points)
        self.halfspaces=tuple(self.halfspaces)+tuple((p,Q(1)) for p in new_points)
        self.stage+=1;self.denominator=denominator;self.last_updates=tuple(updates)
        return self

    def bounds(self):
        factor=2**self.dimension
        return factor*self.lower,factor*self.upper
