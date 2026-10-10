import unittest
from fractions import Fraction as Q
from itertools import product
from random import Random
from rational_polytopes import ConvexPolytope, UnboundedPolytope, simplex_volume, determinant, dot
from orthant_ball import boundary_samples, orthant_polytopes, ball_volume_bounds, is_axis, OrthantBallComputation, new_boundary_samples

class ExactPolytopeTests(unittest.TestCase):
    def test_cubes_every_supported_dimension(self):
        for d in range(5):
            cube=ConvexPolytope.from_vertices(product([0,1],repeat=d))
            self.assertEqual(cube.volume(),1)
            self.assertEqual(cube.volume(-1),-1)
            self.assertTrue(all(simplex_volume(s)>0 for s in cube.triangulate()))

    def test_simplex_orientation_and_degeneracy(self):
        vertices=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
        self.assertEqual(simplex_volume(vertices),Q(1,6))
        vertices[-1],vertices[-2]=vertices[-2],vertices[-1]
        self.assertEqual(simplex_volume(vertices),-Q(1,6))
        self.assertEqual(ConvexPolytope.from_vertices(vertices).volume(),Q(1,6))
        self.assertEqual(ConvexPolytope.from_vertices([(0,0,0),(1,0,0),(0,1,0)]).volume(),0)
        self.assertEqual(ConvexPolytope.from_vertices([],dimension=3).volume(),0)

    def test_affine_laws_and_vertex_order(self):
        cube=list(product([Q(0),Q(1)],repeat=3))
        shear=[(x+2*y+Q(1,3),y+z-Q(2,5),z+7) for x,y,z in cube]
        stretch=[(Q(3,2)*x,y,z) for x,y,z in shear]
        reflection=[(-x,y,z) for x,y,z in stretch]
        for vertices,expected in [(shear,Q(1)),(stretch,Q(3,2)),(reflection,Q(3,2))]:
            Random(42).shuffle(vertices)
            self.assertEqual(ConvexPolytope.from_vertices(vertices).volume(),expected)

    def test_coplanar_collinear_duplicate_points(self):
        cube=list(product([0,1],repeat=3))+[(Q(1,2),0,0),(0,Q(1,2),Q(1,2)),(Q(1,2),Q(1,2),Q(1,2)),(0,0,0)]
        for seed in range(6):
            Random(seed).shuffle(cube)
            self.assertEqual(ConvexPolytope.from_vertices(cube).volume(),1)

    def test_halfspace_cubes_and_unbounded_rejection(self):
        for d in range(1,5):
            planes=[]
            for i in range(d):
                normal=tuple(Q(j==i) for j in range(d))
                planes.extend([(normal,Q(1)),(tuple(-x for x in normal),Q(0))])
            cube=ConvexPolytope.from_halfspaces(planes,[Q(1,2)]*d)
            self.assertEqual(cube.volume(),1)
        with self.assertRaises(UnboundedPolytope):
            ConvexPolytope.from_halfspaces([((-1,0),0),((0,-1),0)],(1,1))
        with self.assertRaises(TypeError):ConvexPolytope.from_vertices([(0.,0.)])

    def test_incremental_hull_against_enumerated_supporting_planes(self):
        from rational_polytopes import _enumerated_facets
        for seed in range(24):
            rng=Random(seed)
            points={tuple(Q(rng.randrange(-3,4)) for _ in range(3)) for _ in range(10)}
            poly=ConvexPolytope.from_vertices(points)
            if not poly.full_dimension():continue
            actual={(f.normal,f.offset) for f in poly.facets()}
            expected={(f.normal,f.offset) for f in _enumerated_facets(poly.vertices,3)}
            self.assertEqual(actual,expected)

    def test_sampling_axes_faces_and_refinement(self):
        for d in range(2,5):
            a=boundary_samples(d,2);b=boundary_samples(d,4)
            self.assertTrue(set(a)<=set(b))
            self.assertEqual(sum(is_axis(p) for p in b),d)
            for i in range(d):
                if d>=3:self.assertTrue(any(p[i]==0 and not is_axis(p) for p in b))
                self.assertTrue(all(dot(p,p)==1 and all(x>=0 for x in p) for p in b))

    def test_all_axis_tangents_and_exact_orthant_bounds(self):
        previous=None
        for m in [1,2,4,8]:
            samples,planes,inner,outer=orthant_polytopes(3,m)
            tangent=[a for a,b in planes if b==1]
            self.assertEqual(len(planes)-len(tangent),3)
            self.assertEqual(len(tangent),len(samples))
            self.assertEqual(sum(is_axis(p) for p in tangent),3)
            self.assertIn((Q(0),Q(0),Q(0)),inner.vertices)
            self.assertTrue(all(dot(a,x)<=b for a,b in planes for x in inner.vertices))
            self.assertTrue(all(all(x>=0 for x in p) for p in outer.vertices))
            # The axis tangents are included, so every coordinate is bounded by one.
            for i in range(3):self.assertEqual(max(p[i] for p in outer.vertices),1)
            lo,hi=inner.volume(),outer.volume()
            if previous:self.assertLessEqual(previous[0],lo);self.assertLessEqual(hi,previous[1])
            previous=(lo,hi)
            a=1-Q(4,m*m)
            if a>0:
                for f in inner.facets():
                    self.assertGreaterEqual(f.offset,0)
                    self.assertLessEqual(a*a*sum(max(x,0)**2 for x in f.normal),f.offset*f.offset)
                for x in outer.vertices:
                    self.assertLessEqual(dot(x,x),1/(a*a))
                    self.assertTrue(all(dot(f.normal,tuple(a*a*v for v in x))<=f.offset for f in inner.facets()))
        self.assertEqual(ball_volume_bounds(3,0),(Q(4,3),Q(8)))
        self.assertEqual(ball_volume_bounds(0,0),(1,1))
        self.assertEqual(ball_volume_bounds(1,0),(2,2))
        lo,hi=ball_volume_bounds(2,0)
        self.assertLess(lo,Q(22,7));self.assertGreater(hi,Q(3))

    def test_incremental_refinement_matches_independent_polytopes(self):
        from unittest.mock import patch
        for d in [2,3]:
            computation=OrthantBallComputation(d)
            for k in range(1,4):
                old_lower,old_upper=computation.lower,computation.upper
                original_volume=ConvexPolytope.volume
                def cap_volume(poly,orientation=1):
                    self.assertIsNot(poly,computation.inner,'Refinement recomputed the whole inner volume')
                    self.assertIsNot(poly,computation.outer,'Refinement recomputed the whole outer volume')
                    return original_volume(poly,orientation)
                with patch.object(ConvexPolytope,'volume',cap_volume):computation.refine()
                samples,planes,inner,outer=orthant_polytopes(d,2**k)
                self.assertEqual(computation.samples,set(samples))
                self.assertEqual(computation.lower,inner.volume())
                self.assertEqual(computation.upper,outer.volume())
                self.assertEqual(set(computation.outer.vertices),set(outer.vertices))
                self.assertEqual(computation.lower-old_lower,sum(u['innerIncrement'] for u in computation.last_updates))
                self.assertEqual(old_upper-computation.upper,sum(u['outerDecrement'] for u in computation.last_updates))
                for update in computation.last_updates:
                    self.assertTrue(all(simplex_volume(s)>0 for s in update['innerSimplices']))
                    self.assertTrue(all(simplex_volume(s)>0 for s in update['outerCapSimplices']))
                    self.assertEqual(sum(simplex_volume(s) for s in update['innerSimplices']),update['innerIncrement'])
                    self.assertEqual(sum(simplex_volume(s) for s in update['outerCapSimplices']),update['outerDecrement'])

    def test_local_updates_in_dimension_four(self):
        cube=ConvexPolytope.from_vertices(product([0,1],repeat=4))
        extended,added=cube.add_vertex((2,0,0,0))
        self.assertEqual(cube.volume()+sum(simplex_volume(s) for s in added),extended.volume())
        face,whole=cube.clip((1,0,0,0),Q(0))
        self.assertEqual(face.volume(),0)
        self.assertTrue(face.vertices and all(v[0]==0 for v in face.vertices))
        self.assertEqual(whole.volume(),1)
        kept,cap=cube.clip((1,1,0,0),Q(3,2))
        self.assertEqual(kept.volume()+cap.volume(),1)

if __name__=='__main__':unittest.main()
