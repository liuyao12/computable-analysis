# Computation first, then its geometry

Chapter 2 now begins with the existing quarter-circle raw computation, its
literal rational stage sums, and validity. The following sections develop
area on rational vectors and cyclic vertex lists, then identify the same raw
stage endpoints with the inscribed and circumscribed polygon areas. The
circumference, solid, and surface material follows unchanged except numbering.

## Checked finite geometry

`ComputableAnalysis.RationalGeometry` depends only on finite rational algebra.
A `Polygon` is a list of rational `Point`s with an implicit closing edge. A
change of first vertex is `startAt P k`; reversing the traversal reverses area.
The empty and degenerate cases are included. Area retains orientation, and is
called simply area throughout the chapter.

The key result is `triangulationArea_startAt`: the explicit fan algorithm
returns the same area whatever the chosen starting vertex. The stronger
`fanArea_startAt` permits any rational fan origin, independently of the cyclic
cut. No simplicity, convexity or interior-origin hypothesis is used. A fan
for a concave or self-crossing cycle is an oriented triangle sum, not a claim
of a disjoint geometric triangulation of its interior.

The normalized alternating bilinear area specification is inhabited by the
determinant and characterized by `AreaForm.unique`. No new global axiom is
introduced. The affine determinant law gives translations, proper rotations,
reflection sign and homothety scaling. Tetrahedral volume has the matching
finite subdivision and cubic-scaling identities; a general polyhedral-surface
or scissors-congruence classification is not claimed.

## The original computation remains the original computation

`QuarterCircleGeometry.raw` reuses `ArctanGeometry.arctanGeom 1`. Its validity
is independent of the new polygon interpretation. The new `raw_width` proves
the sharp displayed upper bound 4^(-n) for the existing dyadic stage gap.

`raw_compute_polygon_areas` is an exact equality of rational stage intervals,
not just equivalence of limiting values. It connects the old circle point
records to the new finite geometry and proves that the concrete positive
boundary orientations agree with the earlier magnitude convention.
`raw_compute_any_fans` allows either stage polygon to use any rational fan
origin and any starting vertex. No previous circle or integral evaluator is
modified. The integral is not redefined as area.

## Publication and proof provenance

The new scoped import is `ComputableAnalysis.GeometryFoundation`. CI checks
these supplemental sources against the same pinned mathematical snapshot used
by the already published comparisons, and exports their exact declarations
and reference paths. Two new maps explain fan independence and the quarter-
circle stage interpretation. They are native checked maps, not new Mathlib
comparison results or newly measured proof-size claims.

The old map entries, benchmarks, numerical records, Chapter 1 flashcards and
animation bytes remain unchanged. New maps carry their own source revision.
The complete inherited axiom lists are exported, including existing native-
computation dependencies of the circle development. Absence of `sorryAx` does
not mean the inherited foundation is axiom-free.

Verify with:

```sh
lake build ComputableAnalysis.GeometryFoundation
lake env lean book/checks/ExportRationalGeometry.lean
```

The exporter checks independence of the finite geometry from RealRaw, circle
and integral declarations, independence of numerical validity from the new
interpretation, and absence of Mathlib, native noncomputable declarations and
transitive sorryAx in the checked roots. It also emits five literal stage
outputs; a separate rational-arithmetic test checks their displayed formulas.
