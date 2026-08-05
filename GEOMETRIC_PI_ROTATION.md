# Direct geometric `pi / 2` rotation

`ComputableAnalysis.GeometricPiRotation` is the small, independently checked
route from the geometric arctangent computation to a valid represented complex
rotation. It does not import `PiProofs`, the large registry of pi
presentations.

```lean
import ComputableAnalysis.GeometricPiRotation

open ComputableAnalysis

#check GeometricPiRotation.halfPi
#check GeometricPiRotation.halfPi_equiv_geometricQuarterTurnOne
#check GeometricPiRotation.halfPi_width_le_two_div_succ
#check GeometricPiRotation.rotation
#check GeometricPiRotation.rotation_valid
#check GeometricPiRotation.imaginaryHalf
#check GeometricPiRotation.imaginaryHalf_valid
```

## Computation route

`halfPiUnscheduled` is literally `2 * arctan.geom(1)`. Its initial rational
box is `[1, 2]`; validity gives nested later boxes. The geometric sector
algorithm proves the width bound `8 / (m + 1)` for this doubled angle.

`halfPi` observes the same raw computation at the cofinal schedule `m = 4n+3`.
That finite reindexing yields the explicit bound

```text
width(halfPi.compute n) <= 2 / (n + 1).
```

`halfPi_equiv_geometricQuarterTurnOne` connects this scheduled raw real to the
normalized rational-circle quarter-turn computation. The result is a raw-real
equivalence, proved from rational interval overlap; no completed real number
is introduced.

## Complex construction

`RotationLift` evaluates the common rational factorial rotation series at the
midpoint of each `halfPi` box. Its input-motion radius is `16 * width`. The
final `rotation` is the finite intersection of all widened candidate boxes in
the prefix, so `rotation_valid` is a certificate about rational boxes:

- each candidate box is ordered;
- widths shrink;
- every later candidate lies in the earlier widened candidate;
- the widening radius shrinks.

`imaginaryHalf` is the valid coordinate embedding `i * halfPi`.

## Current boundary

This module proves a valid represented factorial rotation at the geometric
quarter-turn input. It does **not** yet prove that the rotation equals the
geometric point `(0, 1)`, and therefore does not claim Euler's identity. That
remaining bridge must compare the stabilized factorial boxes with the
rational-circle coordinate algorithm.
