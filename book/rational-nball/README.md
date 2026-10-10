# Rational ball volume, Chapter 2

The reader addition gives a general-dimensional mathematical proof using
rational stereographic boundary samples, exact inner and outer polytopes,
and a finite radial-shell recurrence. It uses the chapter's orientation
convention for volume. No integral or Gamma-function proof is used.

The simplex determinant expression is derived from finite dissection,
translation and determinant-one invariance, and unit-cube normalization.
The mathematical proof is written in `chapter-section.html`.

## Checked finite arithmetic

`FiniteRationalBall.lean` uses only native Lean rational arithmetic. For Lean
4.33.0-rc2, from this directory:

```sh
lean -o FiniteRationalBall.olean FiniteRationalBall.lean
LEAN_PATH=. lean CheckFiniteRationalBall.lean
```

Twelve general-dimensional endpoints are checked, including the rational
sphere chart, finite power bounds, partition power-sum convergence estimate,
and shell summation by parts. `lean-audit.txt` records standard Lean axioms
only. No admission is used. This is **not** a completed Lean proof that the
constructed geometric ball volume equals the recurrence formula.

The remaining geometric obligations are:

- Oriented simplex volume from the volume axioms, including rational stretching.
- Rational triangulations and their independence; product-region volume.
- Boundary-chart coverage and the inner/outer containment gap.
- Valid represented ball volume, scaling, invariance, and recurrence agreement.

## Convex bodies over rational coordinates

No general polytope type is necessary. `RationalConvexBodies.lean` uses
`Fin n → ℚ`, `convexHull ℚ`, and finite rational halfspace presentations.
It checks convexity, rational-ball containment, nested refinement, and
boundedness of the tangent body when axis samples are present.
`RationalSimplexLinearAlgebra.lean` checks translation and determinant
transformation identities for `determinantCoefficient`, an algebraic
expression that has not been identified with axiomatic volume in Lean.

Download `rational-geometry-proof.tar.gz` for the isolated five-file package.

This supplementary package pins Mathlib revision
`51e6992efd06126df61a496bebf8f49482a4e129`. In a separate directory, place
`lakefile.lean`, `lean-toolchain`, `RationalProofAudit.lean`,
`RationalConvexBodies.lean`, and `RationalSimplexLinearAlgebra.lean`, then run:

```sh
lake update
lake exe cache get Mathlib/Analysis/Convex/Hull.lean Mathlib/Tactic/Linarith.lean Mathlib/LinearAlgebra/Matrix/ToLin.lean
lake build
lake env lean RationalConvexBodies.lean
lake env lean RationalSimplexLinearAlgebra.lean
```

Both source files run a transitive declaration-dependency audit and print
standard-axiom audits. No theorem depends on Mathlib real/complex scalars,
measure, or integration. Mathlib's broader module import closure does contain
real/complex modules, so this package is isolated from the native foundation.
The two audit text files record the successful checks. They do not supply the
remaining geometric volume theorem.

## Exact three-dimensional construction

```sh
python3 generate_polyhedra.py
```

This uses only the Python standard library and `Fraction`. Convex-hull
visibility, support checks, vertex intersections, orientation, and determinant
volumes are rational. `polyhedra.json` contains exact certificates;
`polyhedra-data.js` contains rounded coordinates solely for display. The
computed decimal endpoints are rounded outwards. These runtime certificates
are separate from the Lean proofs.

## Reader maintenance

```sh
python3 apply_chapter_overlay.py /path/to/base/ch-circle-sphere.html ch-circle-sphere.html
```

The addition is idempotent, preserves the earlier text and anchors, and moves
"What precedes calculus" to Section 2.13. Publication overlays only this
chapter and its assets on a previous successful Pages artifact.
