# Rational signed triangle area under general linear maps

This companion contains the exact source closure checked for
`ComputableAnalysis.RationalTriangleAreaTransform`. It uses the existing
rational points and signed twice-area API. It imports no Mathlib real or
complex numbers.

With the Lean version in `lean-toolchain` installed, run:

```sh
python3 verify.py --lean lean
```

The verifier checks the recorded source hashes, cold-builds every module in
an isolated temporary directory, and audits seven theorem endpoints. The
original successful checker output and source manifest are in `verification/`.

`triangleSignedArea_affine` proves that applying a rational matrix and common
translation to all three vertices multiplies signed area by the determinant.
It covers arbitrary matrices, including singular maps, and arbitrary vertex
orientations. Determinant-one invariance, singular collapse and coordinate
swap reversal follow as corollaries. Composition and the corresponding
dot-product Gram-matrix law are checked as well.

This is an opt-in companion; the main library root exports are unchanged.
The broader geometry/sector proposal is deferred. No quarter-turn, numerical
distance, sector area or new geometric area axiom is needed for these proofs.
