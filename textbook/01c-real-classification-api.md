# Chapter 1 API note: value predicates and raw names

The canonical mathematical predicates are now defined on the quotient type
`ComputableAnalysis.Real`: rational, irrational, algebraic over the rationals, and
transcendental over the rationals. Polynomial evaluation uses a finite list
of rational coefficients and quotient-real arithmetic.

The raw API records the same properties through quotient values. Existing
`RealCompute.Irrational` remains available and is equivalent to quotient
irrationality for every valid raw name. `RealCompute.Algebraic` and
`RealCompute.Transcendental` take a validity proof and are invariant under
`RealCompute.Equiv`.

A `RealCompute.Certified` pairs one computation with its validity proof.
Its rationality and irrationality predicates agree with those of its
quotient value. Use `ComputableAnalysis.Real` for public mathematical
statements and `RealCompute` when the theorem refers to a specific computation.

The [rationality supplement](01a-rationality-and-transcendence.md) explains
how the predicates control the continued-fraction computation. The
[pi classification section](01b-pi-classification-theorems.md) records the
status of the companion proof developments.
