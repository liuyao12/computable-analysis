# Comparison notes

This project develops its own proof-oriented foundation for computable real
and complex analysis. The main documentation describes that foundation on its
own terms: rational interval algorithms, stage-indexed refinement, certified
domains, and explicit equivalence proofs.

Mathlib and other analysis projects remain useful comparison points. They use
different abstractions, including completed number systems, general topology,
measure theory, and broad reusable theorem libraries. This repository makes
different design choices because it wants the computation and its proof
certificate to remain visible.

The comparison is intentionally secondary. A theorem developed here should be
evaluated first by the certificate it provides:

```text
domain → stage algorithm → validity → finite estimate → equivalence
```

The absence of a classical wrapper is not, by itself, a defect in the project;
it is often the point of the construction. Conversely, a declaration here is
not automatically a general classical theorem: its hypotheses and certificate
determine its scope.
