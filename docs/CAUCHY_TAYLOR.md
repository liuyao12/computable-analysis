# Exact Cauchy-series reconstruction

The checked result is exact equality of computations, conditional on a
certified Cauchy representation. It is **not yet the general Taylor theorem
from complex differentiability**.

```lean
CauchyTaylor.Disk.eq_series (d : CauchyTaylor.Disk)
  (hz : QComplex.normSq (QComplex.sub z d.center) < d.radius * d.radius) :
  (d.function z).Equiv (d.series z)
```

`Disk.realPart_eq_series` and `Disk.imagPart_eq_series` give `RealRaw.Equiv`.
`Disk.series_valid` certifies the independent evaluator. The supplied radius
is a guaranteed open disk of equality, not necessarily the maximal radius.
No conclusion is made at its boundary.

## What is proved

* The finite complex geometric identity and the bound on the full Euclidean
  disk, using squared modulus rather than the smaller coordinate diamond.
* Finite weighted Cauchy samples expand into polynomial prefixes whose
  coefficients are the boundary moments, independent of the evaluation point.
* A certified Cauchy representation of an independently supplied function
  gives an exactly equivalent series computation at every rational complex
  point strictly inside the certified disk.
* Separately certified convergence of the boundary moments produces valid
  fixed `ComplexRaw` coefficients. Each polynomial sample lies inside the
  corresponding finite sum of those coefficients (`Moments.partialSum_contains_sample`).
* Translation and positive rational scaling expose arbitrary rational centers
  and radii. The internal smaller radius is selected rationally without a
  square-root computation.
* Every fixed finite Cauchy rule supplies a concrete instance. In particular,
  `reciprocal_eq_series` proves `1/(1-z)` equals its geometric-series computation
  on the full unit disk. `reciprocal_coefficients` identifies every coefficient
  with one. The example `z = 3/5 + 3i/5` checks the distinction between a disk
  and a coordinate diamond.

## Hypotheses, not hidden conclusions

`Representation f` provides finite rational quadrature rules with unit-circle
nodes, a uniform bound on their total absolute weights, valid function values,
and shrinking enclosures of `f` by the **Cauchy-kernel samples**. The quadrature
constant may depend on the smaller disk. It does not supply a Taylor expansion.
`Moments` separately certifies the convergence of each boundary monomial's
quadrature. `SeriesCertificate` combines these two inputs.

The runtime reads the finite rules, expands their kernels into finite
polynomials and intersects certified rational boxes. It does not call `f` or
use `f` as the runtime answer. The error estimates are proof dependencies;
the public conclusion is exact `Equiv`.

The remaining obligations for the theorem originally requested are:

1. Define the effective complex-differentiability certificate and construct
   the Cauchy representation and moment certificates from it.
2. Identify the moments with iterated derivatives divided by factorials.
3. Extend the input theorem from rational complex points to represented complex
   inputs, with representation independence.

No general polygon integral or parametrized circular integral was added.
This result consumes certified quadrature data; it does not construct the
contour integral for arbitrary holomorphic inputs. No exact maximal-radius or
nearest-singularity theorem is claimed.

## Files and dependency outline

* `CertifiedComplexApproximation.lean`: reusable sample-to-raw equivalence.
* `CauchyTaylorKernel.lean`: disk geometry and finite geometric identity.
* `CauchyTaylor.lean`: finite Cauchy samples and exact reconstruction.
* `CauchyTaylorCoefficients.lean`: fixed moment coefficients and finite sums.
* `CauchyTaylorDisk.lean`: public disk-radius theorem and real components.
* `CauchyTaylorExamples.lean`: fixed-rule and reciprocal instances.
* `scripts/check_cauchy_taylor.lean`: proof/import audit and exact examples.

Dependency outline:

```
Cauchy representation + moment convergence (supplied certificates)
                       |
       finite geometric identity on a Euclidean disk
                       |
        polynomial samples and rational enclosures
                       |
              valid independent series
                       |
      Disk.eq_series; real and imaginary RealRaw.Equiv
```

The general theorem does not yet depend on the geometric arctangent period:
normalization belongs to the supplied Cauchy weights. The existing geometric
pi and square normalization are preserved, but connecting them to a general
Cauchy representation remains open. Imports contain no Mathlib, and the new
runtime definitions use neither noncomputability nor unfinished proofs.

Run `lake env lean scripts/check_cauchy_taylor.lean` after building
`ComputableAnalysis.CauchyTaylorExamples`. The audit writes the checked theorem
family's project declaration closure to `tmp/cauchy-taylor-closure.txt`.
