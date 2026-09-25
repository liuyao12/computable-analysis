# Polygonal Cauchy theory

This is a native computable-analysis foundation in progress. It does not
complete Fuchs’s criterion or Painlevé–Gambier classification.

The public import is `ComputableAnalysis.ComplexAnalysis`. Its objects are
rational complex points, finite oriented triangles, and `ComplexRaw` interval
computations. No Mathlib real or complex numbers are imported. The quadrature
layer does not depend on the order of a differential equation.

## Checked statements

`Triangle.subdivide` proves the exact four-triangle cancellation identity
for every rational triangle and every sampled function. `Triangle.affine_zero`
proves the zero midpoint sum for a complex-affine function.

`CauchyData.cauchy` and `ChainData.cauchy` prove exact `ComplexRaw.Equiv` to
zero for a triangle and a finite triangle collection, respectively. Their
explicit analytic hypotheses are executable mesh and evaluation schedules,
valid represented function values, shrinking sample-box widths, and local
complex-affine approximations on every leaf triangle. At outer stage \(n\),
the mesh depth \(d_n\ge n\) and each leaf’s uniform approximation error is at most
\(M2^{-d_n}/(n+1)\). The proved boundary estimate is
\[
  \lVert S_n\rVert_1\le MP/(n+1),
\]
where \(P\) is the sum of the original triangle perimeters. The constructor
intersects widened boxes around actual computed sums. It does not define the
quadrature to be zero. No quadrature-vanishing assertion is a certificate field.
A quadratic-remainder specialization gives the geometric estimate
\(MP2^{-n}\) and instantiates the general interface. The polynomial
\(z^2\) is a concrete, nonconstant client.

`SquarePole` adapts the existing sampled-square development to this small
foundation surface, retaining only its arctangent period layer. Its evaluator
uses literal transformed reciprocal pullbacks, supplied rational tags, and
finite-prefix stabilization. Midpoints and left endpoints are distinct
instantiations. `quadrature_equiv_twoPiI` identifies both with the pre-existing
geometric circle computation:
\[
  \oint_{\partial S}\frac{dz}{z-a}\simeq2\pi i.
\]

`Square.residue` combines that computation with two certified regular
triangle contours. For an arbitrary valid represented complex residue
\(\rho\), and a supplied regular part \(g\) carrying the local data above,
its split quadrature satisfies
\[
  \oint_{\partial S}\left(\frac{\rho}{z-a}+g(z)\right)\,dz
  \simeq2\pi i\rho.
\]
The quadrature is a positive rational square centered at the pole. The
regular-part quadratures may choose independent internal schedules;
`Square.triangulate` proves finite diagonal cancellation for a common mesh.
`Square.residue_independent` proves agreement under equivalent residue
representations, changed certified tags, and changed certified regular parts.
`quadratic_simple_pole_residue` instantiates the family
\(\rho/(z-a)+z^2\) on every such square. The residue itself need not be rational.

## Remaining bridges

The local approximation hypotheses are not claimed to have been derived
from an unrestricted represented complex-derivative interface. The existing
first-jet algebra alone does not establish those estimates. The present
function-value interface samples rational complex arguments; evaluating and
reconstructing general analytic functions at represented complex arguments
requires its own invariance and approximation bridges.

The next obligations are:

1. Construct the local approximation schedules from the existing analytic
   function evaluators and their derivative certificates.
2. Prove agreement with arbitrary certified tagged partitions and refinements.
3. Construct the geometric adapters for arbitrary triangulated punctured
   polygons and their small pole squares. Finite triangle-chain cancellation
   is proved; a general residue-transport theorem is not.
4. Treat higher-order principal parts and general winding numbers.
5. Extend \((f(z)-f(a))/(z-a)\) across the center with proved local data,
   obtaining Cauchy’s value formula and then derivative formulas.
6. Connect those formulas to represented-input Taylor reconstruction,
   continuation, and general finite-dimensional differential systems.

No one of these steps is replaced by an interface assuming its conclusion.

## Presentation and verification

The reader uses the fixed example \(p(z)=1/z\), \(q(z)=1\), showing
coefficient scaling, triangle cancellation, pole contours, and a classical
Bessel logarithmic branch in a side panel. Its floating-point solution
animation is explanatory; it is not a Lean monodromy or continuation proof.
All mathematical notation is typeset with the reader’s MathJax renderer.

Run `lake build ComputableAnalysis` and
`lake env lean scripts/check_polygonal_cauchy.lean`. The latter audits the
actual elaborated dependencies, rejects `sorryAx` and Mathlib imports, and
checks that the local residue proof depends on the arctangent normalization
and geometric circle computation. Inherited native-decision axioms are
listed in the audit rather than hidden.
