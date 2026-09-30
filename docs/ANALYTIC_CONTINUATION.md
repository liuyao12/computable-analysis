# Analytic continuation: checked foundation and remaining theorem

The primary uniqueness target is the identity theorem: two holomorphic
functions on the **same connected open domain** that agree on a nonempty
open neighborhood agree everywhere on that domain. Simple connectedness is
not required. Agreement on a line interval or at distinct points accumulating
at an interior point also suffices. For \(\sin(1/z)\), the accumulation point
of the zeros lies outside the domain.

Logarithm continued above and below the origin is the apparent counterexample
to explain first. Suitable slit-plane branches agree on the right component
of their intersection and differ on the left component. Their intersection
is disconnected, so the identity theorem does not propagate between those
components. Taylor reconstruction and overlapping disks explain how agreement
propagates when the common domain is connected.

The monodromy theorem is a separate existence/path-independence statement:
if a starting germ can be continued along every path in a simply connected
domain, its terminal germ is independent of the route and gives a global
holomorphic extension. Neither pathwise continuation nor extension across
singularities follows from simple connectedness alone.

**The general identity theorem and the full analytic monodromy theorem are
not yet proved.**
The new foundation proves the finite transport argument, represented germ
algebra, derivative uniqueness, and local holomorphic gluing. It also supplies
actual chart-chain semantics and a fully instantiated affine client. The
remaining analytic and geometric bridges below are not assumed away.
A new realization constructor handles supplied locally coherent chart selection,
and reflection preserves holomorphic open charts and their overlaps.

## What is now checked

| Layer | Result and scope | Source |
| --- | --- | --- |
| Represented neighborhoods | Coordinate bounds, triangle inequality, rational-radius restriction; arbitrary valid complex inputs | `Continuation/Neighborhood.lean` |
| Germs | Equality on an open neighborhood is an equivalence relation; it respects represented base points and implies value equality; equality is local | `Continuation/Germ.lean` |
| Derivatives | Complex derivative uniqueness on open domains; transfer across neighborhood equality; equality of derivatives of equal germs | `Continuation/Derivative.lean` |
| Local gluing | A supplied represented map with supplied local holomorphic models is holomorphic; derivative and continuity radii are constructed | `Continuation/Gluing.lean` |
| Coherent-chart realization | A total chart selector with local germ coherence yields an actual represented evaluator, representation invariance, holomorphicity, and comparison with other realizations | `Continuation/Realization.lean` |
| Reflected charts | Conjugate input and output; transport the derivative, continuity radii, and open-overlap agreement | `Continuation/Reflection.lean` |
| Differential equations | Equal holomorphic germs have equal derivative germs; with holomorphic derivatives, their second-order residuals agree for arbitrary valid represented coefficient values | `Continuation/DifferentialEquation.lean` |
| Actual continuation | A finite chain contains holomorphic charts, whole-segment coverage, and neighborhood agreement; concatenation preserves this property | `Continuation/Chain.lean` |
| Domain geometry | Vertices and interpolation parameters may be irrational; convexity constructs routes and finite triangle contractions | `Continuation/Domain.lean` |
| Finite homotopy | Stationary steps, backtracking, triangle moves, and composition; contractions are geometric data, independent of functions | `Continuation/FinitePath.lean` |
| Finite monodromy | Local stationary, inverse, and triangle transport laws imply invariance under finite fillings and a unique parallel extension | `Continuation/Transport.lean` |
| Analytic interpretation | Transports realized by actual chart chains give path-independent terminal germs and exact represented endpoint values | `Continuation/Monodromy.lean` |
| Concrete client | Affine germ equality determines both represented coefficients; the entire affine family supplies every local transport law and actual chart chains | `Continuation/Affine.lean` |
| Fuchs client | The solution \(y=z^2\) changes between two actual holomorphic chart computations, satisfies \(z^2y''-zy'=0\), and agrees with the scaled jet used by the rational-ray growth theorem | `AlgebraicODE/FuchsContinuation.lean` |

The public import is `ComputableAnalysis.Continuation`. No Mathlib module is
imported. The finite algebra uses shared rational samples inside interval
boxes, and the derivative proof uses positive rational displacements; neither
uses an ambient completed field or a compactness argument.

## Exact statements, rather than endpoint-only comparisons

A local germ consists of a holomorphic map near a valid represented base
point. For some positive rational radius, two representatives must agree at
**every valid represented point** in that neighborhood, and both maps must
be defined there. Equality at one point is insufficient.

The derivative theorem proves

\[
D f(a)\simeq d\quad\text{and}\quad D f(a)\simeq e
\quad\Longrightarrow\quad d\simeq e.
\]

Its proof compares the two first-order remainders at a small rational real
displacement, cancels the positive displacement, and makes the remaining
coordinate bound arbitrarily small. The holomorphic derivative definition
still controls all complex directions. Neighborhood equality transports the
entire derivative modulus, rather than merely identifying formal jets.

The gluing theorem uses actual local charts for an independently supplied
represented map. Near each base point it compares neighboring derivative
computations with the derivative in one fixed chart, then transfers that
chart's continuity estimate. `Realization.holomorphic` now constructs the evaluator itself from a total
chart selector, domain evidence, rational neighborhood radii, and local germ
coherence. Evaluation selects the chart at the input and uses that chart's
boxes. Representation invariance is derived from local agreement even when
equivalent inputs select different charts. The selector is data, not a
classically chosen quotient representative or a domain-membership decision.
This completes realization for such supplied coherent charts. An arbitrary
abstract germ section still needs executable selection and local stability.

For transport, the local triangle law has the form

\[
T_{bc}(T_{ab}(s))\simeq T_{ac}(s).
\]

The finite monodromy proof inducts on stationary, backtracking, and triangle
moves to derive

\[
T_p(s)\simeq T_q(s)
\]

for supplied finite homotopies. Neither this global path independence nor
uniqueness is a field of the transport structure. A chosen route supplies a
parallel section; its uniqueness follows from finite path induction. The
same uniqueness argument compares two parallel sections using a connecting
path without requiring simple connectedness.

`GermSystem` connects these transports to actual holomorphic chart chains.
Its fibers are a **specified family of continuable germs**, not all germs at
an arbitrary point: a generic germ can encounter a singularity along an edge.
The affine instance constructs the local data. The general analytic instance
remains to be constructed.

## Application audit: differential equations and Fuchs

The continuation and differential-equation layers now have a checked shared
client, but a general ODE solver cannot yet be passed directly to continuation.
The distinctions below are mathematical obligations, not missing imports.

- `Holomorphic.derivativeMap` preserves validity and representation invariance
  on the original domain. `AgreeAt.derivative` proves equality on a smaller
  neighborhood, using half the supplied agreement radius. Iterating it
  requires holomorphicity of the derivative; that extra evidence is not
  inferred from the current first-order interface.
- `secondOrderResidual_congr` compares the actual values of
  \(Ay''+By'+Cy\) for equal germs, with arbitrary valid represented complex
  coefficient values. It does not assume the equation or its uniqueness.
  Nor does it prove that an arbitrary continuation chart satisfies the ODE
  throughout its whole domain. General propagation of the residual still
  needs an identity theorem or a separate solution comparison.
- `ContinuationExample` supplies \(y(z)=z^2\) for
  \(z^2y''-zy'=0\). Both derivatives are analytic witnesses at arbitrary
  valid represented complex inputs. `twoCharts` changes from direct squaring
  to \((z+1)^2-2z-1\), proves neighborhood agreement, and covers both edges.
  `recentered_equation` uses the general residual comparison. Because this
  particular solution is entire, it can continue through the origin even
  though the normalized equation has a singular coefficient there.
- The same example identifies every coefficient of the existing Frobenius
  solver's exponent-two factor: its constant coefficient is one and all
  higher coefficients vanish. This does not upgrade the general
  `FrobeniusConvergence.factorRaw` to a complex holomorphic map. General
  series differentiation, represented complex inputs, and branches of
  \(z^r\) and \(\log z\) remain necessary for other Frobenius modes.
- `ray_value` and `ray_scaled_derivative` identify all four coordinates of
  the example's `RaySolution` with the holomorphic scaled jet \((y,zy')\)
  on the positive real ray. Its finite-difference remainder has norm
  \(3|h|^2\), giving the explicit radius \(\varepsilon/3\).
  The existing Fuchs theorem then yields the checked, deliberately coarse
  bound \(\lVert Y(a)\rVert_1\le6/a^3\) for \(0<a\le1\).
- For general functions, pointwise complex derivative radii do not supply
  the uniform interval radii and refined-box sample estimates required by
  `LinearSolution`. A general holomorphic-to-ray adapter therefore remains
  open. So do sector bounds, the Fuchs converse, local ODE existence and
  uniqueness for the relevant equation families, and continuation of a
  fundamental matrix with its basis-change and loop laws. The Bessel
  monodromy illustration remains an illustration.

Run `lake build ComputableAnalysis.Continuation
ComputableAnalysis.AlgebraicODE.FuchsContinuation`, then
`lake env lean scripts/check_continuation.lean`. The audit includes the
new application, its exact ray comparisons and growth theorem, a two-edge
change of chart, and executable complex and rational-ray values. The finite
transport theorem's local laws are not being claimed for general ODE germs.

## What remains before the full analytic monodromy theorem

1. **General analytic uniqueness.** Prove an identity theorem for the existing
   represented `FunctionTheory.Holomorphic` interface. The affine identity
   theorem is checked, but not the theorem for arbitrary holomorphic maps.
   A Cauchy/Taylor route still needs reconstruction from holomorphicity at
   arbitrary represented inputs, coefficient uniqueness, and the local
   zero/identity argument. The current Cauchy/Taylor disk result assumes a
   Cauchy representation and evaluates at rational complex inputs; it cannot
   be cited as this missing bridge.
2. **Uniqueness and local stability of actual chart chains.** Use analytic
   uniqueness to compare different chains along the same route, then derive
   the local inverse and triangle laws for the reachable germs of a supplied
   initial germ. Construct the finite charts and their neighborhoods from
   the supplied continuation data. Do not replace these proofs by giving a
   `GermSystem` the desired laws as unexplained fields.
3. **Continuous homotopy to finite filling.** `FiniteSimplyConnected` describes
   a finite polygonal presentation. It is not silently identified with
   arbitrary topological simple connectedness. Prove a finite subdivision
   theorem for a supplied homotopy with suitable quantitative domain/cover
   control. The convex-domain constructor is checked; a general homotopy-cover
   algorithm and its termination are not. No universal effective Lebesgue
   number follows merely from pointwise moduli.
4. **Coherent chart selection from pathwise continuation.** The evaluator,
   representation invariance, and holomorphicity are now constructed by
   `Realization.holomorphic` once a total locally coherent chart selector is
   supplied. Derive that selector and its neighborhood radii from the
   path-independent continuation section. This is tied to local stability in
   step 2, not a missing global gluing law. Route functions, chart selections,
   and evaluation functions must have executable implementations when a
   computable constructor is claimed.

Continuation along every path is a genuine hypothesis of the monodromy
statement, not something that every starting germ satisfies. For a concrete
function one must construct that evidence on the requested domain. No
logarithm, square-root, arctangent, or Bessel monodromy identity is newly
claimed by this foundation.

## Verification

```sh
lake build ComputableAnalysis.Continuation
lake env lean scripts/check_continuation.lean
lake build ComputableAnalysis ComputableAnalysis.Blueprint
lake exe checkdecls blueprint/lean_decls
```

The dedicated audit checks the elaborated theorem dependencies, rejects
unfinished proofs, Mathlib imports, and new axioms, and exposes one inherited
`Basic` native-decision certificate explicitly. The new modules introduce no
native-decision axioms. A runtime regression transports an affine chart over
a two-edge polygonal route and checks its exact endpoint box. The theorem
regressions retain arbitrary represented coefficients and base points.

## Function-specific methods and examples

The reader now has a separate analytic-continuation chapter. Its identity
example is \(\sin(1/z)\): zeros \(1/(n\pi)\) accumulate at the excluded
origin, not at an interior point of its holomorphic domain. The identity
theorem must retain both its interior-point and connectedness hypotheses.
The general identity theorem, complex sine-composition chart, zero sequence,
and natural-boundary example are not yet formalized here.

The holomorphicity and continuation skills now distinguish direct remainder
estimates, series, local equations, functional equations, and reflection.
`Holomorphic.reflect` and `AgreeAt.reflect` prove the reflected open-chart
and overlap steps. Holomorphicity across the boundary seam in the full
Schwarz principle remains unproved. The reader also explains Gamma's
recurrence and a lacunary natural boundary; these are mathematical examples
and construction recipes, not new Lean theorem claims.
