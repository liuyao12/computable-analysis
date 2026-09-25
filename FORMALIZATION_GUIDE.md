# Formalization Guide

## Construct the objects; prove their laws

This is the project's organizing principle. General theorems may say: given
constructions of the objects in the statement, with proved validity and the
stated mathematical properties, the conclusion follows. Proving that such
objects can be constructed under broadly applicable or minimal hypotheses is
a separate theorem, not a prerequisite for proving the conditional law.

Formal definability alone is insufficient: a raw evaluator needs validity,
a represented function needs its domain and invariance, and a derivative,
integral, root, or solution needs evidence of that mathematical role. State
these hypotheses explicitly and identify what the conclusion adds. A record
that already contains the desired conclusion is an interface or transport
package, not an independent proof of that conclusion.

Keep three tasks distinct: construct particular objects; prove laws about
supplied objects; prove comparisons between constructions. A completed
conditional law need not solve the first task for every possible input.
For a requested concrete example, however, construct its required evidence;
do not replace the example by an assumption of its result. Keep proved
existence theorems and the full stated domains of existing results.

Choose sufficient hypotheses that support a useful finite proof. Do not seek
the most general existence criteria as a default milestone. Methods belong
in the formalization skill; finite algorithms, mathematical predicates, and
proofs belong in Lean. Reusable proof-data records are optional. Internal
precision choices may be bundled or hidden after their agreement is proved;
genuine domain, branch, convergence, and solution assumptions remain visible.

This principle applies equally to algebra, geometry, limits and series,
calculus, function theory, ODEs, and PDEs. The previous exactness and
computable-foundation rules remain in force. See the
[project-wide contract audit](docs/CONSTRUCTION_FIRST_AUDIT.md) for the source
coverage, concrete examples, and the distinction between conditional laws
and unsupported interfaces.

**Arctangent function-theory showcase (2026-09-23).**
`ArctanTaylor.convergence_iff` classifies convergence of the ordinary Taylor
partial sums for every rational input: exactly the closed unit interval.
`geometric_converges` reuses the independent series-to-geometric-arctangent
bridge; `not_converges` excludes every represented limit outside the interval.
The new reader centers function theory and real-variable Taylor behavior.
Arbitrary represented inputs and the general Cauchy-to-Taylor chain remain
explicit obligations. See [the theorem ledger](docs/ARCTAN_TAYLOR.md).


**Polygonal Cauchy foundation (2026-09-23).**
`ComplexAnalysis` proves finite triangle cancellation, valid Cauchy
quadrature computations from explicit local complex-affine approximation data, and a local
simple-pole residue identity on positive rational squares. The pole
normalization uses actual sampled pullbacks and the existing arctangent and
geometric circle computation. Residues may be arbitrary valid represented
complex values. Concrete nonconstant polynomial clients are checked.
General derivative-to-model construction, partition agreement, punctured
polygon transport, higher-order residues, Cauchy value/derivative formulas,
and analytic continuation remain open. Fuchs and Painlevé remain partial.
See [the precise theorem ledger](docs/POLYGONAL_CAUCHY.md).


## Computable foundations, exact mathematical theorems

This is the repository-wide rule for choosing interfaces and deciding when a
formalization is complete.

The foundation layer is computable. Construct values with rational interval
algorithms and prove validity using explicit error bounds, convergence rates,
separation bounds, and finite estimates. Do not introduce Mathlib's real
numbers or an abstract completion to bypass these obligations. Arbitrary valid
represented inputs and coefficients, including irrational ones, are allowed.
`RealRaw.compute` is a function, not a computability certificate. Preserve
executable algorithms for executable inputs; inspect numerical witness
selection before calling an existential result an executable constructor.

The mathematical layer states exact results over valid represented reals.
Equality of real values means `RealRaw.Equiv` between valid raw computations;
it does not require literal equality of programs or their finite-stage boxes.
Package validity and quantitative certificates so callers can use the exact
theorem without reconstructing its error analysis. Keep the quantitative
lemmas available for computational use.

For example, the intended public shape of the sine derivative theorem is
\[
  D\sin(x) \simeq \cos(x)
  \qquad\text{for every valid represented real }x,
\]
where \(\simeq\) denotes `RealRaw.Equiv`. This is a specification of the theorem
shape, not a claim that a particular derivative API is already implemented.
The proof must connect the derivative construction to the value of cosine.
A rational-input secant estimate or a formal differentiation identity is an
intermediate lemma; it is not the requested theorem for all represented real
inputs. Prove the required real-input evaluation bridges and invariance under
equivalent input representations.

Integration may be constructed on monotone pieces and assembled across
rational partitions or shrinking brackets around irrational turning points.
Those choices belong in the construction and proof. Prove the refinement,
partition-independence, or overlap-agreement results needed to expose an exact
integral identity without making callers choose the internal breaks. Likewise,
a global derivative identity should not ask callers for monotonicity pieces
or local charts that the proof can construct and reconcile internally.

Retain genuine mathematical domain hypotheses: validity, integrability or its
constructive evidence when it cannot be derived, pole avoidance, branch
restrictions, and explicitly supplied factorization data where required.
Hiding implementation choices means constructing or packaging the needed
evidence, not dropping it or assuming the desired conclusion. State the full
intended domain first, then use rational intervals and local certificates
inside the proof. Do not weaken a requested exact theorem to rational inputs,
symbolic differentiation, or an uninstantiated certificate interface merely
because those are the current APIs. If a bridge is missing, identify and prove
it; report intermediate progress as such until the exact theorem is established.

### Point-set topology boundary

The user permits abstract point-set topology from Mathlib when the selected
imports and their transitive dependencies do not introduce Mathlib real or
complex numbers. This is an exception to the earlier blanket import ban.
Audit the actual pinned dependency closure before adding an import. Keep
number computations, analytic estimates, and contour algorithms on the
project foundation. Mathlib's standard `Path` uses the real unit interval;
continue using finite polygonal paths unless a permitted replacement is
constructed. No Mathlib topology import is introduced by the arctangent work.

### Whole-chunk enclosures define each integral

Begin with the particular integrand and domain. On each chunk, certify an
outer enclosure of the function's value rectangles throughout that chunk.
Proved increasing or decreasing behavior selects endpoint bounds; otherwise
use an explicit function-specific range estimate. Multiply the range by the
real length or the finite oriented complex displacement, and sum. Prove
nesting (or justified intersection) and shrinking widths. Point samples,
validity of an unrelated number, and endpoint formulas alone are insufficient.

Straight complex segments are subdivided geometrically. Do not define their
integrals by first postulating a parametrized real integral. A pullback may
subsequently compare two finite constructions. Keep rotation, orientation,
whole-domain pole avoidance, and approximation error explicit.

Use `Integral.EnclosureConstructionFor` for direct real enclosure sums and
`Integral.EnclosureRealizationFor` for a computation compared with shrinking
whole-cell sums. `enclosureRealizationOfEffectiveFTC` retains the local range
proofs already present in a derivative-bound FTC certificate. The old
`CandidateFor`, `SampleConstruction`, and monotone-candidate wrappers only
package numerical computations: they do not themselves establish integrability.
For complex sums, `PolygonalIntegralCertificate` additionally requires
`EntireBoxFunctionRaw.Sound`; a positive mesh is required from the first stage.
See [the complete native-source audit](docs/INTEGRAL_ENCLOSURES.md).

### Computation methods are skill guidance

The choice of a method for a definite integral or an infinite series belongs
in the [formalization skill](skills/computable-analysis-formalization/SKILL.md#methods-belong-in-the-skill)
and its strategy references. Lean defines the particular finite computation
and proves the bounds, convergence, and agreement theorems for it. Reusable
lemmas and optional records of proof data support those proofs; no single
record or universal integral or infinite-sum operator is required to express
all examples. A method described in the skill is not itself a proved theorem.

### State integration formulas as definite integrals

Do not introduce a separate formal notion of primitive or indefinite integral.
Requests for a closed-form primitive mean a definite-integral identity with an
explicit base point. The public theorem has the shape
\[
  \int_a^x f(t)\,dt \simeq G_a(x),
  \qquad G_a(a) \simeq 0,
\]
or equivalently
\[
  \int_a^x f(t)\,dt \simeq F(x)-F(a).
\]
Here the integral and the displayed expression are valid raw-real computations,
and \(\simeq\) is `RealRaw.Equiv`. Construct the integral and prove this exact
identity; a derivative identity alone does not complete an integration theorem.

Require the entire segment between \(a\) and \(x\), including its endpoints,
to lie in a certified domain where the integrand is defined and integrable and
the displayed expression uses valid branches. For rational expressions, give
the necessary denominator-apart evidence throughout that segment; checking
only the endpoints is insufficient. Use the oriented integral when
\(x<a\). Do not extend an endpoint formula across a singularity or combine
components separated by poles. Internal monotone subdivisions and coordinate
charts still belong in the proof and must agree where they overlap.

Derivative lemmas and elementary expression construction remain useful proof
steps. Existing identifiers or historical progress notes containing `Primitive`
or “primitive” do not establish a separate public mathematical notion; their
integration-facing results must be packaged as the definite-integral identities
above. This convention applies in particular to rational functions and rational
functions of sine and cosine.

**Trigonometric primitive formulas and finite substitution (2026-09-23).**
`ComputableTrigonometricRationalization.RepresentedFactorization.primitive_correct`
computes an elementary formula for every rational sine/cosine expression with
arbitrary computable coefficients, given a certified factorization of the
half-angle pullback denominator. It proves represented equivalence of the
formal angle derivative with the original expression. Both circle charts
preserve undefined divisions. `PrimitiveChangeOfVariables` supplies the
finite chain-rule error proof and conversion to `HasDerivativeOnInterval`,
including zero finite inner increments. This is not yet the full interval
primitive corollary: the rational formula assembly and the instantiation of
the finite composition certificate for the represented angle evaluator remain.

**Concrete derivatives with computable coefficients (2026-09-23).**
`ComputableLogarithmChart.Coefficient.hasDerivative` and
`weightedHasDerivative` construct actual finite secant certificates for local
logarithm charts and computable constant multiples. The simple-pole bridge
identifies the derivative with the independently evaluated reciprocal, including
irrational poles. The arctangent candidates are the usual odd Taylor sums.
`ComputableQuadraticPrimitives` supplies the logarithm and normalized angle
base primitives for \(Q(x)=(x-a)^2+b^2\), using arbitrary computable coefficients
and finite reciprocal certificates for nonzero \(b\). Their derivatives are
proved equivalent to \(2(x-a)/Q(x)\) and \(1/Q(x)\). Irrational examples are
checked. The full finite assembly, the bridge from a supplied positive
quadratic constant to its width, and sine/cosine transport remain unfinished.

**Computable coefficients in factored integration (2026-09-23).**
`ComputableFactoredAlgebra.FactoredRational` accepts numerator, leading,
linear, and quadratic coefficients built from arbitrary certified `Real`
parameters. `certifyFactors` uses finite rational interval tests for positive
quadratic constants and separated residual denominators; it does not decide
real equality. Partial fractions and logarithm/arctangent formulas are
computed. `primitive_correct` proves `RealRaw.Equiv` between the represented
formal derivative and the original factored rational function. An example
uses the repository's square-root bisection for irrational numerator and
factor coefficients. No FTA, decomposition, or derivative law is assumed.
The analytic assembly for these general coefficients and trigonometric
transport remain unfinished; the actual analytic theorem below still has
rational linear factors as its scope.

**All positive even zeta values via Euler’s sine product (2026-09-23).**
The isolated [Mathlib companion](book/euler-proof/README.md) now proves
$\zeta(2m)=(-1)^{m+1}B_{2m}(2\pi)^{2m}/(2(2m)!)$ for every $m\ge1$.
The proof uses the justified logarithmic derivative of the sine product,
an absolutely convergent double series, and uniqueness of power-series
coefficients to identify the Bernoulli generating function. Its dependency
audit excludes Fourier theory, previous zeta evaluations, and the earlier
Basel evaluation. Specializations at $4$, $6$, and $8$ are checked too.
This is a Mathlib result; a native interval sine-product certificate and
cross-foundation bridge remain open.


**Analytic primitives for rationally split denominators (2026-09-23).**
`RationalPrimitiveAssembly.splitPrimitive` constructs an elementary evaluator
and an actual `HasDerivativeOnInterval` for every rational numerator and
admissible list of rational linear pole blocks, near each rational center
where the denominator is nonzero. `radius_pos` proves the computed
neighborhood is nondegenerate; `denominator_near` proves it avoids all poles.
`ofFactorization` transfers the result to a `RatFun` with a checked rational
linear factorization, including its leading coefficient. Partial-fraction
coefficients are computed by repeated synthetic division, not supplied.
The evaluator witness includes polynomials, normalized logarithms, reciprocal
powers, rational scaling, addition, and interval restriction. All derivatives
use the project's finite secant certificates; no Mathlib or custom axioms.
General algebraic factorization, quadratic analytic assembly, and represented
trigonometric transport remain open.

**Rational primitive algebra (2026-09-23).**
`RationalPrimitiveFormula` computes and checks formal primitives of supplied
rational linear/quadratic partial fractions of arbitrary multiplicity.
`TrigonometricRationalization` compiles every rational circle expression and
its half-angle Jacobian to `RatFun`, preserving all undefined cases. Two
charts cover the rational circle. The general analytic theorem is still open:
algebraic partial-fraction construction, represented elementary evaluators,
finite-difference differentiation soundness, and angle-chart transport remain.
See [the exact theorem ledger](docs/RATIONAL_PRIMITIVES.md); do not promote
`formalDerivative` identities to `HasDerivativeOnInterval` certificates.

**Squared-cosine showcase (2026-09-23).**
The reader now evaluates $\int_0^{1/2}\cos^2(\pi x)\,dx=1/4$ by two
unconditional Lean proofs of the same rational interval program. One uses
finite reflected sums and the circle identity; the other constructs the
product primitive and applies the finite FTC. Validity and an explicit
width bound are established independently of the value. The source and
reproduction instructions are in [the checked reader proof package](book/cosine-square/README.md).
This package extends the pinned published foundation; it is built and audited
separately from the current root import. The earlier cosine primitive remains
supporting mathematics. The RMS discussion is explanatory, not an additional
formalized application.



**Basel and the Euler sieve (2026-09-22).**
`ComputableAnalysis.Basel.RealZeta` exports the unconditional identity
$\zeta(2)=\pi^2/6$ for geometric $\pi$, including the real-input zeta function.
Finite Leibniz-square rearrangements supply an explicit rational error budget.
The finite Euler sieve proves prime unboundedness assuming irrationality of
$\pi^2$. Irrationality is already proved in the pinned published Cartwright
development; importing that theorem and connecting its implementation to this
newer source version remains open. The general even-value formulas remain open in the native foundation; the separate Euler/Mathlib companion now proves them. The elaborated-dependency audit excludes the existing Euclid infinitude
proof from this route. See [the mathematical proof and precise scope](docs/BASEL.md).

**Exact Cauchy-series equality (2026-09-22).**
`CauchyTaylor.Disk.eq_series` proves `ComplexRaw.Equiv` throughout a certified
rational open disk; the real and imaginary component theorems use
`RealRaw.Equiv`. The series computation is independent of the supplied
function evaluator. Its hypotheses are a quantitative Cauchy representation
and convergent boundary moments. This is not yet Taylor's theorem from an
effective complex derivative: deriving the Cauchy formula, identifying the
moments with derivatives/factorials, and extending to represented inputs
remain open. See [the precise scope](docs/CAUCHY_TAYLOR.md).

This is the contributor and agent entry point. The project formalizes explicit
rational algorithms and the certificates that make them usable as real or
complex quantities. It does not rebuild ordinary analysis by importing a
completed real line.

## Start here

```lean
import ComputableAnalysis
```

For faster iteration, import the narrowest foundation listed in
[GOALS.md](GOALS.md). The supported calculus build target is:

```sh
lake build ComputableAnalysis.CalculusFoundation
```

Foundation modules are import surfaces, not renaming namespaces. Refer to a
declaration by the name in its subject module; do not add an `effective...`
alias merely because a theorem is re-exported by a broader foundation.

## The four layers

1. **Finite evaluator.** At stage `n`, compute a rational interval or complex
   box.
2. **Validity.** Prove ordered boxes, cross-stage nesting, and widths shrinking
   to zero.
3. **Representation edge.** Prove overlap with another implementation at all
   stages.
4. **Abstract object.** Bundle useful implementations and a maintained tree of
   equivalence edges.

Do not put equivalence proofs inside a raw evaluator. When adding an
implementation, connect it to one existing implementation; pairwise edges
against the whole family are unnecessary.

## Real numbers

Use `RealRaw` for one algorithm and `Real` for the abstract represented number.
A valid raw computation proves:

```lean
RealRaw.ValidCompute compute
```

which consists of stage orderedness, cross-stage nesting, and eventual
arbitrary rational precision.

Two valid implementations represent the same number through `RealRaw.Equiv`.
This relation is stagewise overlap. Never compose arbitrary interval overlaps
as though overlap itself were transitive.

### Non-nested candidates

Finite algorithms chosen independently at each precision often shrink without
being nested. Use one of these canonical repairs:

- `RealRaw.prefixStabilize` when the candidate overlaps one valid anchor;
- `RealRaw.overlapChainStabilize` when the available evidence is
  `candidate ↔ bridge ↔ anchor` and the bridge is not itself valid.

The chain construction widens the candidate by the bridge width, which tends
to zero, and then performs prefix stabilization against the valid anchor.

## Functions

Use `FunctionRaw` for one complex-variable computation with its natural
represented domain. Use the abstract function layer to retain alternative
implementations and agreement proofs on intersections of domains.

Do not attempt to classify every acceptable function. Add a special function
when an application needs it, and prove:

1. its domain;
2. validity of its boxes;
3. one useful derivative, integral, ODE, or representation theorem;
4. equivalence to another implementation only when that edge is used.

Routine scalar multiples, sign changes, polynomial combinations, and finite
piecewise definitions should use existing algebra and assembly theorems.

### Applying a continuous computation to a real

For `F : ContinuousFunctionOnInterval`, use:

```lean
F.applyReal x hsource
F.applyReal_equiv hxy hxsource hysource
F.mapImplementation x hsource impl himplSource
```

`applyReal` is the public abstract operation. Underneath it, `applyRealRaw`
searches the stages of the preferred implementation until its interval is
narrow enough, evaluates the rational interval algorithm, and
prefix-stabilizes the image boxes. It does not require an advertised
convergence rate. `applyReal_equiv` is the sole representation-congruence
rule, and `mapImplementation` transports one parent-child edge through the
function. Do not rebuild this argument for named functions or define a public
same-stage composition `evalInterval (x.compute n) ... n`; its validity does
not follow from `x.Valid`.

Inverse branches use the same mechanism through
`InvertibleFunctionOnInterval.forwardRealRaw`; there is no separate
same-stage composition API.

### Inverse branches

Package a regular monotone computation as an
`InvertibleFunctionOnInterval`; do not add a second evaluator merely to change
scale. The canonical arctangent branch is the one-half view of the sector-area
clock in `SectorAreaReparametrization`.

Inverse data should be target-local. For trigonometry, construct the native
scaled-endpoint target with `arctanOnUnitRegularTarget`, prove its geometric
meaning once, and supply a finite search only for those normalized targets.
Do not demand an inverse for every value carrying a nominal endpoint-range
certificate.

Reuse the quantitative rectangle facts in `ArctanGeometry`—in particular
`arctanIntegralRectangleCompute_width_le_sixteenth_input_precision` and
`arctanIntegralRectangleCompute_boxes_strictly_separated`. Do not re-prove
their finite tail estimate in a scaled presentation module.

For a total target-driven search, attach a
`GapAwareTargetWidthCertificate`: it gives a named stage whose target box has
width at most `1 / (16 * (n + 1))`. This cannot be recovered computationally
from `RealRaw.Valid` alone. The canonical quarter-turn target already supplies
`arctanOnUnitRegular_gapAwareTargetWidth`.

Use `InvertibleFunctionOnInterval.source_equiv_of_forward_equiv` for
uniqueness: equivalent forward interval computations imply equivalent source
computations when the separation schedule resolves every positive rational
gap. This is a finite interval theorem, not an appeal to real completeness.
An `InverseBisectionSearch` must provide both its literal finite target
brackets (`value_overlaps`) and the representation edge
`forward_equiv_target`. The former alone can be vacuous when an unscheduled
image box is too wide; the latter certifies the canonical adaptive
application.

When the output precision needed to distinguish two source points depends on
their actual rational gap, use `GapAwareInvertibleFunctionOnInterval` and a
`GapAwareInverseBisectionSearch`. The canonical arctangent branch is exposed
as `arctanOnUnitRegular_gapAwareInvertible`: the denominator of the source
gap selects its separating rectangle stage. Its public result is
`GapAwareInverseBisectionSearch.preimage`, with checked validity,
source-domain containment, and finite forward-image/target overlap. The
corresponding `GapAwareInverseRaw.apply` exposes the same three facts for a
target-local evaluator. This interface intentionally does **not** claim a
`RealRaw.Equiv` edge: add that only after the search has supplied the separate
all-stage argument. The exponential regression searches are examples of this
weaker, already implemented interface.

Do not require a strict left/right comparison at every midpoint. A target box
can genuinely overlap the finite image box of its midpoint. In that case a
total search needs a certified small central source bracket. Its forward-image
overlap is obtained from
`IntervalRegularOn.evalInterval_overlaps_of_point_overlaps`: an interval image
containing the midpoint image still overlaps the target. The separate work is
to prove that the chosen central brackets are nested, shrink, stay in the
source interval, and carry the required forward-equivalence edge.

## Integrating a new function

Choose the first applicable route.

### Monotone rectangles

For a rational interval on which the evaluator is increasing or decreasing,
use endpoint rectangles. Supply interval regularity, monotonicity, and a width
schedule. The Darboux constructors provide a valid integral raw.

### Finitely many turns

Split the interval at certified critical points. Build one monotone integral
per cell and combine them with the finite raw-sum/telescope API. For example,
absolute value is two affine integrals, not a new general integration theory.

### Effective FTC

This is the preferred route when a primitive is known. Construct an
`EffectiveDerivativeBoundFTC` certificate. The main output is:

```lean
h.stabilizedBoundedIntegralRaw endpointValid
```

Use:

```lean
EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw_valid
EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw_equiv_endpointDifference
Integral.effectiveFTCConstructionFor
Integral.effectiveFTCIntegral_equiv_endpointDifference
```

For a public enclosure integral, certify `dF.Valid` and its domain on
\([a,b]\), then use `Integral.enclosureRealizationOfEffectiveFTC`. This retains
the whole-cell ranges and their exact endpoint comparison. The raw stabilizer
remains an internal value computation; `Integral.effectiveFTCConstructionFor`
is the numerical-candidate compatibility adapter.

When an endpoint identity itself must be packaged, use
`Integral.EndpointComparisonFor`; that comparison alone does not define an
integral. Pass a certified endpoint computation to the
direct constructor for the relevant FTC certificate. Endpoint-agreement and
stage-schedule conversion lemmas belong in `FTC`; duplicating one adapter for
every certificate subtype is not part of the public integral API.

These theorems do not assume the native finite sums are already nested. The
older `FTC.effectiveFTCStabilizedRaw_valid` route is compatibility API for
existing `EffectiveFTC` clients and is not the preferred foundation.

For algebra on sampled candidates, reuse
`Integral.SampleConstruction.addOfCommonPlan` and
`Integral.SampleConstruction.scaleRat`; their corresponding `integral_*_equiv`
theorems transport the result. Addition requires a shared finite plan, making
the exact rectangle identity explicit instead of hiding a resampling step.

### Stieltjes/change of variable

When the natural sampling coordinate is not the public variable, represent the
computation as a finite Stieltjes sum. A substitution theorem is then an
equivalence between two explicit sum algorithms, not an appeal to a general
completed-real change-of-variables theorem.

Expose one evaluated theorem for the resulting integral. Keep FTC or chart
arguments as reusable certificate transports; do not publish a second value
theorem whose only distinction is the proof route used to obtain it.

## Effective FTC provider checklist

For primitive `F`, derivative `dF`, and rational interval `[a,b]`, provide:

- `F.Valid` and `dF.Valid` on the required domains;
- finite partitions for every stage;
- a derivative interval on every cell;
- containment of the cell endpoint increment in cell width times that box;
- a global width bound by the stage tolerance;
- validity of the canonical endpoint-difference computation.

Then use `Integral.effectiveFTCConstructionFor`. Do not separately prove
nesting for the bounded-sum candidate.

The representative nonlinear regression is
`sineTaylorPrefixThreeSquareEffectiveFTCConstruction_equiv_value`, which
proves the domain-aware integral of `(x-x^3/6)^2` on `[0,1/2]` is
`6389/161280`.

For a genuinely non-polynomial client, copy the shape of
`arctanEffectiveFTCConstruction` and
`arctanEffectiveFTCIntegral_equiv_arctanGeom_one`: the module supplies the
finite derivative certificate and endpoint interpretation, while the generic
effective FTC supplies stabilization and validity.

## The squared-sine transport

The canonical route is a pairwise chain:

```text
public equal-dyadic square sum
        ↕ finite circle/sample overlap
nested-radical square sum
        ↕ common witness
normalized tangent-square anchor
        ↕ endpoint value
1/4
```

Use `dyadicPublicSquareIntegralRaw_chainStabilized`. Its current open provider
instances are:

- `DyadicSquareCircleOverlapFamily`;
- `DyadicNestedRadicalSquareAnchorCommonWitness` for
  `normalizedTangentSquareEffectiveFTCIntegralRaw`.

The public API deliberately has no three-way shared-witness certificate: such
a certificate asks for stronger same-stage data than the proof needs.
The normalized anchor is already valid, and
`normalizedTangentSquareEffectiveFTCIntegralRaw_equiv_quarter` gives its value
directly from the tangent-square effective FTC.  The chain theorem is not a
completed value theorem until the two finite transport providers are
inhabited.  Derive them from the canonical tangent representation edge rather
than reviving finite candidate searches.

For unsquared sine, use
`DyadicHalfAngleTangentEquivalenceFamily`. The nested-radical evaluator already
stabilizes both its explicit half-angle tangent and sine sample into valid
`realRaw` representatives. A provider supplies only the tangent equivalence
edge to the inverse-arctangent computation; `sine_equiv` transports that edge
through the rational circle chart. The algorithms may use different stage
schedules, so do not replace this edge with same-stage containment or add
rational searches and parallel certificate APIs.

## Series

An infinite series belongs in the foundation only when it has:

1. an executable finite prefix;
2. a rational tail interval;
3. a proof that the tail width shrinks;
4. an equivalence or functional identity used downstream.

Finite sum identities alone should remain dependencies or local lemmas. One
representative tail proof should serve routine coefficient variants.

## Fourier analysis

Finite transforms and orthogonality are algebraic prerequisites, not the goal.
A meaningful Fourier theorem must connect finite coefficients and partial
reconstructions with an explicit tail or approximation schedule. Prefer one
nontrivial function class over many finite transform examples.

## Differential equations

The canonical linear route is:

```text
finite sampled recurrence
→ chronological products and Duhamel sums
→ simplex/Peano–Baker terms
→ explicit factorial tail
→ valid represented trajectory
→ uniqueness by a shrinking zero-initial envelope
```

Finite matrix algebra is reused. New work should target the interval simplex
provider and tail/uniqueness bridges, not additional fixed-size matrix demos.

## Wiedijk's list

Only the analysis-relevant 16-item subset is canonical. The registry is
`ComputableAnalysis.wiedijkAnalysisEntries`. Subject modules own the proofs;
the scoreboard never re-exports them under numbered alias names.

## What not to add

- a theorem already available in Lean's finite algebra or combinatorics;
- a second wrapper whose proof is merely `exact existing_theorem`;
- several degree-specific or fixed-stage examples of one pattern;
- a provider structure presented as though an inhabitant had been built;
- a finite check advertised as an unrestricted infinite theorem;
- measure-theoretic or completed-real machinery hidden in an import.

## Documentation rule

The blueprint states the algorithm, invariant, theorem, and current frontier.
Lean carries proof details. Link directly to the canonical declaration. Do not
link compatibility aliases, repeat historical progress logs, or list every
supporting arithmetic lemma.

## Verification

Before committing:

```sh
lake build ComputableAnalysis.CalculusFoundation ComputableAnalysis
rg -n '\b(sorry|admit)\b' ComputableAnalysis
git diff --check
```

For blueprint changes, run the declaration checker and `leanblueprint web`.
After pushing, confirm Lean CI and the Pages deployment rather than assuming a
successful local render is already live.

## Leibniz benchmark for geometric π

`ComputableAnalysis.pi_eq_leibniz` in `LeibnizPi.lean` retains
`piCircleArea` as the canonical geometric value. `LeibnizPiTaylor` supplies
the separate polynomial-FTC proof. Reuse `Series.AlternatingRaw.interval_remainder`
for an inclusive prefix's first-omitted-term bound, and
`FinitePolynomial.SecantDerivativeBound.exactCellOrder` for exact integral
order from quantitative finite differences on `[0,1]`. The latter closes
the all-degree arctangent polynomial order obligation. Verification and
elaborated dependency separation are recorded by `scripts/check_leibniz.lean`.
No new canonical π, general integration operator, Basel or Fourier result
is introduced by this benchmark.

## Algebraic ODE boundary

`AlgebraicODE.Expr` evaluates residuals on valid `ComplexRaw` inputs and respects
overlap equivalence. A residual alone does not certify a derivative. Use
`Painleve.AlgebraicSolutionOn` to package both finite-difference certificates,
the ODE, and a nonzero algebraic relation for one rational interval evaluator.
`Fuchs.radical_euler` assumes the differentiated curve identity; it does not
construct or differentiate a branch. See [scope and audit](docs/FUCHS_PAINLEVE.md).

### Differential growth from finite steps

Use `LinearGrowth.LinearSolution` (namespace `LinearODE`) for rational matrix
systems whose values are valid component `RealRaw` algorithms. Its local
residual condition has a strictly positive rational step radius on each
closed annulus and a precision stage depending on the step. Keep solution
growth out of that interface: `LinearSolution.moderate_growth` derives it
from a coefficient column bound. `NormBound` uses the nearest-to-zero vector
in each box; do not require every coarse enclosure to fit inside the final
norm bound. `normBound_exact` checks the singleton interpretation, and
`normBound_from_initial_boxes` computes an admissible outer constant.
`LinearSolution.ofExact` and `.constant` construct concrete local solutions.

`Fuchs.Growth` applies this to the real-coordinate scaled jet `(y,z*y')`.
The current theorem is forward growth along rational rays with polynomial
regular coefficients. Do not label it the full Fuchs equivalence or silently
identify the differential-system interface with an arbitrary holomorphic
solution. The proof uses rational subdivisions and polynomial weights;
introducing an ambient completed real line is unnecessary.

### Frobenius and finite polynomial semantics

Reuse `FormalPowerSeriesAlgebra` for finite Cauchy products, shifted Euler
operators, and rational coefficient streams. `Fuchs.Frobenius.Equation.residual`
is defined independently of its coefficient solver; `residual_split` derives
the triangular recurrence. The solver is total as rational code, but its
solution theorem requires every positive-index indicial denominator nonzero.
Use `resonance_compatibility` when this condition fails.

`FormalPowerSeriesPolynomial` connects truncations to the existing Horner
polynomial evaluator and finite-difference calculus. A same-cutoff derivative
requires the explicit first-omitted-coefficient zero hypothesis. The all-degree
Laguerre construction supplies this via termination and proves the unmultiplied
ODE even at zero.

Use `GeometricPowerSeries.geometricRaw` (in namespace `FormalPowerSeries`)
for rational power series satisfying `|cₙ| ≤ M*R^n`. Its validity theorem
requires `M,R ≥ 0` and `R*|x| ≤ 1/2`. Each box contains all later finite
prefixes, and `geometricRaw_precision` supplies a width schedule; width alone
is not a validity proof. `FrobeniusConvergence.coeff_growth` (under
`Fuchs.Frobenius.Equation`) derives the needed coefficient bound when the
indicial root has nonnegative root gap, then `factorRaw_valid` certifies the
factor evaluator. This adds neither analytic derivative certificates nor a
branch of `x^r`. Compare the corresponding Lean 4 statements in Ripple as
recorded in `docs/FUCHS_PAINLEVE.md`; do not import its Mathlib real foundation.

## Finite transmutation

For geometric change-of-area arguments, reuse the finite trapezoid and
rectangle-complement identities in `FiniteTransmutation`. The benchmark
`LeibnizTransmutation` replaces tangent infinitesimals with an exact cubic
cell correction and sums its explicit error. Its geometry bridge is separate
from power quadrature, which reuses polynomial FTC. Run
`lake env lean scripts/check_leibniz_transmutation.lean` to audit that distinction.
See [the historical reconstruction](docs/LEIBNIZ_TRANSMUTATION.md).

## Differentiating rapidly convergent series and local PI charts

Use `GeometricSeriesCalculus.geometricRaw_hasBoxDerivative` (namespace
`FormalPowerSeries`) for coefficient bounds `|cₙ|≤M(1/8)ⁿ` on rational
`|x|≤1`. It certifies all sufficiently refined endpoint and derivative box
samples using the positive step radius `ε/(4(M+1))` and a precision stage
that depends on the nonzero step. Do not replace that dependency by a fixed
precision as the step tends to zero. `coefficientShift_growth` and
`coefficientShift_unit_growth` control derived coefficient streams.

Use `CauchyProductEstimate.cauchy_prefix_error` for a finite product of
prefixes; its triangle-versus-rectangle error is bounded by `M²/2ᴺ` under
rapid coefficient bounds. No infinite-sum rearrangement is assumed.

`Painleve.Laurent` derives its nonlinear recurrence from the independent
residual and checks the resonant index separately. `Painleve.Pole` uses a
conservative rational scale to certify both factor derivatives and the
regularized PI equation on actual box samples. Its reconstructed value has
two-sided double-pole bounds. The original-equation jet identity is algebraic;
a derivative adapter for the reconstructed value is still needed. Do not
promote these local rational charts to a global Painlevé property, a complex
continuation theorem, or an algebraic-solution classification.
## Square-pole normalization and the PNT+ reference

`PDE.CauchyContour` checks literal oriented pole pullbacks, enclosure of all
common-partition tagged sums, valid complex boxes of height at most `16/2^n`,
and `raw_equiv_twoPiI` against the existing geometric π. Translation and
nonzero rational dilation preserve the pole pullback. It imports only
`CauchyPi` and finite rational-complex algebra from `HolomorphicJet`.

See [the PNT+ source map and native obligations](docs/PNT_CAUCHY_ARCTAN.md).
PNT+'s rectangle theorem for finite simple poles is an external Mathlib
reference. Its explicit Cauchy derivative formula uses a separate circle
integral theorem. General native residue transport, regular-part removal
and the Cauchy integral formula are not claimed by this normalization.
The focused audit is `scripts/check_cauchy_arctan.lean`.

The selected contour interface starts with rational rectangles and supplied
piecewise monotonicity certificates for the real and imaginary **side
pullbacks**, using the existing piecewise real integral machinery. Finite
assemblies remain available under addition and subtraction. Integrability
certificates and interior analyticity certificates have separate roles;
the general rectangle adapter and residue transfer are still open.

### Arithmetic generating functions and Apéry

`Apery.Binomial` defines integer binomial sums independently of any ODE and
proves their recurrence by an explicit telescoping certificate. Treat the
finite-support boundary separately before cancelling factors. Integrality
must come from an integer construction or a separate theorem; a rational
recurrence alone does not establish it.

`Apery.DifferentialEquation` defines the Euler operator independently, checks
its ordinary derivative expansion, and uses the existing rapid-series
calculus for three successive actual derivatives. Its residual proof aligns
finite prefixes of different lengths under monomial shifts; every aligned
prefix remains in the same stage box. This gives a uniform residual budget
without invoking completed reals. `Apery.Companion` proves the inhomogeneous
forcing and the discrete Wronskian. Keep identification with `zetaNatRaw 3`,
denominator estimates, and irrationality as distinct obligations; no target
limit is encoded into the companion's definition.

### Real-exponent zeta by finite Dirichlet rectangles

Use `ComputableAnalysis.ZetaReal` for $\zeta(s)$ on represented $s>1$.
`AboveOne` records a finite separating input box. The constructor searches for
that box and selects a chart, then calls `ContinuousFunctionOnInterval.applyReal`.
Do not replace this adapter with same-stage substitution.

The power computation uses binomial coefficients forced by a formal first-order
ODE. `rectangle_dirichlet`, `inversePowerRaw_enclosure`, and
`dirichlet_convergence` are its semantic bridges. `zeta_integer_equiv` supplies
independent compatibility with the earlier integer Dirichlet evaluator.
For changes to schedules preserve the two finite tail inequalities and prove
`RealRaw.Equiv`; chart and implementation independence are already checked.
The algorithm is a reference construction, with coarse bounds near one.
See `docs/ZETA_REAL.md`. Identifying the binomial powers with log–exp powers,
analytic derivatives, and continuation requires additional proofs.

### Mathematical notation in documents

Write all mathematical notation in LaTeX, including inline expressions. Use
`\(...\)` and `\[...\]` in HTML readers with the established MathJax renderer,
and math delimiters supported by Markdown or TeX in source documents. Do not
use Unicode formulas or HTML superscripts/subscripts as substitutes. Literal
Lean declarations and API names remain code. Verify actual typesetting and
mobile layout before publication.
