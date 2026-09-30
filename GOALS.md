# Computable Analysis: Canonical Roadmap

## Analytic-continuation foundation

The main uniqueness target is the identity theorem on the same connected
open domain; simple connectedness is not needed. Monodromy is the separate
path-independence/existence question. The chapter follows local rigidity,
logarithm's apparent counterexample, Taylor propagation, line agreement,
sequence agreement, and \(\sin(1/z)\)'s excluded accumulation point.

Checked: represented germ equivalence, derivative uniqueness, local holomorphic
gluing, finite chart chains with whole-segment coverage, geometric triangle
homotopies, and the local-transport-to-monodromy implication. Affine germs
instantiate the analytic local system with arbitrary represented coefficients.
The full theorem for arbitrary holomorphic germs remains open: general identity,
chain comparison/local stability, continuous-homotopy subdivision, and coherent
chart selection from pathwise continuation still need their bridges.
Global realization from supplied coherent charts and reflection of open
holomorphic charts and overlap evidence are now checked. The reader adds
identity-theorem examples, monodromy comparisons, and a natural boundary;
those general analytic example proofs and the Schwarz seam remain open. See [the exact ledger](docs/ANALYTIC_CONTINUATION.md).

The ODE application audit now checks derivative-germ equality and second-order
residual comparison. A concrete Fuchs client \(y=z^2\) connects a change of
holomorphic chart, the exponent-two Frobenius coefficients, and the existing
rational-ray growth theorem through exact scaled-jet comparisons. General
Frobenius branch construction, uniform ray adapters, sector continuation,
and fundamental-matrix monodromy remain open.

## Continuous quotient derivative foundation (2026-09-30)

Real and complex derivatives now have a common exact specification: a
representation-invariant divided difference, continuous at its center, with
\(f(y)-f(a)\simeq(y-a)Q_a(y)\) and \(Q_a(a)\simeq d\).
Constructed constants, identity, sum/product/chain rules, all represented
polynomials and their iterated derivatives, and real restrictions. Center,
derivative, and evaluator transport are checked. The quotient proves the
existing quantitative remainder law and identifies the derivative in the
Fuchs square client. Open-domain complex uniqueness is a theorem.
Derivative continuity stays separate; supplied extra evidence upgrades the
construction to the existing holomorphic interface.

The general reverse remainder-to-quotient constructor remains open, as do
reciprocal, exponential, sine/cosine, logarithm, and root quotient adapters.
No completed real/complex system or compactness is used. See the
[construction scope](docs/HOLOMORPHIC_FUNCTIONS.md#derivative-as-a-continuous-divided-difference).

## Represented-value continuity (2026-09-30)

`RepresentedContinuity` provides real and complex continuity at a point and
throughout a represented domain, using exact arithmetic and order on values.
Local and whole-domain witnesses convert without uniformizing the radii.
Input-name and equivalent-evaluator transport are proved. Real constants and
identity have constructed witnesses; a derivative at a single complex point
now constructs continuity there directly. Existing interval-stage estimates
remain sufficient proof tools underneath this public law.

## Function-theory audit (2026-09-29)

Completed the missing algebraic calculus: function continuity, sum/product/chain
rules, derivative continuity, correct intersection and inverse-image domains,
and equivalent-evaluator transfer. Arbitrary represented-coefficient
polynomials now have actual derivatives of every order, Horner and coefficient
representation comparisons, and compatibility with the analytic ODE residual.
The focused proof audit rejects new axioms and exercises non-real inputs,
four successive polynomial derivatives, and an affine composition.

This closes the basic calculus and polynomial components, not the entire
function-theory program. Reciprocal and represented complex-series adapters,
Cauchy's formula from holomorphicity, general identity/monodromy, and general
Frobenius/sector applications remain open. The next construction direction is
represented complex series with differentiated-tail and remainder estimates,
starting with exponential and sine. See [the audited boundary](docs/HOLOMORPHIC_FUNCTIONS.md).

## Integral and series skills in the reader

The Skills navigation follows the chapters and contains real integrals,
complex path integrals, series, holomorphic functions, and analytic continuation. Their pages are generated from maintained
`SKILL.md` files, with direct downloads. Rational, trigonometric, power, and
Gaussian/Gamma constructions are supporting examples within the real-integral
guide. The elementary integration baseline remains piecewise-constant data
on piecewise-linear paths. This documentation adds no new Lean theorem.

## Guiding priority: laws about constructed objects

Develop useful laws for supplied, mathematically justified constructions and
instantiate them in concrete examples. Universal existence and weakest-
hypothesis characterizations are separate research goals, not default gates
for every theorem. Track construction, conditional law, and comparison results
separately. A conditional law can be complete while a stronger classical
existence theorem remains open; an uninstantiated record alone proves neither.

Retain the exact scope of established results and the obligations of requested
examples. The older milestone notes below describe their own statements;
they should not be read as a requirement to generalize every constructor.
See [the contract audit](docs/CONSTRUCTION_FIRST_AUDIT.md) and the governing
[project principle](FORMALIZATION_GUIDE.md#construct-the-objects-prove-their-laws).

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

## Aim

Build a usable foundation for calculus and elementary function theory from
explicit rational computations, without importing a completed real-number
or measure-theoretic foundation. Abstract point-set topology is permitted
within the governing import boundary.

A theorem is in scope when its infinite process is represented by finite data
at every stage and the Lean proof supplies the quantitative certificate that
makes those stages coherent. Routine finite algebra and combinatorics should
be reused from Lean rather than duplicated here.

## Canonical objects

- `RealRaw`: one stage-indexed rational-interval computation.
- `Real`: one or more `RealRaw` implementations connected by enough
  equivalence edges to form a maintained spanning tree.
- `FunctionRaw`: one computation on its natural represented domain.
- `ComplexFunction`: equivalent function computations, compared only where
  their domains overlap.

`RealRaw` and `FunctionRaw` do not store equivalence proofs. The abstract
objects do. A new implementation needs one edge to an existing implementation,
not pairwise proofs against every implementation.

## Canonical imports

New clients should import `ComputableAnalysis` or one of these narrower entry
points:

| Area | Module |
| --- | --- |
| raw and abstract represented numbers | `ComputableAnalysis.Basic` |
| rational circle and trigonometry | `ComputableAnalysis.CircleFoundation` |
| finite integrals and endpoint identities | `ComputableAnalysis.IntegralFoundation` |
| effective derivatives, MVT, and FTC | `ComputableAnalysis.EffectiveCalculusFoundation` |
| power series and Fourier certificates | `ComputableAnalysis.SeriesFoundation` |
| exponential and logarithm | `ComputableAnalysis.ExponentialLogarithmFoundation` |
| linear ODEs | `ComputableAnalysis.DifferentialEquationsFoundation` |
| algebraic numbers and finite root certificates | `ComputableAnalysis.AlgebraicFoundation` |
| complete calculus route | `ComputableAnalysis.CalculusFoundation` |

Worked `Finite*Example` modules are regression tests and examples. They are
not re-exported by the canonical root.

## Checked foundation

### Represented numbers

- Rational interval algorithms, nestedness, shrinking widths, arithmetic,
  order, and overlap equivalence are checked.
- Prefix stabilization turns shrinking, non-nested candidate intervals into a
  valid `RealRaw` when they overlap a valid anchor.
- `RealRaw.overlapChainStabilize` composes two overlap edges even when the
  middle candidate is not valid. It widens by the middle width before prefix
  stabilization; it does not falsely treat interval overlap as transitive.
- Rational square roots and the project-native irrationality theorem are
  checked without standard real numbers.

### Circle and trigonometry

- Rational parametrization of the circle, rational area bounds, arctangent
  presentations, nested-radical dyadic sine values, and finite complex
  rotations are executable.
- The oriented dyadic cosine table has one canonical nonnegative-magnitude
  projection. Together with the sine boxes it gives a half-angle tangent
  `RealRaw` whose stabilized form is valid without a completed-real anchor.
- The regular arctangent branch reuses the accelerated sector-area clock by
  one-half scaling; it has interval regularity, monotonicity, and effective
  inverse separation without a second schedule.
- Effective inverse branches have a generic source-uniqueness theorem based
  on equivalent forward interval computations and finite separation.
- Independent pi computations are connected by explicit `RealRaw.Equiv`
  theorems.

### Integration and FTC

- Monotone Darboux rectangles, finitely piecewise monotone assembly, finite
  Stieltjes sums, polynomial examples, and the arctangent example are checked.
- `EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw_valid` is the
  canonical FTC closure. It derives validity from the derivative certificate,
  shrinking finite-sum widths, and a valid endpoint computation. It does not
  assume that the native Riemann candidate was already nested.
- The matching equivalence theorem identifies the stabilized integral with
  the primitive's endpoint difference.
- `FunctionOnInterval.ofRealFunRaw` records a certified raw integrand on its
  rational interval, and `Integral.effectiveFTCConstructionFor` turns the
  stabilized FTC output directly into the domain-aware integral API.
- The arctangent kernel is the canonical non-polynomial client: it supplies
  one `EffectiveDerivativeBoundFTC` certificate and obtains its construction,
  validity, and endpoint identity from the general route without local
  stabilization wrappers.
- The nonlinear regression `(x - x^3/6)^2` on `[0,1/2]` now uses this
  construction route and is identified with `6389/161280`.

### Series, special functions, and ODEs

- Finite power-series algebra, explicit tails, finite Taylor FTC, finite
  Fourier transforms, and representative effective Fourier tails are checked.
- Exponential and logarithm have explicit rational evaluators and substantial
  derivative, inverse, and representation bridges.
- Finite Peano--Baker products, discrete Duhamel sums, and factorial-tail
  estimates provide the linear-ODE core.

## Active frontier

Work in dependency order. Do not add routine examples while an earlier bridge
is open.

1. **Inverse-arctangent source edge / computable IVT frontier.** Construct a finite inverse plan for
   `arctanOnUnitRegular` (its interval regularity, fixed-gap separation, and
   denominator-selected gap-aware separation are checked), and its normalized
   targets have executable (1/(16(n+1))) width schedules.  A sound midpoint
   kernel may retain its parent when its finite target and midpoint boxes
   overlap.  The local third-case fact is checked: non-separation certifies
   that the midpoint forward box overlaps the target box.  A total plan still
   needs a certified small source bracket whose target and forward stages stay
   synchronized across outputs; it must not claim that strict left/right
   comparisons are available at every midpoint.  The conservative kernel now
   has the fixed-stage finite-IVT invariant: every iterate retains its
   oriented endpoint bracket around the target box, including a central
   overlap; each normalized arctangent target supplies the initial full-chart
   bracket.  The explicit arctangent interval-image formula also turns each
   such endpoint bracket into a whole-bracket image enclosure of the target;
   this uses endpoint coherence, not an assumed global image-monotonicity
   axiom, and therefore applies to every fixed finite bisection iterate.
   At each finite depth the checked dichotomy is now explicit:
   either all decisions were strict and the bracket has dyadic width, or a
   rational midpoint forward box overlaps the target.  For each fixed source
   interval, the arctangent rectangle-image boxes now also refine across
   output stages, and a later witnessed image--target overlap transports to
   the earlier enclosing stage on both sides.  The finite theorem now returns
   a dyadically narrow rational source box with an overlapping arctangent
   image at every chosen depth (using the final strict bracket or the central
   rational midpoint).  The literal finite search now keeps those outcomes
   distinct, with a checked invariant: it either retains an endpoint bracket
   or stops at a concrete midpoint-overlap witness; the canonical arctangent
   branch lifts either outcome to a checked forward-image/target overlap.
   The remaining work is
   to synchronize these fixed-stage brackets
   across output stages and prove their source widths shrink.  Then lift rational chart
   addition to bounded `RealRaw` slopes;
   prove that the nested-radical table has normalized angle `k / 2^n`; and use
   constructive inverse uniqueness to inhabit
   `DyadicHalfAngleTangentEquivalenceFamily`.  The remaining stage-box proof
   must supply simultaneous strict rational margins: a circle witness lies
   inside the nested-radical sine box and its half-angle box lies inside the
   inverse box.  Plain `RealRaw.Equiv` alone does not imply this same-stage
   enclosure.  Its `sine_equiv` theorem already transports every equal-dyadic
   sine sample, including zero.  Do not add matching-stage searches,
   certificate families, or parity-specific public wrappers.
2. **Squared sine.** Derive the two square-sum edges from the same tangent
   representation family and the checked tangent-square FTC: public dyadic
   squares to nested radicals, then nested radicals to the normalized
   tangent-square anchor.  The anchor's validity and conditional `1/4` value
   are checked.  These are downstream consequences of item 1, not a second
   finite-search problem.  The canonical chain stabilizer then gives the
   public value.
3. **Fourier series.** Complete effective reconstruction for one genuinely
   infinite, nontrivial class with explicit coefficient and tail schedules.
4. **Linear ODEs.** Lift finite Peano--Baker/Duhamel algebra to interval-valued
   simplex computations with a uniform factorial-tail certificate, then prove
   uniqueness.
5. **Complex special functions.** Treat special functions as complex-variable
   computations from the start, adding one representative per new evaluator
   or analytic estimate.

## Effective FTC contract

For a function computation `F`, derivative computation `dF`, and rational
endpoints \(a \le b\), a provider supplies:

1. domains for `F` and `dF`;
2. finite rational partitions;
3. derivative boxes on each cell;
4. containment of each scaled derivative box around the endpoint increment;
5. a rational width budget tending to zero;
6. a valid endpoint-difference computation.

The library forms finite bounded sums, proves their widths shrink, stabilizes
them against the endpoint computation, and uses
`Integral.enclosureRealizationOfEffectiveFTC` to retain the whole-cell ranges
and the exact comparison with \(F(b)-F(a)\). No
theorem that every continuous function is integrable is needed for this
workflow.

## Wiedijk challenge

The project tracks only the 16 entries from Freek Wiedijk's list whose content
is genuinely relevant to represented numbers, infinite processes, calculus,
or function theory. The machine-readable list is
`ComputableAnalysis.wiedijkAnalysisEntries`; the preface
links each item to its blueprint statement.

Finite arithmetic, counting, elementary coordinate geometry, and similar
items are excluded even when a short Lean proof exists. They can be imported
from Lean when an analytic proof needs them.

## Canonization rule

- One canonical declaration owns each concept.
- Subject modules contain proofs; scoreboard and foundation modules index or
  import them rather than reproving them under new names.
- Keep one representative for a computational pattern. Derive scalar,
  sign, degree, and finite-piece variants by transport.
- Keep a compatibility adapter only while a concrete consumer needs it;
  otherwise remove the closed adapter chain. Do not link adapters from the
  blueprint.
- A provider structure is not counted as a completed theorem until an
  inhabitant and its endpoint/value theorem are checked.
- Do not keep orphan portfolio, checkpoint, or assumption-repackaging modules
  in the source tree.  Git history is the archive for superseded proof routes.
- No `sorry`, `admit`, standard real numbers, measure theory, or hidden
  completeness enters the canonical import chain.

## Release checks

Before publishing:

1. build `ComputableAnalysis.CalculusFoundation`, `ComputableAnalysis`, and
   `ComputableAnalysis.PiProofs` (the canonical arctangent/\(\pi\) bridge);
2. run the blueprint declaration checker;
3. render the blueprint web output;
4. inspect changed files for `sorry`/`admit` and stale legacy links;
5. commit, push to `main`, and confirm both Lean CI and GitHub Pages.

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

## Fuchs–Painlevé algebraic ODE subproject

See [the subproject ledger](docs/FUCHS_PAINLEVE.md). The first milestone checks
Euler–Fuchs polynomial coefficients and PII simple-pole/affine candidates, with
finite-difference certificates for the pole solutions. Next are rational
differential algebra, certified algebraic branches, Fuchs singularity criteria,
and Painlevé classification. General algebraic-solution classification is open.

## Fuchs: formal Frobenius and terminating algebraic solutions

Checked: for `x²y''+xp(x)y'+q(x)y=0` with rational polynomial coefficients,
the indicial obstruction, derived coefficient recurrence, nonresonant formal
existence and uniqueness, resonance compatibility, and finite-prefix residual
vanishing. `Fuchs.Laguerre` constructs every natural-degree terminating solution
of `xy''+(b-x)y'+my=0` for rational `b>0`, with exact degree when `y(0)≠0`,
a pointwise equation and both interval derivative certificates, plus a nonzero
algebraic graph relation. This is local regular-singular theory; Laguerre is
irregular at infinity.

Checked convergence: if the rational indicial root satisfies
`0 ≤ 2*r - 1 + p₀`, `FrobeniusConvergence` derives a geometric coefficient
bound from the recurrence and constructs valid nested rational boxes for
`Σ cₙ*xⁿ` on the explicit disk `R*|x| ≤ 1/2`. The boxes contain every later
finite prefix and have width `4*|c₀|/2^n`, with a computable precision schedule.
The reusable foundation is `GeometricPowerSeries`. Analytic differentiation
of this evaluator, convergence for smaller nonresonant roots, logarithmic
resonant solutions, branches for nonintegral exponents, and global
algebraic-solution classification remain open. The later Painlevé milestone
below adds a reusable series derivative theorem, not yet adapted to this
Frobenius interface.

## Historical geometric Leibniz reconstruction

`LeibnizTransmutation` now supplies `pi_eq_leibniz_transmutation`, using a
new finite geometric bridge and shared polynomial quadrature. The reusable
finite area identities live in `FiniteTransmutation`. See
[the reconstruction and historical scope](docs/LEIBNIZ_TRANSMUTATION.md).
The dedicated dependency audit is `scripts/check_leibniz_transmutation.lean`.

## Fuchs: solution growth without completed reals

Checked: `LinearODE.LinearSolution.moderate_growth` derives an explicit
polynomial bound from a local finite-difference ODE condition and a `1/t`
column bound. The initial constant is computed from the outer endpoint's
stage-zero boxes. `Fuchs.Growth.fuchs_ray_moderate` instantiates this for
second-order Fuchs form with complex rational polynomial coefficients and
a fixed rational complex ray. The proof uses finite rational meshes and
polynomial weights. A reciprocal solution and a non-singleton series-valued
constant exercise the solution interface. No growth bound is assumed as a
solution field; no real-number completion or Mathlib is added.

Open: general holomorphic-solution adapter, sector-uniform bounds, arbitrary
holomorphic regular coefficients, and the converse Fuchs criterion. This
forward growth theorem does not assert a full solution basis or an
algebraic-solution classification. See `docs/FUCHS_PAINLEVE.md` for exact scope.

## Painlevé I: computable local double poles

Checked: an independent Laurent residual forces leading coefficient one and
resonance compatibility. For every rational pole position `p` and free
resonant coefficient `q`, the terminating coefficient algorithm is the unique
formal solution and satisfies an explicit geometric majorant. Scaling by
`ρ=1/(64(1+6|p|+6|q|))` yields valid interval computations for the regular
factor and its first two derivatives on rational `|t|≤1`.

The new `GeometricSeriesCalculus` certifies derivatives by finite differences
on arbitrary box samples. `CauchyProductEstimate` controls finite convolution
errors. Together they prove the regularized nonlinear PI equation with
residual at most `146/2ⁿ`. The reconstructed value has certified double-pole
bounds at every nonzero local coordinate. No completed real type is added.

Open: transporting these derivative certificates to the reconstructed pole
value, complex charts, general computable parameters, continuation from
arbitrary initial data, and exhaustion of movable singularities. The global
Painlevé property and algebraic-solution classifications are not proved.
See `docs/FUCHS_PAINLEVE.md` for theorem names and exact scope.
## PNT+ rectangle residue route

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

## Apéry: differential equation with arithmetic content

Checked: the independent integer binomial sums satisfy Apéry's recurrence by
an explicit finite telescoping certificate. Their generating series solves
`theta^3-t(34theta^3+51theta^2+27theta+5)+t^2(theta+1)^3`.
On the rational chart `t=x/4096`, `|x|<=1`, actual series and first-three-
derivative computations are valid, certify finite differences, and satisfy
the ordinary differential equation with residual at most `24/2^N`.
The companion has forcing `6t`, and its Casoratian proves exact strictly
positive increments of `B_n/A_n`. See `docs/APERY.md`.

Open: identification with the independently computed zeta(3), denominator
control, sharper approximation/growth bounds, and the resulting irrationality
proof. K3 geometry and the period identification are explanatory context,
not formalized results. No algebraicity of the generating function is claimed.

## Zeta: represented real exponents greater than one

Checked: `ZetaReal.zeta` computes a valid represented real for every input with
a finite box strictly above one. Binomial power polynomials, finite Dirichlet
rectangles, uniform coefficient and moment estimates, terminating cutoff
searches, and explicit Lipschitz bounds supply the construction.
`dirichlet_convergence` proves effective convergence of the finite Dirichlet
sums; `zeta_equiv` proves representation independence across selected charts.
`zeta_integer_equiv` recovers every existing integer zeta, including $\zeta(3)$.
See `docs/ZETA_REAL.md` for the formulas and public theorem boundary.

Open: efficient numerical schedules, the binomial-to-log–exp bridge,
parameter derivatives, Euler product, continuation, and the Apéry-to-$\zeta(3)$
identification. The coefficient differential equation is formal; it is not
advertised as an analytic derivative theorem.

## Integral enclosure audit (2026-09-25)

The preferred integral API retains whole-cell range evidence. Legacy valid
number and sampled-sum wrappers are now explicitly candidates. The original
subinterval-copy defect and empty complex first stage are repaired. The
reciprocal on the unit vertical segment now has a direct nested-rectangle
construction with a proved exact coordinate-width rate. See
[the audit and source inventory](docs/INTEGRAL_ENCLOSURES.md).

Remaining bridges: direct contour rectangles to the existing midpoint Cauchy
computation and square-pole computation; the reciprocal vertical segment to
the logarithm evaluator; generic Cauchy-to-Taylor and abelian integration.
These are not supplied by numerical validity, finite endpoint cancellation,
or an uninstantiated representation record.

## Represented holomorphic functions (2026-09-26)

Checked: an open-domain interface with a represented complex derivative,
explicit first-order error radii and derivative-continuity moduli; exact
representation transport; affine and square examples at arbitrary valid
represented inputs. See [scope and remaining adapters](docs/HOLOMORPHIC_FUNCTIONS.md).
The next function-theory bridge is from these local data to the uniform
estimates needed by specific rectangular Cauchy computations. No universal
polygon-integral constructor or weakest-hypothesis theorem is required first.

## Analytic continuation as a function-specific method

Presentation priority: arctangent beyond one Taylor disk; logarithm and its
square-loop period; square root and its branch switch. Retain Bessel's
logarithmic companion as a later ODE application. The
[continuation skill](skills/analytic-continuation/SKILL.md) separates local
holomorphicity, overlap agreement, route coverage, and terminal comparison.
These are proposed continuation showcases; this documentation change adds
no Lean continuation theorem. Existing local estimates and contour periods
are prerequisites, not substitutes for the connecting proofs.


### Monodromy in the differential-equations chapter

Define monodromy on solution germs, its basis-dependent matrix, and the
monodromy group in the reader and chapter manuscript. Use columns of a
fundamental matrix, \(\Phi^\gamma=\Phi M_\gamma\), throughout; the Bessel
illustration now displays the matrix for both loop orientations. These are
mathematical definitions and classical consequences, not new Lean declarations
or completed continuation proofs. Construct local solutions, overlap identities,
route coverage, and the terminal comparison before claiming a specific
monodromy theorem; representation of the fundamental group also requires
homotopy invariance. The continuation skill now records these conventions.


### Guided route from a local logarithm to Fuchs

The reader now follows \(zy''+y'=0\) from a concrete local series through
open-overlap agreement and a square circuit, then explains monodromy,
moderate growth, the scaled state \((y,zy')\), indicial exponents, and
Frobenius series before stating Fuchs's criterion. The side illustration
shows local patches, branch return, and radial growth. This is explanatory
mathematics and a roadmap, not newly checked Lean continuation or Fuchs
proofs; the outstanding represented-input bridges remain explicit.


### Textbook narrative and theorem shortcuts

The continuation-to-Fuchs story is now a section of the main differential-
equations chapter, with its interactive example and chapter navigation.
The former standalone story URL redirects there. Theorem shortcut pages
start with a brief proper setup and the precise statement; extended
motivation belongs in the main textbook. This changes presentation and
navigation only, with no new mathematical or Lean claims.


### Squared trigonometric integrals at arbitrary endpoints

The pinned worked-example package `book/cosine-square` now proves the exact
cosine-square and sine-square definite-integral formulas for every valid
represented real endpoint, with orientation for negative endpoints and
representation invariance. The half-integer values are derived corollaries.
A second local value proof uses a proved imaginary-exponential integration
law and a differential characterization of Euler's circle construction.
The audit checks its independence from the product-rule local value proof.
This is an extension of the documented pinned foundation, not a claim that
these declarations are exports of the current root library; no Taylor-series
exponential bridge is claimed.

## Gaussian convolution and central limit program

The new `FiniteConvolution` module constructs convolution on finite rational
probability kernels. Checked results include preservation of mass, action
commutativity and associativity, addition of means and variances, function
convolution composition, quadratic moment cancellation, and the quantitative
rescaled replacement bound
\(nC|r|^3(\rho_3(K)+\rho_3(L))\). The theorem consumes local cubic
remainder estimates and derives the action comparison by finite telescoping.
It does not assume the resulting comparison in a certificate.

The remaining program is to certify Gaussian compact and exhaustion
semantics, identify its mass with \(\sqrt\pi\), prove affine variants,
moments and Gaussian convolution stability, then transport the finite
replacement estimate to represented integral actions. Smooth-test CLT
convergence and pointwise density convergence are separate targets. See
[the detailed theorem contracts](docs/GAUSSIAN_CONVOLUTION.md).

## Ball formulas, Gamma coefficients, and Gaussian diagonal control

`NBallGaussian` proves validity and representation invariance of the ball-volume
formula on arbitrary valid presentations of nonnegative values, including
irrational radii and early boxes crossing zero; reboxing is internal. It also proves reciprocal half-step coefficient recurrences
and the finite square-to-triangles identity with a diagonal error bound.
The separate reader calculator compares exact rational outputs against 213 Lean
fixtures. Geometric volume, Gaussian normalization, and Gamma improper-integral
bridges remain open. Formula validity inherits the existing native rational
check in the multiplication foundation; see [the precise scope](docs/N_BALL_GAMMA.md).


## Represented-real power integral test

`RealPowerIntegralTest` now gives exact improper power values and convergence
classifications for arbitrary valid represented-real exponents: the zero-end
integral converges exactly for \(p<1\), the infinity-end integral and the series
exactly for \(p>1\). Finite rational endpoint witnesses, reciprocal substitution,
explicit endpoint errors, finite sum–integral comparisons, and representation
invariance are proved in the native foundation. No compactness theorem or
completed zeta series is used. The general series constructor is executable
but deliberately conservative; fast numerical evaluation is not claimed.
See [the exact scope and verification commands](docs/POWER_IMPROPER.md).


## Zeta/Gamma function theory and certified zeros

The primary open-domain derivative contract is now `HolomorphicOn`; algebra,
composition, function continuity, and polynomial witnesses are checked without
requiring derivative continuity. Legacy continuation/ODE clients retain their
stronger interface and explicit extra evidence.

First concrete results: exact integer-zeta bounds, monotonicity and nonvanishing;
Gauss-product Gamma computations at positive integers with proved factorial
limits; exact reflected-root location from genuine uniqueness evidence.
See [the scope audit](docs/FUNCTION_THEORY_ZETA_GAMMA.md).

Next: represented complex series and reciprocal neighborhoods; complex zeta
on its initial half-plane; Gamma on a full parameter domain with justified
improper integral/limit comparisons; continuation and completed-zeta symmetry;
function-specific contour and argument-principle constructions with actual
multiplicity counts, selected by the zero-counting skill; then
certified isolating contours and completeness up to a specified height.
No finite-height critical-line zero theorem is yet claimed.

## Pedagogy of zeta zeros

The reader now follows Euler's product, a paired-series continuation into the
strip, completed-function symmetry, certified contour counting and unique
isolation, and the explicit formula connecting zeros to prime powers. A finite
wave model illustrates frequency and amplitude without claiming a zero
computation or a certified prime-counting remainder. General Cauchy–Goursat is
an optional skill route, not a prerequisite. The classical formulas and
construction recipes remain distinct from checked repository theorems.
