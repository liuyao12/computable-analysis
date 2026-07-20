# Computable Analysis Goalposts

This file is the prose roadmap. Lean files contain definitions, certificates,
and proved bridges; broad mathematical milestones live here with references to
the relevant declarations.

**Current source map.** The checked foundation is
`ComputableAnalysis/Basic.lean`, with calculus in `Calculus.lean`/`FTC.lean`
and the pi comparison layer in `PiProofs.lean`. There is no Mathlib import:
the only non-project import is Lean's rational-number support
`Init.Grind.Ordered.Rat`. Older paragraphs below that name removed files such
as `Base.lean`, `Core.lean`, or `RealEquiv.lean` are historical planning notes,
not a description of the current module graph. The checked blueprint
(`blueprint/lean_decls`) and current Lean declarations take precedence.

## Ground Layer

- Raw reals are interval algorithms `Nat -> QInterval`. `Real` packages a
  preferred valid `RealRaw` and finite, proven-equivalent alternatives. See
  `RealRaw` and `Real` in `ComputableAnalysis/Basic.lean`.
- `RealRaw.ValidCompute` no longer means “width at stage `n` is at most
  `1/n`. It means: every stage is an ordered interval, later stages are
  nested inside earlier stages, and widths shrink to zero.  Any clean bound
  such as `C/n^r` or `C*rho^n` is evidence for this, not the definition.
  `ComplexRaw.ValidCompute` has the same shape for rectangular boxes.
- `RealRaw` has a single optional `rate` metadata field.  The rate is not a
  second kind of real number: it is either unknown, eventually polynomial, or
  eventually geometric.  See `RealRaw.Rate` in
  `ComputableAnalysis/Basic.lean`.
- For concrete algorithms, record public rate information as eventual upper
  bounds, not necessarily exact widths.  For pi, `piLeibnizRate` records width
  `<= 4/n`, while `piMachinRate` records width `<= 20*(1/2)^n`, i.e.
  `20/2^n`.
- Equality of raw representatives is same-stage rational-interval overlap:
  `RealRaw.Equiv x y` means that `x.compute n` and `y.compute n` overlap for
  every `n`. Validity makes this relation transitive. The project-facing
  equality notion is this raw-level relation.
- `RealRaw.anchorRebox` is a finite rational normalization construction: given
  a shrinking, stagewise-overlapping raw algorithm and a valid nested anchor,
  it intersects the prefix of their stagewise hulls.  The result is a valid
  representative equivalent to both inputs, proved by
  `RealRaw.anchorRebox_valid` without any completed-real or completeness
  principle.
- The stronger all-stages notion is now formalized as
  `RealRaw.AllStagesOverlap`: every interval from one algorithm compares as
  `overlap` with every interval from the other. For valid raw algorithms it is
  equivalent to `RealRaw.Equiv`; see `RealRaw.equiv_iff_allStagesOverlap` in
  `ComputableAnalysis/Basic.lean`.
- For computation with a higher-level real number, use `Real`: it keeps a
  preferred certified representative for evaluation plus a list of certified
  equivalent alternatives.  The preferred representative should be the best
  available algorithm/rate. See `Real.compute`, `Real.rate`,
  `Real.representations`, and `Real.withAlternative` in
  `ComputableAnalysis/Basic.lean`.
- Complex numbers mirror the same foundation: `ComplexRaw` has optional
  coordinate-rate metadata, and `Complex` keeps a preferred certified raw
  representative with optional equivalent alternatives. See `ComplexRaw.Rate`,
  `ComplexCert`, and `Complex` in `ComputableAnalysis/Basic.lean`.
- Function layers are representation/domain layers.  Real and complex function
  raws carry a domain and pointwise output-rate metadata; the rate may depend
  on the input and its domain proof.

## Continuity Replacement

- Replace pointwise continuity on an interval by interval regularity:
  every small rational subinterval has a computable narrow output interval
  containing all point-value intervals, with a positive modulus at every
  positive requested precision.  The checked bridge
  `IntervalRegularOn.epsilonDeltaContinuous` derives the literal rational
  epsilon-delta predicate from this enclosure data.
  See `IntervalRegularOn` in `ComputableAnalysis/Calculus.lean`.
- Rational-function denominator apartness is only a sufficient certificate,
  not the general definition.
  See `RatFun.DenominatorApartOnInterval` in
  `ComputableAnalysis/FunctionDomains.lean`.

## Integral

- Public integral target: construct an `Integral.ConstructionFor F` from a
  `ContinuousFunctionOnInterval`.
  See `Integral.ConstructionFor` and `Integral.ExistsConstructionFor` in
  `ComputableAnalysis/Calculus.lean`.
- Proved bridge: once the construction exists, the integral is a computable
  real.
  See `integral_construction_proves_well_defined_for`.
- FTC route for ordinary functions: do not pursue a generic "effective FTC"
  whose hypotheses are derivative bounds and local controls.  The main theorem
  should be the exact convex FTC: exact convexity on `[a,b]` implies the
  one-sided convex derivative is monotone, integrable, and has integral
  `F b - F a`.
- Exact convexity is now stated through `RealRaw.Le` and rational secants.
  See `RealRaw.Le`, `secantRaw`, and `ExactConvexOn`.
- Convex derivative: a construction supplies a valid raw interval algorithm
  for the right or left derivative.  `IsRightDerivative` and
  `IsLeftDerivative` then verify it by the rational-secant lower-bound /
  greatest-lower-bound or upper-bound / least-upper-bound laws.  These are
  certificates for an explicit algorithm, not constructions by infimum or
  supremum.  The full two-sided derivative exists only where the two supplied
  one-sided algorithms agree; corners such as `abs` should not block the
  universal one-sided FTC.
- Convex FTC proof step: for each partition cell `[x_i,x_{i+1}]`, convexity
  gives
  `D_+F(x_i) <= Sec_F(x_i,x_{i+1}) <= D_-F(x_{i+1})`.
  Multiplying by the cell width and summing gives Darboux sums around the
  telescoping endpoint difference `F b - F a`. A finite rational mesh together
  with an explicit modulus must shrink the Darboux gap; no appeal to
  completeness of an ambient real-number type is permitted.
- Piecewise convexity: if a function switches convexity, split the interval at
  rational breakpoints, apply the exact convex FTC on each piece, and combine
  endpoint equalities by raw-real arithmetic and transitivity.  Do not add a
  separate piecewise theorem unless the examples force a reusable abstraction.
- Formula-identification route: to identify a proposed kernel, prove that it
  lies in the same shrinking enclosures as the pointwise derivative produced
  by secants.  For arctangent, this means proving finite sector-area secant
  inequalities and comparing them with `1/(1+x^2)`.
- Projective-line test integral: use the reciprocal quartic
  `∫_(-∞)^∞ dx/(x^4+a*x^2+1)` as a simpler full-line benchmark before the
  Gaussian integral.  The exact rational folding and substitution identities
  for `x ↦ 1/x` and `u=x-1/x` are formalized through
  `IntegralIdentities.reciprocalQuarticUnitFoldDensity_eq_pullback_shiftedCauchy`;
  the clean pi case has its denominator side conditions discharged as
  `IntegralIdentities.reciprocalQuarticUnitFoldDensity_minus_one_eq_pullback_shiftedCauchy`.
  Lean also identifies that shifted Cauchy kernel with the existing arctangent
  kernel through
  `IntegralIdentities.reciprocalQuarticUnitFoldDensity_minus_one_eq_pullback_integralKernel`.
  A second finite bridge now compactifies the line by
  `x ↦ x/(1-x^2)`: the checked theorem
  `reciprocalQuarticSymmetricDensity_minus_one_eq_projectiveCompactPullback`
  identifies its Cauchy pullback with the everywhere-defined density
  `(1+x^2)/(x^4-x^2+1)`, whose two endpoint values are exactly `2`.
  The uniform rational estimate
  `IntegralIdentities.reciprocalQuarticDenominator_minus_one_ge_three_quarters`
  proves `3/4 ≤ x^4-x^2+1` for every rational `x`, and the compact density is
  proved nonnegative.  Its checked finite-difference factorization is
  `IntegralIdentities.reciprocalQuarticSymmetricDensity_minus_one_sub`.
  Lean now proves the resulting `8`-Lipschitz estimate on `[-1,1]` and the
  literal epsilon-delta theorem
  `IntegralIdentities.reciprocalQuarticMinusOneCompact_epsilonDeltaContinuous`,
  using `delta = epsilon/8`.  It now also has a completed
  `IntervalRegularOn` witness,
  `IntegralIdentities.reciprocalQuarticMinusOneCompact_intervalRegular`:
  midpoint evaluation widened by `8 * width(I)` contains every point value,
  and an input width of `1/(16*n)` gives output width at most `1/n`.
  The theorem-facing package
  `reciprocalQuarticMinusOneCompact_continuous` can therefore be consumed by
  the finite-interval calculus and ODE interfaces.  The next analytic
  obligation is now the finite integral and projective substitution
  certificate rather than interval regularity or an unstructured tail limit.
  The expected-value side is packaged as
  `IntegralIdentities.reciprocalQuarticMinusOneExpectedPi`, and Lean proves
  `PiProofs.reciprocalQuarticMinusOneExpectedPi_equiv_piCircleArea`.  The
  remaining work is an improper rational-integral construction that supplies a
  `ReciprocalQuarticMinusOneProjectiveRoute` and turns the `a=-1` case into
  another counted computation of `piCircleArea`.  That route is now typed by
  an `Integral.ConstructionFor` for the concrete compact density on `[-1,1]`;
  its `projectiveIntegral` is definitionally that integral, rather than an
  unconstrained raw real.  The remaining agreement is therefore precisely the
  finite compact-integration and projective-substitution proof.
  The new denominator-cleared endpoint identity
  `projectiveCompactCoordinate_sub_cleared` supplies the finite rational
  displacement calculation for transporting a partition through
  `x / (1 - x^2)`.  The checked positivity lemmas and
  `projectiveCompactCoordinate_strictMono` now prove that this chart preserves
  strict rational order on `(-1,1)`.  `projectiveCompactIntervals_covers`
  lifts that fact to finite rational partitions of every compact source
  subinterval, and `projectiveCompactIntervals_nonnegative` gives the
  nonnegative-branch admissibility needed for the Cauchy quadrature bounds.
  The new pointwise and squared-mesh bounds
  `projectiveCompactCoordinate_sub_le_lipschitz` and
  `projectiveCompactAreaLoop_squareSum_le` quantify the distortion on every
  source branch `[0,s]` with `s < 1`.  The endpoint/refinement schedule is now
  checked too: `projectiveCompactDyadicEndpoint n = 1 - 1/2^n` stays in the
  positive compact chart and has `1 / 2^n <= 1 - s_n^2`;
  `projectiveCompactDyadic_lipschitzFactor_le` bounds the resulting chart
  distortion, and
  `projectiveCompactDyadic_schedule_squareSum_le` proves that `6*n` source
  refinements give transported squared mesh at most `4 / 2^(2*n)`.  The
  quadrature-substitution proof was thereby reduced to a finite cellwise
  comparison and its assembly across the two compact branches.  The cellwise
  comparison is now checked: the exact left and right secant expansions
  'projectiveCompactCoordinate_sub_eq_leftJacobian_add' and
  'projectiveCompactCoordinate_sub_eq_rightJacobian_sub' give the endpoint
  Jacobian bounds on every '0 <= p <= r < 1' source cell.  With the projective
  pullback identity and the compact density's 8-Lipschitz bound, Lean proves
  both cross inequalities between a compact Lipschitz cell and its transported
  Cauchy rectangle.  The finite induction
  'projectiveCompactLipschitzSum_overlaps_integralSum' packages these into
  interval overlap for every positive-branch cover.  The finite global
  ingredients are checked too: the compact density is even, and
  'projectiveCompactSymmetricLipschitzSum_overlaps_integralSum' scales the
  positive branch to a symmetric finite-core overlap.  The endpoint cell is
  bounded by 'projectiveCompactTailUpperCell_le'; at the dyadic endpoint,
  'projectiveCompactDyadicTailUpperCell_le' makes this at most
  '(32 / 3) * 2^(-n)'.  Twice that endpoint budget is now packaged as the
  valid shrinking raw 'projectiveCompactDyadicSymmetricTailError', with the
  stagewise absorption theorem
  'projectiveCompactDyadicSymmetricTailUpper_le'.  What remains is one nested
  raw construction that combines these finite core and tail boxes and agrees
  with the existing compact dyadic integral raw.  That agreement is now tied
  to the actual candidate brackets: the affine map `x = 2*t - 1` carries
  every concrete unit-dyadic lower and upper cell exactly to the compact
  density's 8-Lipschitz cell, and the two sum identities package this for the
  whole stage.  The next finite task is to split these affine dyadic
  partitions into their symmetric positive cores and two endpoint cells.  The
  affine transport is now formally an ordered cover of `[-1, 1]`, so that
  remaining split is a finite partition calculation.
- Hidden singularities such as `1/(x^2 - 2)` are not handled by an FTC theorem.
  They are handled before calculus by denominator-apartness or
  interval-regularity certificates on the rational interval.

## Inverse Functions

- Main calculus route: construct inverses on intervals where the function is
  interval-regular, monotone, and effectively separated.
  See `InvertibleFunctionOnInterval`, `InRangeRaw`, `InverseRaw.apply`, and
  `HasInverse` in `ComputableAnalysis/Calculus.lean`.  `HasInverse I` is now
  explicitly branch-local: its source interval, orientation, and certified
  output range are all fixed by `I`.
- `InRangeRaw` now has computational range content: it carries a validity
  proof for the target raw real and, at every target stage, a named endpoint
  precision whose oriented endpoint boxes enclose the target box.  An
  invertible branch also records that its source endpoints are ordered.  This
  replaces the former unconstrained `in_range : Prop`, which could not guide a
  finite bisection search.
- The separation certificate now chooses exactly one orientation
  (`nondecreasing` or `nonincreasing`), and `InvertibleFunctionOnInterval`
  requires it to match the monotonicity witness.  A certificate must not
  prove both opposing strict endpoint-separation inequalities for the same nonconstant
  function.
- Concrete forward data: `squareOnUnit` on `[0,1]` has exact rational point
  boxes, an interval-regularity modulus (hence an explicit rational
  epsilon--delta certificate), nondecreasing order, and nondecreasing
  effective separation.  `squareOnUnit_epsilonDeltaContinuous` and
  `squareOnUnit_invertible` expose these facts.
  The existing `sqrtRaw` bisection has its algebraic raw-real specification,
  and `sqrtOnUnitBisectionSearch` packages it as an `InverseBisectionSearch`
  for every exact rational target in `[0,1]`, including the explicit
  endpoint-range enclosure for that target.  Extending this to all
  represented unit-range targets remains future work.
- Proved bridge: `HasBisectionSearch I` is computational data assigning a
  certified finite bisection/search to every target in the stated range; it
  gives `HasInverse I` by
  `inverse_function_from_bisection_search`.  Its data-valued formulation
  prevents a hidden choice step when assembling the inverse.
- The sine/cosine route is intentionally next.  The first-octant bridge
  `IntegralIdentities.ArctanInverseBisection` now ties the geometric
  trigonometry chapter to the actual inverse-function interfaces: it requires
  a branch certified equal to `arctanGeomOnUnit`, certified
  `InRangeRaw` quarter-turn targets, and an `InverseBisectionSearch` for each
  target.  It produces `tangentRaw`, a valid partial slope function whose
  outputs stay in `[0,1]` and whose forward evaluator overlaps each target.
  The intended next construction evaluates the rational circle chart
  `((1-u^2)/(1+u^2), 2u/(1+u^2))` at that recovered slope `u`; its coordinate
  projections are the first-octant cosine and sine functions.
  The old `ArctanInverseConstruction` remains only the downstream
  special-value contract.  The next analytic task is to construct the new
  bridge by proving interval regularity, monotonicity, and effective
  separation for `arctanGeomOnUnit`; no inverse law is assumed as a bare
  proposition.
- `asin` is the inverse of sine on a chosen monotone branch, and `log` is the
  inverse of exponential on a chosen monotone branch.
  See `Elementary.ArcsinFromMonotoneSin`, `Elementary.LogFromMonotoneExp`,
  `ArcsinViaInverseFunction`, and `LogViaInverseFunction` in
  `ComputableAnalysis/Elementary.lean`.
- Conditional well-definedness is proved: such branch data produces certified
  computable `asin` and `log` raw functions.
  See `ArcsinFromMonotoneSin.asin_well_defined` and
  `LogFromMonotoneExp.log_well_defined`.

## Elementary Functions

- Positive-base powers now have a constructive interface: a positive raw base
  has a uniform positive rational lower bound; natural powers are repeated
  interval multiplication; and a rational-power extension records valid
  values, the additive law, and certified denominator/root equations. An
  exponential representation also requires `ContinuousInExponent`: the
  explicit rational epsilon-delta predicate
  `EpsilonDeltaContinuousOn` on every rational interval. Its output condition
  is `QInterval.NearAt`, not literal overlap: it bounds the rational
  separation of two evaluation boxes by epsilon while bounding each box's
  width. This certificate is
  the intended gateway for extending continuous functions from rational names
  to computable-real or open complex domains; the extension theorem itself
  remains future work.
  `exp.ExponentialFunction.eAtOne` defines the Euler base as the value at `1`
  of any exponential representation.  See `PositiveRealRaw`,
  `PositiveRealRaw.natPow`, `RationalPowerExtension`, and
  `ExponentialFunction.eAtOne` in
  `ComputableAnalysis/ElementaryFunctions.lean`.
- The two intended characterizations of the Euler base are now explicit
  obligations: the exponential solves `f' = f` on rational intervals, and a
  positive base is Euler exactly when its rational powers have derivative `1`
  at exponent zero.  `RationalPowerExtension.HasDerivativeAt`,
  `RationalPowerExtension.HasUnitDerivativeAtZero`,
  `ExponentialFunction.SolvesSelfDerivativeOn`, and
  `ExponentialFunction.UnitDerivativeCharacterizesE` record the
  rational-interval statements.  Their analytic proof remains to be supplied;
  only the formal coefficient identity is proved so far.
- Exponential has three constructive representations to compare: power series
  `exp.ps`, Euler limit `exp.euler`, and inverse to the logarithmic integral
  `int_1^x dt/t`.  The first two are concrete `FunctionRaw`s now.  The
  inverse-log-integral route is concrete on finite real intervals via
  `exp.LogIntegralInverseBranch` and `exp.fromLogIntegral`; a global real
  branch can be assembled later by effectively choosing a source interval for
  each rational input.
  See `exp.ePowerSeriesRaw`, `exp.eEulerRaw`,
  `exp.eFromLogIntegralBranchRaw`, `exp.representationsAgree`, and
  `exp.powerSeries_equiv_logIntegralInverse_on_interval` in
  `ComputableAnalysis/ElementaryFunctions.lean`.
- Logarithm has two constructive representations to compare: inverse to
  exponential and the integral `∫_1^x dt/t`.
  See `Elementary.LogFromMonotoneExp`, `Elementary.LogFromIntegralInv`, and
  `Elementary.LogIntegralAgreesWithInverseExp` in
  `ComputableAnalysis/Elementary.lean`.
- Power-series representations of `sin` and `cos` are named in
  `ComputableAnalysis/ElementaryFunctions.lean`.
- Hyperbolic sine and cosine have constructive exponential representations
  `(exp z - exp (-z)) / 2` and `(exp z + exp (-z)) / 2`.
  See `sinh.fromExp` and `cosh.fromExp` in
  `ComputableAnalysis/ElementaryFunctions.lean`.
- Power-series machinery and convergence certificate targets live in
  `ComputableAnalysis/PowerSeries.lean`.

## Constructive Differential Calculus

- Derivatives are extracted from shrinking finite-difference intervals on
  rational cells, not assumed as limits in a classical real topology.  See
  `HasDerivativeOnInterval` in `ComputableAnalysis/Differential.lean`.
- Convexity and concavity are helper certificates for producing slope
  enclosures on short intervals.  The rational secant-slope layer is
  `CurvatureOnSubinterval`; the current implementation still has older
  declaration names such as `MonotoneDerivativeBoundMethod` and
  `DerivativeBoundFromCurvature`.
- The first proved power-series brick is formal: the coefficient stream
  `1/n!` is fixed by formal differentiation.  See
  `FormalPowerSeries.expCoeff_derivative` in
  `ComputableAnalysis/PowerSeries.lean`.
- The same formal layer now covers the standard differential identities for
  trig and hyperbolic functions:
  `sin' = cos`, `cos' = -sin`, `sinh' = cosh`, and `cosh' = sinh`.
  See `FormalPowerSeries.sinCoeff_derivative`,
  `FormalPowerSeries.cosCoeff_derivative`,
  `FormalPowerSeries.sinhCoeff_derivative`, and
  `FormalPowerSeries.coshCoeff_derivative`.
- Next theorem for `exp.ps`: turn the formal coefficient identity plus
  rational tail bounds into an effective derivative certificate for the boxed
  algorithm, hence a witness for
  `exp.ExponentialFunction.SolvesSelfDerivativeOn`.  This can be specialized
  to exponential first; a general term-by-term differentiation theorem can
  come later.
- To prove equality of the three exponential representations by calculus
  rather than by ad hoc estimates, prove a constructive uniqueness principle
  for `f' = f` with `f(0) = 1`, then prove the equivalent unit-slope
  characterization of the base at zero.  See
  `SolvesSelfDerivativeOnInterval` and `SelfDerivativeInitialValueUnique` in
  `ComputableAnalysis/Differential.lean`.

## Linear Differential Equations

- The finite noncommutative core for Peano--Baker is now checked in
  `ComputableAnalysis/PeanoBaker.lean`, without Mathlib. It defines local
  rational vectors/matrices, explicit finite matrix sums/products, sampled
  linear recurrences, and the ordered-word enumerator
  `LinearODE.peanoBakerDiscreteSum`. The enumerator has exactly `2^N` terms
  after `N` samples (`LinearODE.orderedIndexWords_length`); its two-step
  expansion contains `B_1 * B_0`, preserving chronology.
- `LinearODE.discretePeanoBakerExpansion` now proves the purely rational
  algebra theorem equating that word sum with
  `(I + B_(N-1)) * ... * (I + B_0)`. Its proof establishes the local matrix
  identity, distributivity, and finite induction before touching convergence.
- The same finite layer now proves a sampled variation-of-constants formula:
  `DiscreteLinearSystem.trajectory_eq_homogeneous_add_zeroInitial` splits any
  inhomogeneous trajectory into its time-ordered homogeneous action and the
  zero-initial forcing response. `ForcingZero` makes that response vanish.
  Constant increments are checked exactly by
  `chronologicalProduct_constant` and `peanoBakerDiscreteSum_constant`, giving
  `(I + B)^N`; `peanoBakerDiscreteSum_zeroCoefficient` supplies the zero
  coefficient identity case. The new `PairwiseProductZero` specialization is
  a proved finite nilpotent case: when every `B_i * B_j` is zero,
  `chronologicalProduct_pairwiseProductZero` and
  `peanoBakerDiscreteSum_pairwiseProductZero` collapse the exact transition
  to `I + matrixSequenceSum B N`.
- The local matrix product is now proved associative by a finite double-sum
  interchange (`matrixMul_assoc`). Consequently
  `chronologicalProduct_split` proves the exact chronological composition law
  across adjacent sampled intervals. `PairwiseCommuting` and
  `matrixMul_commutes_chronologicalProduct` supply the finite reordering
  lemma for commuting samples. This is the algebraic prerequisite for the
  later commuting-exponential formula, not a claim that the continuous
  formula has already been constructed.
- The continuous input is `LinearODE.IntervalLinearSystem`, whose scalar
  entries are existing `FunctionOnInterval`s on a common rational time
  interval. `CoefficientsRegular` asks for supplied componentwise
  `IntervalRegularOn` witnesses; it does not assume a completed-real
  function space.
- Next analytic target: build interval matrices for ordered-simplex
  Peano--Baker terms, prove a factorial tail enclosure from a rational
  coefficient bound, and obtain state-transition and variation-of-constants
  formulas for `x' = A(t)x + b(t)`. The next specializations are the analytic
  commuting-exponential identification, scalar and piecewise-constant
  systems, and higher-order nilpotent/triangular systems. Chapter `Linear
  Differential Equations` gives the certificate plan.

## Elementary Function Coverage

The library should use familiar functions as examples and regression tests for
the formulation.  Each entry should eventually have a raw algorithm, a domain
certificate when partial, and enough calculus facts to participate in FTC/FTA
arguments.

- Algebraic: polynomials, rational functions with domain certificates, square
  roots, and algebraic functions.
- Power-series families: exponential, sine, cosine, hyperbolic sine/cosine,
  and later functions obtained from these by algebraic operations and
  composition.
- Inverse/integral families: logarithm, arctangent, arcsine, and branch-based
  inverse trig/hyperbolic functions.
- Standard calculus/science examples: tangent/secant on certified domains,
  polar and complex exponential identities, and special functions that are
  naturally defined by effective power series or effective integrals.
- Complex path integrals now have a first polygonal finite-sum layer:
  `ComplexPathIntegral.segmentLeftSum` integrates a complex `FunctionRaw` along
  one rational segment, and `ComplexPathIntegral.polygonalLeftSumEntire`
  sums over consecutive vertices of a polygonal path.  The wrapper
  `ComplexPathIntegral.polygonalIntegralRawEntire` packages these finite sums
  as a `ComplexRaw` algorithm.  The current Cauchy sanity checks integrate
  `z^2` and `z^3 + 2z` around the unit square and check overlap with zero at
  stages `10`, `100`, and `1000`.

## Algebraic Numbers and FTA

- The algebraic-number layer is now proof-honest: exact rational-complex
  algebraic numbers and exact roots of unity are formalized, while arithmetic
  closure and algebraic closure are explicit targets rather than theorem
  placeholders.  See `AlgebraicComplex.MulRawValid`,
  `AlgebraicComplex.add_annihilator_exists`,
  `AlgebraicComplex.neg_annihilator_exists`,
  `AlgebraicComplex.mul_annihilator_exists`,
  `AlgebraicComplex.inv_exists`, and `AlgPoly.exists_root`.
- Next finite algebra target: prove `ComplexRaw.mul` preserves validity, then
  use resultant-style rational polynomial transformations to supply the
  addition, negation, and multiplication annihilator witnesses.

## First-Year Calculus Course

The course layer should avoid broad classical theorem dependencies such as IVT
and MVT.  Instead, it should grow a concrete table of functions, domains,
derivatives, and definite integration algorithms that covers the examples
students actually compute.

- New course module: `ComputableAnalysis/FirstYearCalculus.lean`.
- Checked formal derivative table:
  monomials `x^(n+1)/(n+1)`, `exp`, `sin`, `-cos`, `sinh`, and `cosh`.
  See `FirstYearCalculus.PowerSeriesDerivativeEntry` and
  `FirstYearCalculus.checked_power_series_table`.
- Linear closure for the table is now available at the formal coefficient
  level.  See `FormalPowerSeries.derivative_add`,
  `FormalPowerSeries.derivative_scaleRat`,
  `FormalPowerSeries.HasFormalDerivative.add`, and
  `FormalPowerSeries.HasFormalDerivative.scaleRat`.
- Real-axis wrappers for concrete functions are named:
  `FirstYearCalculus.RealElementary.expPS`, `sinPS`, `cosPS`,
  `sinhFromExp`, `coshFromExp`, `sqrtRat`, `invX`, and
  `invOnePlusSquare`.
- Rational-function kernels ready for calculus:
  `RatFun.oneOverOnePlusSquare_denominator_apart_on_interval` proves that
  `1/(1+x^2)` has denominator-apartness bound `1` on every rational interval,
  and `RatFun.oneOverX_denominator_apart_on_pos_interval` proves that `1/x`
  is denominator-apart on every interval `[a,b]` with `0 < a`.  These expose
  `1/(1+x^2)` and `1/x` as certified interval functions.
- Next concrete integral targets, without a general integrability theorem:
  `integral 1/x = log x` on positive intervals,
  `integral 1/(1+x^2) = arctan x`,
  `integral 1/sqrt(1-x^2) = asin x` on certified subintervals of `[-1,1]`,
  tangent/secant formulas on intervals whose cosine denominator is apart from
  zero, and polynomial/rational examples via domain-specific interval
  certificates.
- For each target, the desired endpoint is a named raw algorithm with an
  optional `RealRaw.Rate`, plus a checked definite-integral formula on its
  natural certified domain.

## Taylor Expansions

- Taylor's formula should be generated by iterated definite-integral FTC:
  first prove `F(x) = F(a) + integral_a^x F'(t) dt`, then apply the same
  statement to `F'`, then to `F''`, and so on.  The shape is recorded by
  `Taylor.FTCStepAt` and `Taylor.IteratedFTCChain` in
  `ComputableAnalysis/Taylor.lean`.
- The coefficient-level operation for one step from `0` is
  `FormalPowerSeries.coeffsFromDerivativeAtZero`; the theorem
  `FormalPowerSeries.coeffsFromDerivativeAtZero_hasFormalDerivative` proves
  that differentiating the constructed coefficient stream gives the supplied
  derivative stream.
- First checked Taylor coefficient route for arctangent:
  `FormalPowerSeries.atanTaylorCoeff_hasFormalDerivative` proves that the
  arctangent coefficient stream differentiates to the coefficient stream for
  `1/(1+x^2)`, and `Taylor.arctanTaylorCoefficientRoute` records the odd
  coefficients `(-1)^k/(2k+1)`.
- The analytic input for that route is now a certified rational function:
  `Taylor.arctanKernelOnInterval` is `1/(1+x^2)` as a function on any rational
  interval, backed by `Taylor.arctanKernel_regular_on_every_interval`.
- The higher-derivative problem for arctangent is avoided by a finite rational
  division theorem: `Taylor.ArctanKernel.finiteRemainderRoute` proves
  `1/(1+x^2) = kernelPartial x n + kernelRemainder x n`, with
  `|kernelRemainder x n| <= (x*x)^(n+1)`.  This is the exact theorem that
  should feed the later definite-integral remainder estimate.
- The finite Riemann-error core is now formalized without a completeness
  principle.  `powDifferenceFactor` factors `r^n-p^n` by `r-p`,
  its endpoint-average bounds bracket each monomial primitive, and
  `monomialIntegralBetween_endpoint_error_le` gives each left/right
  rectangle an explicit `k * (r-p)^2` error on the unit interval.  The
  remaining series bridge work is to sum these finite polynomial bounds over
  the dyadic area mesh and combine that schedule with the Taylor remainder.

## Iteration-Based Construction Layers

- Alternating series now have a first iteration-style raw layer.  See
  `Series.AlternatingRaw` in `ComputableAnalysis/Series.lean`.
- Proved: if the magnitudes of an alternating series shrink to zero, then the
  intervals between consecutive partial sums shrink to zero.  See
  `Series.AlternatingRaw.intervals_shrink`.
- Next step for alternating series: prove nestedness/enclosure from
  nonnegative decreasing terms, then instantiate Leibniz/arctangent series.

## Pi Representations

- The canonical progress measure is the checked table in
  `blueprint/src/pi-scoreboard-table.tex`: currently eleven of nineteen named
  computations are valid raw reals, and eight of eighteen applicable rows
  have a formal equivalence chain to `piCircleArea`.  The completed canonical
  rows are the direct area-loop computation, its independently evaluated
  rational polygon-fan form `piCircleAreaPolygon`, the geometric quarter-turn
  computation `4 * arctanGeom(1)` and its single rectangle-integral
  formulation `4 * arctanIntegralRectangleForAtOne`, the series computation
  `4 * arctanSeries(1)`, the single classical power-series formula `piMachin`,
  the reciprocal-tail full-line Cauchy integral, Nilakantha's accelerated
  rational series, and the direct cross-fan circumference computation
  `piCircumferenceFan`.  The valid-but-not-yet-equivalent Basel row and the
  concrete compact reciprocal-quartic candidate
  `PiProofs.piReciprocalQuarticCompact` account for the two definition-only
  completions.  The latter is the verified dyadic integral of
  `(1+x^2)/(x^4-x^2+1)` on `[-1,1]`; its projective-substitution equivalence
  to `piCircleArea` remains the next analytic obligation.
- The canonical Leibniz series equivalence is proved by the finite Riemann
  bridge `leibnizEqualsRectangleRawAtOne_finiteRiemannBridge`, which schedules
  a finer dyadic rectangle mesh, absorbs its finite polynomial error in a
  shrinking dyadic-zero interval, and cancels the padding in raw-real
  arithmetic.  Its public consequence is
  `four_arctanSeries_one_equiv_piCircleArea`.  The exact-order route remains
  an independent stronger quadrature API and needs the uniform all-partials bridge
  `PiProofs.LeibnizRectangleBridge.KernelPartialExactCellOrderPreservationOnUnit`.
  Pointwise kernel bounds and finite certificates through the indicated
  prefixes are checked. Exact cell-order preservation is now proved for the
  constant partial, `1 - x^2`, `1 - x^2 + x^4`,
  `1 - x^2 + x^4 - x^6`, and `1 - x^2 + x^4 - x^6 + x^8`. The first
  nonconstant case uses explicit nonnegative rational endpoint-gap factors;
  the degree-four case uses Boole quadrature and the degree-six and
  degree-eight cases use positive seven-point and eleven-point rational
  Newton--Cotes identities.  Neither route uses completeness.
- `piMachin` previously needed a principal-branch addition certificate.  The
  required three bounded rational additions are now proved:
  `2*atanGeom(1/5) = atanGeom(5/12)`,
  `atanGeom(7/17) + atanGeom(1/239) = atanGeom(5/12)`, and
  `atanGeom(5/12) + atanGeom(7/17) = atanGeom(1)`.
  `geometricMachinUnitAdditions_of_chartTransport` obtains this certificate
  from finite rational rectangle transport, and
  `geometricBranchIdentity_of_chartTransport` formally assembles it into
  The universal `GeometricUnitAdditionLaw` remains a useful stronger API, but
  is no longer a prerequisite for the concrete Machin branch.
  The finite Gaussian/rational calculation is complete.  The rational
  kernel-Jacobian identity
  `RationalCircle.Trigonometry.arctanKernel_chartAdd_jacobian`, its exact
  endpoint displacement law
  `RationalCircle.Trigonometry.chartAddParameter_sub`, and its
  chart-admissible order-preservation law
  `RationalCircle.Trigonometry.chartAddParameter_mono` are also proved;
  `ArctanGeometry` now lifts this algebra to every finite rectangle partition:
  the chart-transformed target bracket contains the source bracket and maps
  each area-loop stage to a verified finite target cover.  On the
  Machin-relevant half-unit chart, transformed endpoint widths are bounded by
  eight times their source widths and squared meshes by a factor of \(64\);
  this gives a \(128 x^2/2^n\) transported rectangle-width bound whenever the
  image endpoint stays in the unit interval.  The transformed brackets are now
  a valid nested shrinking raw construction with width at most \(256/(n+1)\),
  and `arctanIntegralRectangleRaw_equiv_chartAddAreaLoopRaw` proves its
  construction-level equivalence to the source rectangle raw.  Appending the
  source prefix partition to the transported interval partition proves the
  canonical endpoint-difference comparison, and
  `arctanGeom_chartAdd_add_of_half` now proves the bounded geometric addition
  law needed at all three Machin instances.  Consequently
  `MachinIdentity.geometricMachinUnitAdditions_of_chartTransport` and the
  resulting geometric Machin branch identity are proved.  The finite Riemann
  bridge now proves the needed power-series/kernel comparisons at `1/5` and
  `1/239`, so `piMachin_equiv_piCircleArea_finiteRiemannBridge` is a completed
  canonical scorecard row.  The endpoint comparison at `1` belongs to the
  independent Leibniz route.  Machin remains solely a power-series
  computation, not a second integral-based pi representation.
- The generic finite-Riemann theorem
  `arctanEqualsGeom_finiteRiemannBridge` remains reusable series-to-geometry
  infrastructure on nonnegative rational inputs in `[0,1]`.  The canonical
  scoreboard deliberately uses it only for the Leibniz endpoint and the two
  power-series inputs in the single Machin formula; auxiliary arctangent
  addition identities are not separate pi computations.
- The exact stage bridge
  `ArctanGeometry.piCircleArea_compute_eq_piCircleAreaPolygon_compute` now
  proves `PiProofs.PiCircleAreaPolygonAgreement`; with finite Archimedes this
  gives the raw equivalence
  `PiProofs.piCircumference_equiv_piCircleArea_of_verified_area_polygon` and
  promotes the polygon scaffolding computation to a valid raw real through
  `PiProofs.areaPolygonValid`.  `PiProofs.piCircumferenceReboxed` is now a
  valid finite-prefix reboxing of the direct perimeter intervals against the
  verified area intervals, and is formally equivalent to `piCircleArea`.
  `PiProofs.piCertified : Real` uses the area loop as its preferred evaluator
  and retains this reboxed perimeter route as a checked alternative.
  It is a usable alternate representative, not a substitute for the direct
  `piCircumference` validity proof; the direct algorithm still lacks the
  one-step refinement certificate, so the canonical row remains uncounted.
  The direct rational endpoint condition has an executable regression proof
  through the first twelve dyadic transitions in
  `PiProofs.circumferenceQuarterLengthStepRefinesUpToTwelve`; the required
  all-stage theorem remains open.  The exact tangent-geometry half is now
  symbolic rather than experimental: `adjacentTangentCrossClosedForm` gives
  each outer tangent cell a denominator-cleared rational length, and
  `outerFanPerimeter_refinesByDoubling_withZeroGap` proves that the exact
  outer tangent fan decreases by an explicit positive first-cell gap under
  every dyadic subdivision.  The certified bisection-width schedule is below
  that gap, so `outerQuarterLength_hi_refinesByDyadicStage` proves the outer
  (circumscribed) endpoint at every public stage.  The complementary exact
  inner geometry is now also symbolic:
  `innerFanPerimeter_refinesByDoubling` proves that the rational inscribed
  chord cross-product fan increases under every dyadic subdivision.  This is
  an exact sector-area fan, not the chord-path length: it improves the
  Archimedes geometry but cannot on its own transport the direct lower
  endpoint of the original `piCircumference` evaluator.  It does, however,
  give a separate direct raw computation: `piCircumferenceFan` uses this
  exact rational cross-fan as its lower endpoint and the original
  circumscribed path-length upper endpoint.  Lean proves its ordered nested
  brackets and explicit `10/(n+1)` width modulus in
  `piCircumferenceFan_valid`, then proves
  `piCircumferenceFan_equiv_piCircleArea` from the common inscribed-polygon
  lower endpoint.  The original chord-length lower path remains isolated as
  `AdjacentChordLowerRefinesByDoubling`: a local comparison between the
  bisection lower enclosure of each coarse chord and the two lower enclosures
  of its refined chords.  Lean proves that this finite local condition lifts
  to the entire quarter path through
  `innerQuarterLength_lo_refinesByDoubling_of_adjacentChordLowerRefines`, and
  `circumferenceQuarterLengthStepRefines_of_adjacentChordLowerRefinement`
  combines its all-stage form with the proved outer endpoint.  The original
  direct circumference row remains uncounted until that local bisection
  comparison is proved.  A curvature-corrected refinement and its squared
  margin reduction remain design notes until their dependency order is
  reconstructed as a portable Lean proof; they are not scorecard rows.

### Archived pre-refactor notes (not current source)

The following notes, through the next top-level heading, describe modules and
names from an earlier architecture (`CirclePi.lean`, `CircleArea.lean`, and
related polygon files) that are no longer in this repository.  They are kept
only as historical design context.  They are not a roadmap, should not be used
to measure progress, and must not override the checked source map or the pi
scoreboard above.

- Pi should be represented by several independent computable algorithms:
  Leibniz series, Machin/arctangent formulas, geometric constructions,
  integrals such as `4 * ∫_0^1 1/(1+x^2) dx`, and continued fractions.
  See `Pi.Representation`, `Pi.Integral`, `Pi.Geometric`,
  `Pi.ContinuedFraction`, and `Pi.RepresentationsAgree` in
  `ComputableAnalysis/Pi.lean`.
- These equivalence proofs should be consequences of the constructive calculus
  layer: arctangent as inverse/integral, trig branch identities, integral
  substitution/additivity, and direct finite interval estimates where needed.
  They should not invoke classical real completeness or mathlib analysis.
- Proved algebraic core for Leibniz/Machin: the rational tangent formulas give
  `tan (4 atan(1/5) - atan(1/239)) = 1`.  See
  `Machin.quarter_tangent_identity` in `ComputableAnalysis/Pi.lean`.
- The same algebraic fact is also recorded as the Gaussian-rational identity
  `(5 + i)^4 = (2 + 2i) * (239 + i)`.  See `Machin.gaussian_identity`.
- Arctangent now has a formal rational branch layer for expressions generated
  by `atan x`, addition, and subtraction.  This proves, without real numbers,
  that the selected-branch expression `4 * atan(1/5) - atan(1/239)` has tangent
  slope `1`, i.e. the same formal branch value as `atan(1)`.  See
  `Arctan.evalBranch_add_of_pos`, `Arctan.evalBranch_sub_of_pos`, and
  `Arctan.machinQuarter_eq_atan_one` in `ComputableAnalysis/Pi.lean`.
- The arctangent power series is now connected to the shared formal
  power-series coefficient layer.  See
  `FormalPowerSeries.atanOddCoeff_derivative_term` in
  `ComputableAnalysis/PowerSeries.lean`, and
  `Arctan.psTerm` and `Arctan.psIterate_eq_arctanInterval` in
  `ComputableAnalysis/Pi.lean`.
- The named arctangent power-series function is now complex-first:
  `ComputableAnalysis.Arctan.powerSeriesFunctionRaw` is a complex
  `FunctionRaw` for `z - z^3/3 + z^5/5 - ...`, and
  `Elementary.Arctan.powerSeriesFunctionRaw` is its real-axis projection via
  `FunctionRaw.realPartOnRealAxis`.  The older real alternating enclosure
  `Arctan.psIterate` remains available for the Leibniz pi series, where the
  even/odd real alternating bounds are convenient.
- The arctangent branch layer is now tied to rational complex-plane geometry:
  `Arctan.HasSlope` says a rational complex vector represents the branch value
  `atan x`, and multiplication/conjugation prove the geometric
  addition/subtraction laws.  See `Arctan.mul_slope_add`,
  `Arctan.mul_slope_sub`, `Arctan.evalBranch_hasSlope`, and
  `Machin.gaussian_identity_subtract_slope`.
- Exact series bookkeeping: the Leibniz finite sums are precisely
  `4 * arctanOfOne n`.  This is mainly definitional cleanup, not the
  Leibniz/Machin equivalence proof.  See
  `leibnizPartial_eq_four_arctan_of_one` in
  `ComputableAnalysis/Pi.lean`.
- Leibniz's finite intervals are now identified only with the power-series
  representative `4 * atan_series(1)`, not with geometric pi.  See
  `Pi.arctanSeriesPi`, `Pi.leibnizSeries_is_arctanSeriesPi`, and
  `Pi.leibniz_agrees_with_arctanSeriesPi`.
- Polygon definitions are geometric support layers, not prerequisites for the
  primary quarter-disk pi route.  `ComputableAnalysis/Archimedes.lean` records
  the theorem skeleton relating polygon-area pi and half-circumference pi,
  while `ComputableAnalysis/RationalPolygon.lean` and
  `ComputableAnalysis/ComputablePolygon.lean` record finite shoelace geometry.
- Rational-coordinate polygons are now finite objects with shoelace area.
  See `RationalPolygon.QPolygon` in
  `ComputableAnalysis/RationalPolygon.lean`.  The proved theorem
  `RationalPolygon.QPolygon.area_mapMul` says that multiplying every vertex
  by a rational complex number rotates/stretches the polygon and scales its
  area by the squared norm of that complex number.  This is the elementary
  geometry layer behind rational polygon triangulations and regular polygon
  area computations.
- The finite Archimedes rearrangement step is proved sorry-free in
  `ComputableAnalysis/Archimedes.lean`.  `Archimedes.Slices.horizontalSlice_area`
  proves that a triangle slice at height `h` with base width `w` has area
  `h*w/2`, `Archimedes.Slices.horizontalSlice_area_mapMul` records the
  rotation/stretch compatibility via complex multiplication, and
  `Archimedes.Slices.sliceAreaSum_eq_half_perimeter_mul_height` proves that
  finitely many same-height slices have total area `height * totalBase / 2`,
  i.e. the rectangle-rearrangement algebra in Archimedes' proof.
- Regular polygons on the unit circle are generally not rational-coordinate
  polygons after repeated bisection.  The non-rational layer is
  `Polygon.CPolygon` in `ComputableAnalysis/ComputablePolygon.lean`: vertices
  are `ComplexRaw`s, and `CPolygon.areaCompute` is the interval shoelace
  algorithm on their rational boxes.  Rational polygons embed by
  `Polygon.fromRational`, with exact area represented by
  `Polygon.rationalAreaRaw`.
- First-quadrant box exhaustion is the primary circle-area route.  It uses
  only the two corners of each rational grid box, avoiding any need to define
  polygon area or circumference for pi.  See
  `ComputableAnalysis/QuarterCircle.lean`: `QuarterCircle.gridCell_inner_sound`
  proves that a box whose upper-right corner satisfies `x^2+y^2 <= 1` lies
  inside the quarter disk, and `QuarterCircle.gridCell_outer_false_sound`
  proves that a box whose lower-left corner is outside is entirely outside.
  `QuarterCircle.piAreaInterval` is the resulting finite rational interval
  algorithm for pi from four times the quarter-disk area.
- The first quantitative exhaustion step for the quarter-disk route is now
  proved sorry-free.  `QuarterCircle.OuterColumnHeight` records the exact
  height of an outer grid column; `outerColumnHeight_left_edge`,
  `outerColumnHeight_right_edge`, and their uniqueness lemmas prove that the
  actual circle grid has endpoint heights `n` and `1`.  In
  `QuarterCircle.Staircase`, `boundaryCells_eq_two_mul_sub_one` proves the
  telescoping `2n-1` boundary-cell count, and
  `fullDiskBoundaryGap_at_exhaustionFuel_le_one_div` proves that using
  `8n` subdivisions makes this full-disk boundary gap at most `1/n`.  The
  remaining certificate for `QuarterCircle.PiAreaBoxCertified` is to connect
  these column-height facts to the concrete `List` sum in
  `QuarterCircle.piAreaInterval` and prove nestedness across refinements.
- The standalone Archimedes area theorem now has its own package in
  `ComputableAnalysis/CircleArea.lean`.  `CircleArea.unitDiskAreaCompute` is
  the unit-disk area algorithm, `CircleArea.ArchimedesAreaOfUnitCircle` is the
  theorem statement saying this area real equals a chosen pi representative,
  and `CircleArea.piByUnitDiskArea_equiv_of_archimedes` is the proved
  corollary that this standalone theorem implies equivalence between the
  area definition of pi and that chosen pi definition.
- The circumference exhaustion layer is now explicit and sorry-free in
  `ComputableAnalysis/Circumference.lean`.  `Circumference.Bounds` packages
  inscribed/circumscribed perimeter interval algorithms,
  `Bounds.halfPiValid_of_circumferenceValid` proves that a certified
  circumference exhaustion gives a certified half-circumference pi
  representative, and
  `Circumference.unitDiskArea_equiv_halfCircumference` is the direct theorem
  saying the unit-disk area pi equals the half-circumference pi once their
  interval algorithms are coupled at every precision.  The finite sector
  lemmas `FiniteSectors.circumscribed_area_eq_half_perimeter` and
  `FiniteSectors.inscribed_area_le_half_perimeter` prove the algebraic
  Archimedes relation between tangent/inscribed sector fans and perimeter.
  `Circumference.SectorBounds.Stage` now packages the exact finite sector data
  and automatically derives the area/perimeter comparison.  The theorem
  `Circumference.SectorBounds.Exhaustion.archimedes_of_conditions` is the
  current sharp Archimedes endpoint: for any concrete sector exhaustion whose
  area and perimeter intervals are nested and shrink to zero, the area
  definition of pi is equivalent to the half-circumference definition.
  `Circumference.polygon_area_equiv_half_circumference` restates the existing
  certified polygon theorem in this area/circumference language.
- The unit-sector theorem is now stated directly in
  `ComputableAnalysis/CircularSector.lean`.
  `CircularSector.area_eq_halfArcLength` proves that any certified
  unit-sector exhaustion has sector area equal to half its boundary arc length
  as computable reals.  The angle-parametrized shadow is also recorded:
  `CircularSector.ByAngle.area_eq_arcLength_div_two` proves
  `area(theta) = arcLength(theta)/2` for rational angles, and
  `CircularSector.ByAngle.sameDerivativeAndInitial` stores the exact
  derivative certificates saying both sides have derivative `1/2` and agree
  at `theta = 0`.
- Arc sample points are now an explicit certified layer in
  `ComputableAnalysis/ArcSamples.lean`.  `ArcSamples.ComplexCert.ofRealPair`
  turns two certified coordinate `RealCert`s into a certified `ComplexCert`,
  `ArcSamples.Stage` and `ArcSamples.Family` turn finite sample lists into
  polygons, and `ArcSamples.UnitQuarterArcFamily` records the
  first-quadrant/unit-circle box conditions expected from a concrete arc
  algorithm.  The exact endpoints `(1,0)` and `(0,1)` are certified, and
  `ArcSamples.quarterArcEndpointChordNormSq` checks that the squared chord
  length between them is exactly `2`.
- The rational Pythagorean parametrization is now the concrete quarter-arc
  sampling route.  In `ComputableAnalysis/ArcSamples.lean`,
  `ArcSamples.Pythagorean.point u =
  ((1-u^2)/(1+u^2), 2u/(1+u^2))` gives rational points on the unit circle,
  and `ArcSamples.Pythagorean.rationalVertices n` samples the arc at
  `u = k/n`.  Theorems `point_normSq`, `point_re_antitone`, and
  `point_im_monotone` prove that these rational points lie exactly on the
  unit circle and move monotonically through the first quadrant.  The inner
  and outer staircase corners are also certified:
  `adjacent_inner_corner_normSq_le_one` puts every lower staircase corner
  inside the unit disk, while `adjacent_outer_corner_normSq_ge_one` puts every
  upper staircase corner outside it.  The adjacent-step estimates
  `adjacent_re_gap_le_four_over_n` and `adjacent_im_gap_le_two_over_n` give
  the first quantitative shrinking bounds for this exhaustion.  This is the
  current concrete foundation for a rational Archimedes exhaustion.
- The current project-facing Archimedes interface is now the smaller
  `ComputableAnalysis/CirclePi.lean`, not the older arbitrary-polygon layer.
  `CirclePi.areaRaw` is the unit-disk-area definition of pi from the rational
  arc samples: the lower area is the inscribed chord sector and the upper area
  is the adjacent-tangent sector.  `CirclePi.CircumferenceExhaustion.piRaw` is
  the half-circumference definition of pi, and `CirclePi.archimedes` is the
  theorem form saying these two `RealRaw`s are equivalent once the concrete
  rational-arc/tangent coupling has been proved.  The root module imports this
  direct route; the older `Archimedes.lean`, `Circumference.lean`, and
  `CircularSector.lean` files are legacy scaffolding for comparison, not the
  main path.
- The circumference route now uses the right outer object: tangent
  intersections, not staircases.  In `ComputableAnalysis/CirclePi.lean`,
  `CirclePi.PythagoreanCircumference.tangentIntersection p q` has coordinates
  `((q.im-p.im)/(p.re*q.im-p.im*q.re),
  (p.re-q.re)/(p.re*q.im-p.im*q.re))`, and
  `adjacent_tangentDet_pos` proves adjacent rational samples do not hit a zero
  denominator.  `outerTangentBoundaryVertices` is the outer polyline from
  `(1,0)` through adjacent tangent intersections to `(0,1)`.
- The area pi raw algorithm is named by `CirclePi.areaAlgorithm`, with the
  concrete implementation under
  `CirclePi.PythagoreanCircumference.areaAlgorithm`.  This is no longer the
  coarse grid-box algorithm from `CircleArea.lean`; the same rational samples
  used for circumference now drive the area interval too.
- The circumference pi raw algorithm is named in
  `ComputableAnalysis/CirclePi.lean`:
  `CirclePi.PythagoreanCircumference.piAlgorithm` is the `RealRaw` for pi as
  half the full circumference.  Its lower bound uses the inscribed chord
  polyline directly, and its upper bound uses the tangent polyline directly;
  each adjacent segment length is evaluated by the existing rational `sqrt`
  interval function inside the pi module.  The remaining proof target is
  `CirclePi.PythagoreanCircumference.CircumferenceCertified`.
- A third geometric pi definition is now named:
  `CirclePi.fourArctanOnePiRawAlgorithm` is `4 * arctan(1)`, where arctangent
  is the Pythagorean dyadic sector-area construction, not the power series.
  The theorem `CirclePi.fourArctanOnePi_compute_eq_areaPi` proves that this
  algorithm has exactly the same stage outputs as the unit-disk area pi.
  Theorems `CirclePi.fourArctanOnePi_equiv_areaPi` and
  `CirclePi.fourArctanOnePi_equiv_circumferencePi` prove the raw equivalences
  to the previous two geometric definitions.  The first uses the exact
  quarter-sector identification plus `innerQuarterArea_le_outerQuarterArea`;
  the second transports the Archimedes equivalence.
- The concrete Archimedes endpoint now goes through the classical finite
  rearrangement picture, not direct inequality hammering.  In
  `CirclePi.PythagoreanCircumference.RearrangedFan`,
  `area_eq_height_mul_half_perimeter` proves that a finite fan of same-height
  triangles rearranges to a rectangle of width half the total base perimeter.
  `VariableRearrangedSectorStage` records the non-uniform sector-fan data at
  one Pythagorean sample stage, and
  `archimedesBounds_of_variableRearrangedStages` derives the two endpoint
  overlap inequalities from rearranged fans.  The concrete rational-sample
  bridge is now `SectorFanBounds`: `archimedesBounds_of_sectorFanBounds` and
  `areaAlgorithm_equiv_piAlgorithm_of_sectorFanBounds` prove, sorry-free, that
  the concrete area and half-circumference `RealRaw`s are equivalent once the
  finite sector fan bounds are supplied.  The finite geometry is now
  discharged by the direct Archimedes/Riemann-sum estimate:
  `chordCross_le_tangentCrossSum` proves the per-edge chord-vs-tangent bound,
  `adjacentChordLengthLo_le_tangentCrossSum` compares the computed chord lower
  interval with the same tangent pieces, and
  `innerEdgeCrosses_le_outerTangentEdgeCrosses` sums the inequalities.  The
  public raw Archimedes theorem is `CirclePi.archimedes_raw`: the
  unit-disk-area `RealRaw` and the half-circumference `RealRaw` are equivalent
  with no certification assumptions.  Internally this is
  `PythagoreanCircumference.areaAlgorithm_equiv_piAlgorithm`.  The certified
  theorem `pythagorean_area_pi_equiv_circumference_pi` still assumes
  `AreaCertified` and `CircumferenceCertified`.
  The remaining certification task is not this finite Archimedes comparison
  but proving `RealRaw.ValidCompute` for the chosen algorithms.  The public
  algorithms now use dyadic refinement: `dyadicStage n` means `2^n`
  Pythagorean arc subdivisions.  The finite geometry remains stage-local, but
  the raw-real stage parameter now refines naturally.
  The working method for the remaining inequalities is: freeze a stage `n`,
  write the exact finite inequality in rational expressions, solve it on paper,
  then formalize that isolated lemma before returning to the raw-real
  certificate.  For the current Pythagorean sample stage, the local variables
  are adjacent unit points `p_k`, `p_{k+1}` and their tangent intersection
  `t_k`.  The finite Archimedes comparison is already reduced to and proved
  from the per-edge inequalities
  `cross p_k p_{k+1} <= cross p_k t_k + cross t_k p_{k+1}` and
  `sqrtLower (|p_{k+1}-p_k|^2) <= cross p_k t_k + cross t_k p_{k+1}`.
  The remaining public-stage certification inequalities are explicit shrinking
  bounds, for example a convenient estimate like
  `4 * (outerQuarterArea (dyadicStage n) - innerQuarterArea (dyadicStage n)) <= C/n^r`
  or any other bound that tends to zero, and the analogous circumference
  bound.  The remaining cross-stage
  certification inequalities are nesting statements; dyadic stages reduce
  these to one-step refinement from a stage to its doubled stage.
  The sqrt bisection layer now proves `sqrtApproxOnDomain_spec`, and
  `CirclePi` turns it into segment-length endpoint lemmas, including the
  tangent-line identity `tangent_segment_normSq_eq_cross_sq` and the chord
  estimate `chordCross_le_segment_hi`.  The first local orientation lemma is
  also in place: `point_cross_nonneg_of_order` proves that ordered rational
  Pythagorean arc points have nonnegative cross product.
- The power-series arctangent pi representative is now named separately:
  `CirclePi.powerSeriesArctanOnePiRawAlgorithm` is `4 * arctan_ps(1)`, where
  `arctan_ps x = x - x^3/3 + x^5/5 - ...`.  This is intentionally not a
  geometric definition.  The theorem
  `CirclePi.powerSeriesArctanOnePi_equiv_fourArctanOnePi_of_directInequalities`
  proves that the direct finite arctangent inequalities on `[0,1]` would
  identify it with the geometric `4 * arctan(1)` definition.  The remaining
  non-tautological target is
  `CirclePi.PowerSeriesArctanOnePiAgreesWithGeometric`.
- Geometric arctangent is now represented by sector area data in
  `ComputableAnalysis/CirclePi.lean`.  `CirclePi.GeometricArctan.SectorAreaBySlope`
  asks for the signed unit-sector area swept from `(1,0)` to the ray `(1,x)`,
  and `CirclePi.GeometricArctan.raw` turns it into an `Elementary.ArctanRaw` by
  doubling the sector area.  This avoids defining arctangent by its Taylor
  series.
- The more arithmetic geometric arctangent route now uses the Pythagorean
  parameter: the point `((1-x^2)/(1+x^2), 2x/(1+x^2))` has angle
  `2 atan(x)`, so its unit-sector area is `atan(x)` directly.  The concrete
  raw algorithm is now dyadic: `CirclePi.PythagoreanArctan.sectorAreaCompute`
  evaluates the sector using `2^n` subdivisions at public stage `n`, exactly
  matching the circle-area route.  The named comparison target is
  `CirclePi.PythagoreanArctan.DyadicAgreesWithPowerSeries`.
  The naive direct-inequality reduction is also now formal:
  `CirclePi.PythagoreanArctan.DirectNonnegativeUnitInequalities` is precisely
  the endpoint-overlap problem on `0 <= x <= 1`, and
  `nonnegativeUnit_allStagesOverlap_of_directInequalities` proves that solving
  those finite inequalities gives all-stage overlap of the two concrete
  `FunctionRaw` outputs on that interval.
  The finite derivative algebra is proved in `ComputableAnalysis/Pi.lean`:
  `Arctan.pythagoreanPoint_normSq`,
  `Arctan.pythagoreanPoint_det_step`, and `Arctan.pythagoreanPoint_dot_step`
  identify the exact unit-circle/determinant/dot-product formulas; the inner
  triangle quotient is `Arctan.pythagoreanSectorLowerQuotient`, and
  `Arctan.pythagoreanSectorLower_error_eq` plus
  `Arctan.pythagoreanSectorUpper_error_eq` prove that the rational lower and
  upper sector quotients both collapse to the derivative kernel
  `1/(1+x^2)`.  The remaining theorem is the geometric squeeze that puts the
  actual sector-area difference quotient between those two finite formulas.
- Arctangent now has named function representations.  The generic
  representation equivalence is `PartialRealFunRaw.AgreeOnOverlap` in
  `ComputableAnalysis/Core.lean`; `Elementary.Arctan.powerSeries` is the
  alternating power-series representation on `|x| <= 1`; and
  `CirclePi.GeometricArctan.functionRepresentation` turns sector-area data into
  the geometric representation.  The next comparison theorem is
  `CirclePi.GeometricArctan.AgreesWithPowerSeries`: geometric arctangent agrees
  with the power-series arctangent on the common rational domain.
  A stronger comparison target is also available:
  `CirclePi.GeometricArctan.AgreesWithPowerSeriesAllStages`, based on
  `RealRaw.AllStagesOverlap`.  It says every geometric interval at every stage
  compares as `overlap` with every power-series interval at every stage, and it immediately
  implies ordinary function-representation equivalence.  This is often the
  cleaner theorem when both algorithms are proved to enclose the same sector
  integral.
- The honest geometric target is now explicit:
  `Pi.GeometricAtanOneRaw` represents the angle from `(1,0)` to `(1,1)`,
  while `Pi.GeometricAtanOneTaylorRemainderSound` is the missing
  Taylor-with-remainder theorem saying that this independently geometric or
  integral arctangent overlaps the arctangent power-series intervals.
  `Pi.leibniz_agrees_with_geometricAtanOne_of_taylor_remainder` proves that
  this bridge is enough to derive Leibniz's formula for geometric pi.
- Main unproved Leibniz/Machin theorem: prove `Pi.LeibnizMachinOverlap`, which
  is exactly the `RealRaw.Equiv` content for the current raw algorithms.  The
  remaining route is to prove that the Taylor/integral interval algorithm
  `arctanInterval` agrees with the geometric branch relation
  `Arctan.HasSlope`.  More precisely, prove
  `Arctan.PowerSeriesRespectsBranchEquality`, then combine it with the proved
  Gaussian slope identity, the Machin branch equality, and alternating-series
  enclosure certificates.
- The pi-level plumbing is now done conditionally and sorry-free:
  `Arctan.piLeibniz_machin_overlap_of_arctan_sound` proves overlap of the
  concrete Leibniz and Machin interval algorithms from
  `Arctan.PowerSeriesRespectsBranchEquality`, and
  `Pi.leibniz_machin_overlap_of_arctan_sound` restates this as
  `Pi.LeibnizMachinOverlap`.  This uses the proved rescaling identities
  `Arctan.piLeibnizInterval_eq_scaled_one` and
  `Arctan.piMachinInterval_eq_scaled_machinQuarter`.
- The honest theorem target is the safe version
  `Arctan.PowerSeriesRespectsSafeBranchEquality`, where every atom being
  Taylor-expanded is certified to lie in `[-1, 1]`.  Machin's expression and
  `atan(1)` are proved safe by `Arctan.machinQuarter_atomsInClosedUnit` and
  `Arctan.one_atomsInClosedUnit`, and
  `Pi.leibniz_machin_overlap_of_safe_arctan_sound` connects that safe analytic
  theorem to `Pi.LeibnizMachinOverlap`.
- Quantitative convergence is now measured for the concrete algorithms:
  `piMachin_width_eq_ratio_mul_leibniz_width` proves that the Machin interval
  width is the Leibniz interval width times
  `machinToLeibnizRatioAt n = 4*(1/5)^(4*n+1) + (1/239)^(4*n+1)` at the shared
  natural alternating-series stage.  The checked estimates
  `machinRatioAt_one_lt_one_over_thirty` and
  `machinRatioAt_five_lt_one_over_ten_million` record the speedup.
- The series layer now owns the natural alternating-stage representation:
  `Series.evenOddInterval partials n` returns the interval between the `2n`th
  and `(2n+1)`st partial sums, and `Series.AlternatingRaw.interval` uses this
  convention.  The pi and arctangent series algorithms are wired to this shape.

## Basel Problem

- `DirichletSeries.zetaTwoRaw` is the checked interval algorithm for
  \(\zeta(2)\); `Basel.baselSeriesRaw` is its project-facing name, and
  `Basel.baselSeriesRaw_valid` proves validity.
- `Basel.piSquaredOverSixRaw pi` computes \(\pi^2/6\) from any valid bounded
  raw pi representative.  The current geometric specialization is
  `Basel.geometricPiSquaredOverSixRaw`, built from `piCircleArea`, with
  validity theorem `Basel.geometricPiSquaredOverSixRaw_valid`.
- `Basel.eulerBasel_geometricPi` is the remaining constructive theorem
  statement relating these two valid computations.  It is not yet a proved
  equivalence and therefore does not complete the Basel scoreboard row.

## Long-Term Theorems

- Convex FTC: for the examples in Chapter 2, the main calculus theorem is the
  convex/concave secant route.  Define the pointwise derivative from shrinking
  centered secant hulls, form Riemann sums of that derivative, and prove the
  endpoint identity by neighboring-secant enclosures plus telescoping.
- Legacy exact FTC facts remain useful as sanity checks, but they are no
  longer the main dependency for elementary functions.  The affine exact
  certificate is `FTC.affineExactCertificate` / `FTC.affine_exact` in
  `ComputableAnalysis/FTC.lean`.
- First checked exact derivative facts: the derivative of an affine function
  is its constant slope, and the derivative of `x^2` is `2x`.
  See `ExactFunction.affine_derivative_effective` and
  `ExactFunction.square_derivative_effective` in
  `ComputableAnalysis/Differential.lean`.
- First checked non-affine FTC estimate: for `F(x)=x^2`, `f(x)=2x` on
  `[0,1]`, the left-sum FTC error at stage `m+1` is exactly `1/(m+1)`.
  See `FTC.ftcError_square_doubleId_zero_one_succ` and
  `FTC.ftcCheck_square_doubleId_zero_one_succ` in
  `ComputableAnalysis/FTC.lean`.
- This estimate is packaged in the older effective FTC style:
  `FTC.square_doubleId_zero_one_effective` chooses `eps.den + 1`
  subdivisions for any positive rational `eps`.
- First checked non-affine computable-number FTC theorem:
  `FTC.square_doubleId_zero_one_integral_equiv_endpoint` proves that the
  nested Riemann-sum integral raw algorithm
  `FTC.squareDoubleIdIntegralRaw`, with intervals `[1 - 1/n, 1]`, is
  `RealRaw.Equiv` to the endpoint difference `1^2 - 0^2`.
  The validity proof is `FTC.squareDoubleIdIntegral_valid`.
  This is the first theorem in the exact form of the original project goal:
  an integral computed by finite rational sums equals `F(b)-F(a)` as a
  computable real.
- Constructive FTA: a rational-complex polynomial of positive degree has a
  computable complex root.
  See `ComputableAnalysis/FTA.lean`.
- First checked FTA base cases:
  exact rational-complex roots lift to computable roots
  (`exactRoot_is_computable`), monic linear polynomials `X - r` have the
  computable root `r` (`monicLinear_has_computable_root`), and `z^2 + 1`
  has the computable root `i` (`zSqPlusOne_has_computable_root`).
- Next FTC extensions: exact polynomial derivative facts, then interval-valued
  Riemann-sum convergence under `IntervalRegularOn`.
- Next FTA extensions: general linear polynomials using certified complex
  division away from zero, quadratic examples via computable square root, then
  the constructive root-search/argument-principle route for arbitrary degree.
- Next complex integral extensions: package polygonal left sums as valid
  `ComplexRaw`s, prove endpoint-primitive cancellation for polynomial
  differentials, then use that as the first sorry-free Cauchy theorem for
  closed polygonal paths.

## Metrics

- Rough proof-size metrics can be generated with:
  `python3 scripts/decl_metrics.py --kind proofs --min-lines 3`.
- For timing, use Lean/Lake profiling on the file being worked on; the size
  report is only a rough line-count companion to the profiler.
