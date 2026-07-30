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
- `RealRaw.Rate` is optional rate metadata that a concrete evaluator may
  expose alongside its validity theorem.  It is not a field of `RealRaw` and
  not a second kind of real number: it is either unknown, eventually
  polynomial, or eventually geometric.  See `RealRaw.Rate` in
  `ComputableAnalysis/Basic.lean`.
- For concrete algorithms, record public rate information as eventual upper
  bounds, not necessarily exact widths.  For pi,
  `PiProofs.piLeibnizRate` records width `<= 4/n`, while
  `PiProofs.piMachinRate` records width `<= 20*(1/2)^n`, i.e. `20/2^n`.
  The literal reciprocal-log integration-by-parts evaluator similarly has
  `Logarithm.piTriangleLogReciprocalIntegralRate`, with width
  `<= 52*(1/2)^n`.  Its square-pullback substitution companion has
  `Logarithm.piTriangleLogSquareSubstitutionIntegralRate`, with width
  `<= 56*(1/2)^n`.
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

## Calculus Readiness Ledger

The Pi table is a release-style integration suite, not a completion score for
the scientific-calculus objective.  It catches agreement failures across
independent finite constructions, but several rows can share one analytic
bridge, and a major capability such as continuous Peano--Baker need not add a
Pi representation.  Do not optimize the Pi numerator at the expense of these
gates.

The integration policy is deliberately narrow: prove the general FTC,
substitution, and integration-by-parts theorems with explicit constructive
certificates, but do not build a catalogue of antiderivatives or named
``techniques.''  An LLM (or a user) may supply a proposed primitive or
decomposition; the project should check its derivative, domain, and endpoint
certificate through those general theorems.  This is not yet a replacement for
Mathlib in arbitrary scientific or engineering proofs: general calculus
closure, analytic exp/log and trigonometric bridges, continuous matrix
Peano--Baker, and broad numerical/PDE infrastructure remain open.

- **Rational interval foundation — checked.** `RealRaw.Valid`, interval
  overlap equivalence, and the source audit excluding Mathlib analysis and
  completed-real completeness are the non-negotiable base.  Re-audit imports
  whenever this module graph changes.
- **Continuity and extension — partly checked.** `IntervalRegularOn` and
  `IntervalRegularOn.epsilonDeltaContinuous` give the literal rational
  epsilon--delta theorem. The scheduled `sqrtOnUnit` bisection branch is now
  a concrete non-exact interval-regular function, with a quadratic rational
  input modulus on `[0,1]`. The non-exact rectangle arctangent now has its
  own literal continuity theorem
  `arctanIntegralRectangleOnUnit_epsilonDeltaContinuous`: its finite tangent
  chart proves `A.lo(x+h) - A.hi(x) <= h`, so `delta = eps` and common stage
  `4 * (eps.den + 1)` make both cross-box gaps and both widths at most `eps`.
  Its checked `arctanIntegralRectangleOnUnit_effectiveModulus` packages the
  same data as the executable schedule `inputPrecision n = n + 1`, with the
  displayed denominator-controlled rectangle stage at output tolerance
  `precisionAtStage n`.
  The concrete product-derivative candidate `arctan x + x/(1+x*x)` now also
  has literal epsilon--delta continuity. Its rational correction is checked
  3-Lipschitz; splitting the output budget as `eps/2` for arctangent and
  `eps/6` for the input correction gives a finite modulus for the whole
  derivative box. Its fixed theorem uses exactly that radius and stage
  `4 * ((eps / 2).den + 1)`; the checked
  `coordinateTimesArctanIntegralRectangleDerivativeOnUnit_effectiveModulus`
  makes this a computable schedule with `inputPrecision n = 6 * (n + 1)`.
  Its checked positive product secants now also satisfy
  `coordinateTimesArctanIntegralRectangleOnUnit_forward_secant_enclosure`:
  the endpoint difference lies in the cell width times the left derivative
  box widened by twice the requested stage tolerance.
  `...forward_secant_uniform_range_enclosure` now composes this with
  epsilon--delta continuity: every derivative value in a selected rational
  radius and the endpoint secant share a box of width at most ten stage
  tolerances. The local data are now definitions rather than extracted
  witnesses: `coordinateTimesArctanForwardContinuityRadius n` is
  `precisionAtStage n / 6`, its companion stage is
  `4 * ((precisionAtStage n / 2).den + 1)`, and
  `coordinateTimesArctanForwardSecantBound` has the corresponding checked
  explicit enclosure theorem. The generic finite global assembly is now checked: adjacent
  common-stage endpoint boxes telescope by interval containment, and a
  uniform partition turns a per-cell width bound `e` into total width at
  most `(b-a)*e`. `TwoStageCandidateDerivativeFTC` now packages the actual
  order of quantifiers: a common derivative-continuity stage may differ from
  the common endpoint stage used by the telescope. Its overlap is derived
  rather than postulated; `SelectedStageCandidateDerivativeFTC` remains the
  coincident-stage special case. The product-specific cell family, common
  endpoint stage, Riemann-width budget, and endpoint-width budget are now
  assembled in `coordinateTimesArctanForwardTwoStageFTC`; Lean proves its
  bounded-sum raw equivalent to the product endpoint raw. The uniform cell
  count `coordinateTimesArctanForwardPartitionPieces` remains the explicit
  finite mesh selector. The product-specific public FTC bridge is now
  complete: `coordinateTimesArctanForwardTwoStageStabilizedRaw` applies
  finite-prefix stabilization to the actual bounded-sum evaluator, with the
  `4/(n+1)` radius proved against the rectangle anchor but not read at
  runtime. Its `..._valid` theorem provides the public construction, and
  `coordinateTimesArctanForwardTwoStageMonotoneDefiniteIdentity` exposes the
  endpoint formula through the monotone, ordinary, and finite-piece integral
  interfaces. The normalization pattern is now generalized as
  `TwoStageCandidateDerivativeFTC.stabilizedRaw`: any two-stage certificate
  supplies a public construction after its bounded-sum width modulus and an
  explicit shrinking endpoint-radius schedule have been given. The remaining
  task is to supply those schedules for further calculus formulas, not to
  reprove the product FTC.
  `UniformRealFun.CertifiedExtension` states the representation-safe extension
  contract. General closure and extension theorems remain work, so this gate
  is not yet a general function-calculus package.
- **Finite integration and FTC — partly checked.**
  `Integral.ConstructionFor`, its validity bridge, and the derivative-bound
  FTC-to-endpoint theorems are checked; the rectangle, Cauchy, and compact
  reciprocal-quartic computations exercise them concretely. The reusable
  single-turn pattern in `TurningPointIntegral` handles a particular
  up-then-down integrand whose (possibly non-rational) turning point is
  represented by shrinking rational brackets: stagewise monotone outer
  constructions are combined with a fixed range box times the unresolved
  middle width. Lean proves the three-part candidate's width shrinks, but a
  `SingleTurnIntegralCompletion` must still prove, function by function, that
  it encloses the intended integral. This is consciously not a universal
  existence definition for integrals. The reusable
  `IntegralIdentities.LipschitzDyadic` constructor now turns a rational
  Lipschitz kernel on `[0,1]` into literal nested Darboux boxes. Its new
  arctangent-kernel specialization has a checked rational Lipschitz constant
  `2`, exact width `4/2^n`, and a stagewise common-right-sum comparison with
  the existing geometric rectangle integral.  The same rectangle construction
  now also has the finite tangent enclosure `x - x^3 <= A_n(x) <= x` for
  every nonnegative rational endpoint, and its zero-endpoint quotient box is
  `[1 - h^2, 1]` for `h > 0`.  This supplies the basepoint finite estimate.
  The new `HasForwardDerivativeAt` interface now packages this endpoint fact
  as the checked one-sided certificate
  `arctanIntegralRectangleOnUnit_forwardDerivativeAtZero`, with derivative
  `1` and exact stage-zero evaluation. The tangent-chart algebra is checked
  as well: at `x`, ordinary step
  `h` is represented by `h / (1 + x * (x + h))`, which the chart sends exactly
  to `x + h`; its scale differs from the kernel at `x` by at most `h` on the
  unit branch.  These estimates now close the full two-sided certificate
  `arctanIntegralRectangleOnUnit_hasDerivative` on `[0,1]`: negative steps are
  reversed to a positive step at the left endpoint and the kernel's rational
  Lipschitz bound transports the derivative back to the requested point.  The
  checked schedule uses derivative stage `8*(n+1)` and signed step budget
  `1/(72*(n+1))`.  This is not an FTC theorem.  What remains is extension to
  interval-regular functions, an effective FTC closure, and then the
  standard function table.
- **Derivative scheduling — corrected interface.** `HasDerivativeOnInterval`
  and the rational-power `HasDerivativeAt` certificate now choose evaluator
  precision from the rational point, nonzero rational step, and requested
  output precision.  This is necessary for an inexact interval evaluator:
  quotienting a fixed-width box by an arbitrarily smaller step cannot have a
  uniform error bound.  Exact rational examples still use the constant stage
  zero; the correction creates the finite scheduling slot needed by the
  arctangent and exponential derivative constructions.
- **Monotone inverse functions — partly checked.** The branch-local
  `InvertibleFunctionOnInterval`/`InverseRaw`/bisection API is checked, with
  the unit-interval square-root search for exact rational targets. Extend it
  to represented targets, then use it for the sine/arcsine and
  exponential/logarithm branches.
- **Differentiated elementary functions — partly checked.** Formal
  power-series derivatives and finite-difference examples are checked. The
  next end-to-end gate is a selected exponential raw that proves `f' = f`,
  followed by uniqueness and the logarithm relation. The literal rational-input
  evaluator `ExpProofs.expPowerSeries x` is now already a valid raw real for
  every `x : Rat`: its finite rational series boxes are nested and have the
  public geometric rate `ExpProofs.expPowerSeriesRate x`, with ratio `1/2`.
  The same evaluator is now the total `PartialRealFunRaw`
  `ExpProofs.expPowerSeriesFunction`, and
  `ExpProofs.expPowerSeriesOnInterval a b` gives its valid rational-interval
  restriction. When zero is in that interval,
  `ExpProofs.expPowerSeriesOnInterval_zero_initial_value` supplies the exact
  function-level initial equivalence required by the ODE interface. This is a
  certified representation layer, not yet an analytic self-derivative theorem
  or a bridge to the other definitions. Its first finite-difference brick is
  now explicit: `expTaylorQuadratic x = 1 + x + x*x/2`, and
  `ExpProofs.expTaylorQuadratic_forwardDerivativeAtZero` certifies its forward
  derivative `1` at zero by the exact quotient `1 + h/2`. This is deliberately
  a finite polynomial theorem, not the missing tail-aware derivative theorem
  for `expPowerSeries`. The
  constant-level compound-interest representative is now additionally packaged as the
  positive base `ExpProofs.ePositive`: its lower interval endpoint is always
  at least `2`, and `ExpProofs.eNaturalPower` gives valid literal natural
  powers between `2^n` and `4^n`. Rational roots, rational-exponent
  continuity, and the self-derivative theorem remain separate open bridges.
- **Linear ODEs — finite core and scalar tail certificate checked; analytic layer open.**
  `PeanoBaker.lean` proves finite chronological products, the ordered-word
  expansion, discrete variation of constants, and recurrence uniqueness:
  the zero-initial forcing response is the explicit time-ordered Duhamel sum
  sum_(k<N) S_(N-1) * ... * S_(k+1) * g_k; every sampled candidate is the
  recursive trajectory, while a zero-initial homogeneous sampled candidate is
  identically zero. Its checked forced
  harmonic-oscillator instance derives the exact second-order Euler recurrence
  after vectorizing position and velocity. `RationalMajorant.factorialTailTerm`
  and `...factorialTailPartial_bound_at_start` now prove the finite rational
  factorial-tail engine: at the computable start
  `2 * C.num.natAbs + 1`, every finite prefix of `sum C^r/r!` is bounded by
  twice its first omitted term, and the shifted version has an additional
  `1/2^shift` factor. `LinearODE.peanoBakerFactorialTail_bound` specializes
  that estimate to `C = M*T`, the coefficient-norm and interval-length
  product in the continuous Peano--Baker plan. The new executable shift
  `peanoBakerFactorialTailShift` and theorem
  `peanoBakerFactorialTail_shifted_le_eps` now turn the geometric tail into
  any requested positive rational tolerance, uniformly over every finite
  remaining prefix. The constant-coefficient degree term
  `constantPeanoBakerSimplexTerm A T r = (T^r/r!) * A^r` and its checked
  one-step recurrence now give the finite algebraic bridge to the exponential
  series. For the quarter-turn generator, the checked finite identity
  `RotationSystem.simplexPartial_even_split` groups the first `2*n` terms as
  `C_n(T) * I + S_n(T) * J`, with executable alternating rational prefixes.
  `RotationSeries.expPartial_imaginary_even_split` proves that the literal
  complex prefix at `i*T` has those same `C_n(T)` and `S_n(T)` coordinates.
  These remain finite algebra; the continuous-simplex interpretation and the
  complex-raw tail certificate are open.
  The scientific-calculus gate is the continuous
  interval-matrix Peano--Baker series with simplex integral boxes, that
  scalar tail certificate lifted to componentwise boxes, and variation of
  constants.
  This is the intended constructive **linear Picard--Lindelöf** theorem:
  Peano--Baker supplies the homogeneous resolvent, variation of constants
  supplies the affine solution, and a bounded zero-initial difference is
  driven to the zero raw vector by an explicit factorial schedule. It includes
  the scalar `f' = f` uniqueness route needed for exponential. General
  nonlinear Picard--Lindelöf remains a later interval-Lipschitz/contraction
  layer.

There is intentionally no aggregate percentage: these gates have distinct
dependencies, and a proof in one does not compensate for a missing proof in
another. The Pi score stays useful only as secondary integration coverage.

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
- Integration by parts should follow the same explicit-piece discipline.
  `leftStieltjesSum`, `rightStieltjesSum`, and
  `finiteIntegrationByParts_withVariation` now prove the exact rational
  rectangle decomposition, including its corner-area correction.
  `RationalPartition.finiteIntegrationByParts_onPartition` and its
  left-endpoint-with-variation counterpart now lift that identity to every
  supplied certified rational partition, with the actual interval endpoints
  on the right-hand side.  The combined coordinate theorem
  `coordinateIntegrationByParts_onPartition_endpoint_bracket` now turns the
  exact identity and maximum-step corner bound into the usable finite bracket
  `b*v(b)-a*v(a)-delta*(v(b)-v(a)) <= left strips <= b*v(b)-a*v(a)` whenever
  the sampled second path is nondecreasing.  It is the finite
  monotone-piece form needed by the `x*arctan x` Pi route, not yet an FTC
  identification of either strip.  The checked
  `quadraticVariationSum` estimates bound that correction by a maximum first
  increment times the second endpoint variation, or by the product of the two
  endpoint variations; negating both paths supplies the decreasing-piece
  version.  `RationalPartition.uniform` now gives the first explicit common
  refinement: the `m*n` rational grid contains both uniform input grids, and
  `mesh_refine_mul_right` proves its width is the old mesh divided by the
  positive refinement factor.  `RationalPartition.Refines` and
  `CommonRefinement` package the two endpoint-preserving index embeddings as
  finite data; `uniformCommonRefinement` constructs the certified uniform
  case, and `Refines.refl`/`Refines.trans` make staged rational refinements
  compositional.  The literal dyadic grids used by the current Riemann
  constructors inherit this interface directly: `dyadic_leftPoint_refines`
  keeps old index `k` at `2*k`, and `dyadic_mesh_refines` halves its mesh.
  Arbitrary rational breakpoints now have a checked local insertion step:
  `insertPoint_refines` embeds the old partition.  The finite scan
  `locateInsertionCell` chooses and certifies the containing cell of any
  in-range rational point, and `insertionChainOfPointList` converts any
  finite in-range rational list into successive scan-and-insert data.
  `InsertionChain.refines` composes those steps, and
  `Refines.point_between_consecutive` keeps every fine point in its parent
  coarse cell.  `clampedPath_quadraticVariation_le_endpointSquare` applies
  the corner estimate directly to partition data.  The maximum-increment
  premise is now also a checked partition interface.  MaxStepAtMost carries a
  nonnegative rational cap on every genuine cell; clampedPath_step_le_of_maxStep
  extends it to the clamped total path; and
  clampedPath_quadraticVariation_le_stepBound_mul_endpointDifference bounds
  that coordinate-path corner correction against any nondecreasing second
  rational path.  Uniform grids instantiate the cap by their literal mesh,
  while unitMeshPath_quadraticVariation_le_one_div_mul_endpointDifference is
  the exact one-over-n endpoint-variation bound needed for sampled
  x-times-arctangent.  The arctangent subcertificate is deliberately split
  in two.  Lean now proves the same-stage box order
  lo(arctan(x), n) <= hi(arctan(y), n) for 0 <= x <= y <= 1 by extending
  the finite rectangle cover of [0,x] with [x,y] and comparing lower and
  upper sums on [0,y]; it is packaged as a weak nondecreasing
  FunctionOnInterval witness.  The compatible nondecreasing rational
  sampling path is now also checked: `QInterval.lowerEnvelope` takes the
  cumulative maximum of the lower endpoints of any weakly ordered box family.
  It stays in every corresponding box, is nondecreasing, and
  `arctanIntegralRectangleMeshSamples_cornerBound` instantiates the unit-mesh
  corner estimate for the fixed-stage rectangle arctangent boxes.  The
  endpoint-order fact is not the kernel's monotonicity in its integration
  variable, and the lower-envelope construction is precisely what prevents
  arbitrary box endpoints from being treated as an exact nondecreasing path.
  The first explicit two-parameter error schedule is now the target:
  at mesh `eps.den + 1` the endpoint variation lies in `[0,1]`, so the
  corner correction is at most `1/(eps.den + 1) <= eps`; independently,
  rectangle evaluation stage `4 * (eps.den + 1)` makes every sampled box
  have width at most `eps`.  These samples now instantiate the exact finite
  integration-by-parts equality: the two left strip sums plus the corner
  correction equal the final sample, and their total is bracketed within
  `1/mesh` (or the requested epsilon under the denominator-plus-one
  schedule) of that endpoint.  The bracket now additionally feeds a valid
  direct-only regression raw: stage `n` uses the point interval at
  `S_(n+1,n)` widened by `1/(n+1)`, and finite-prefix stabilization uses the
  public `4/(n+1)` rectangle-width radius.  Its candidate width is exactly
  `2/(n+1)`, it is equivalent to the rectangle arctangent at one, and four
  times it is a checked supplementary pi evaluator.  It is intentionally not
  a scoreboard completion: the two finite strip sums have not been promoted
  to definite integrals and no canonical logarithm has entered this proof.
  What remains is to connect these finite
  estimates through the product-derivative and FTC certificates.  The
  general finite merge
  is now checked: `commonRefinementOfPartitions` inserts the right
  `breakpointList` into the left partition and recovers the second ordered
  embedding with a bounded `firstOccurrence` scan.  It is deterministic and
  preserves both index embeddings; duplicate breakpoints are retained, so a
  later minimal-union optimization is optional rather than a theorem gap.
  The model unit path has a fully checked vanishing schedule:
  `unitMeshPath_quadraticVariation` is exactly `1/n`, and choosing
  `eps.den + 1` makes it at most any positive rational epsilon.  For the
  integral theorem, extend this interface from the coordinate factor to
  increasing/decreasing function pieces with arbitrary rational breakpoints,
  then supply product/derivative/FTC comparison certificates.  Do not invoke
  a nonconstructive global variation or Jordan decomposition.
- The first raw product bridge is now checked on positive bounded branches.
  `QBox.mulRealInterval_of_nonneg` reduces the four-corner enclosure to the
  lower--lower and upper--upper products.  Given positive rational bounds,
  `RealRaw.mul_valid_of_nonneg_bounded` proves the product raw valid with
  width bounded by `Bx * width(y) + By * width(x)`, and
  `RealRaw.mul_equiv_of_nonneg` preserves changes of certified
  representation.  `RealFunRaw.mul_valid_of_nonneg_bounded` lifts this
  pointwise to rational-input functions.  `FunctionOnInterval.mulOfNonnegBounded`
  now turns that into a domain-aware interval function.  Its first concrete
  use is `IntegralIdentities.coordinateTimesArctanIntegralRectangleOnUnit`:
  the exact coordinate factor and the geometric arctangent rectangle factor
  are uniformly bounded in `[0,1]`, and its stage box is proved to be
  `[x * A.lo, x * A.hi]`.  This is the product representation needed for
  the positive `x * arctan x` branch on `[0,1]`.
  `coordinateTimesArctanIntegralRectangleOnUnit_nondecreasing` now also
  proves its declared increasing direction from the weak arctangent endpoint
  order and nonnegative product endpoints. A general signed product and its
  FTC comparison are still open; the concrete two-sided derivative below is
  checked separately. The
  product endpoint anchors are now checked as well: the box is exactly zero
  at `0`, agrees with the rectangle evaluator at `1`, and its endpoint
  difference is a valid raw equivalent to `arctanGeom 1`.  This is the
  boundary term needed by the finite integration-by-parts identity, not an
  integral identity for the product.  The
  same concrete positive product evaluator now has a checked forward
  derivative at every rational unit-branch point:
  `coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAt` uses
  the raw derivative box `arctan(x) + x/(1+x*x)`. Its positive quotient is
  decomposed exactly into the arctangent quotient and a bounded product term;
  the arctangent stage `8*(n+1)` and step budget `1/(72*(n+1))` close the
  finite error. The earlier zero theorem is its endpoint specialization.
  `coordinateTimesArctanIntegralRectangleDerivativeOnUnit` packages that raw
  box as an interval function, and
  `coordinateTimesArctanIntegralRectangleOnUnit_hasDerivative` proves its
  full signed-step derivative on `[0,1]`: a negative quotient is reversed at
  `x+h`, and a finer rectangle arctangent quotient plus the kernel's
  rational 2-Lipschitz estimate transports the derivative box back to `x`.
  Its explicit step budget is `|h| <= 1/(648*(n+1))`. The derivative boxes
  are now also certified uniformly inside `[0,2]` by
  `coordinateTimesArctanIntegralRectangleDerivativeOnUnit_range` and its
  `..._nonneg_bounded` packaging, supplying the first range datum for a
  derivative-bound FTC certificate. They are also weakly nondecreasing on
  `[0,1]`: the rational term uses the explicit factor
  `(y-x)*(1-x*y)` after clearing positive denominators, and the arctangent
  box uses its geometric endpoint order. Thus
  `coordinateTimesArctanIntegralRectangleDerivativeOnUnit_nondecreasing`
  supplies endpoint derivative ranges on every positive rational cell. The
  checked forward-range enclosure now supplies one common box for every
  derivative value within its continuity radius and the endpoint difference,
  with an explicit ten-tolerance width bound. Its radius, derivative stage,
  and hull bound are now named computable definitions. The derivative-continuity
  radius and evaluation stage now come from the checked effective modulus,
  not a choice extracted from epsilon--delta existence. The compatible uniform rational
  partition is now selected by the finite denominator product
  `(delta.den + 1) * 72 * (n + 1)`. Its cell containment, common endpoint
  transport stage, global Riemann-width and endpoint-width schedules are
  now all checked in `coordinateTimesArctanForwardTwoStageFTC`, which proves
  the bounded-sum raw equivalent to the product endpoint raw. That raw is now
  normalized by `coordinateTimesArctanForwardTwoStageStabilizedRaw`: finite
  intersections of its widened bounded-sum boxes are valid and shrinking,
  while the rectangle anchor is proof-side only. Thus the actual finite-sum
  computation supplies `coordinateTimesArctanForwardTwoStageMonotoneDefiniteIdentity`,
  a public definite-integral identity equivalent to `arctanGeom 1`.
  The
  exact algebraic core is now formalized for arbitrary rational functions:
  `ExactFunction.product_differenceQuotient_right` keeps the second factor
  at the right endpoint, while `..._corner` exposes the explicit
  `h * D_h(u) * D_h(v)` remainder.  The checked theorem
  `..._error_le` also gives the exact three-term absolute-error allocation:
  the two component derivative errors weighted by the opposite point value
  plus that corner remainder.  The concrete product certificate now bounds
  that remainder and the endpoint replacement through interval continuity
  data, and stabilizes the resulting two-stage finite sum into a public FTC
  construction; no limit or completeness principle is being assumed.  The
  first component certificate is now checked in the actual interval-valued
  derivative interface: `FunctionOnInterval.exactRatAffineDerivative` proves
  the finite quotient of every exact affine rational function is its constant
  slope, and `IntegralIdentities.coordinateOnUnitDerivative` specializes it
  to `d/dx x = 1` on `[0,1]`.  The arctangent certificate, its remainder
  budget, the product closure, and the product-specific FTC are now checked.
  The error
  algebra is now two-sided:
  `ExactFunction.product_differenceQuotient_error_le_qabs` carries `qabs h`
  in the corner budget, with the earlier nonnegative-step theorem as its
  forward-mesh corollary.  This matches the interval derivative interface's
  signed rational steps.
- A future pi coverage bridge should exercise this theorem rather than merely
  mention it: prove
  `pi = 4 * integral_0^1(arctan x) + 2 * log 2` from integration by parts.
  The product FTC bridge and arctangent derivative are now available; this
  still requires an explicit separate arctangent strip, its monotone-piece
  refinement/splitting theorem, and canonical exponential/logarithm alignment.
  This is deliberately the long exp/log/ODE route: first identify the
  logarithmic integral with the inverse of canonical exponential, use the
  linear Peano--Baker/Picard--Lindelöf uniqueness theorem to equate the
  power-series, Euler, and inverse-integral exponentials, then transport the
  resulting `log 2` through the integration-by-parts identity.  A later
  complex corroboration can prove `pi = -2i * log(i)`, but it needs
  represented-input extension and the rotation-system bridge in addition.
  `Logarithm.logTwoSeries` now supplies a valid, rate-certified alternating
  harmonic raw presentation of `log 2`.  Its lower endpoint is now proved
  exactly equal, for every positive mesh count, to the literal uniform right
  Riemann sum for `t ↦ 1/(1+t)`:
  `Logarithm.logTwoLo_eq_logTwoKernelRightRiemann` factors the calculation
  through `H_(2*n) - H_n` and cancels the mesh term by term.  The generic
  finite right-sum/Darboux containment and the public uniform-mesh identity
  now give `Logarithm.logTwoDarbouxCompute_contains_dyadicSeriesLower`; common
  dyadic refinements then prove the final raw-real theorem
  `Logarithm.logTwoSeries_equiv_logTwoReciprocalIntegral`.  This discharges
  the concrete endpoint bridge using rational boxes alone.  The distinct
  remaining logarithm gate is to identify that integral raw with the inverse
  branch of the selected canonical exponential.  The elementary
  change-of-variables algebra is now checked as well:
  `Logarithm.logTwoSquareMesh_substitution_identity` writes the finite
  left-Stieltjes sum for `t = x*x` as the ordinary left mesh sum for
  `2*x/(1+x*x)` plus `Logarithm.logTwoSquareMeshCorrection`; the correction
  is nonnegative and at most `1/n` on the `n`-cell mesh
  (`logTwoSquareMeshCorrection_le_one_div`).  This finite
  square-substitution core is now promoted all the way to the reciprocal
  integral: 
  logTwoSquarePullback_lipschitz_on_unit certifies 2*x/(1+x*x) as
  2-Lipschitz, and logTwoSquareStieltjesRaw_equiv_pullbackIntegral identifies
  the stabilized finite Stieltjes evaluator with its valid
  Lipschitz--Darboux integral.  The checked square-block reindexing compares
  it with the ordinary reciprocal t-mesh: each block contributes at most
  `4/n^2`, so `logTwoSquareMesh_sub_uniformLeftEndpoint_bounds` gives the
  aggregate `4/n` bound, and
  `logTwoSquarePullbackIntegral_equiv_reciprocalIntegral` proves the
  pullback integral equal to the existing `logTwoReciprocalIntegral`.
  The new direct raw pi evaluator
  `PiProofs.piTriangleLogSquareStieltjes` combines that stabilized
  Stieltjes logarithm with the finite arctangent triangle.  Its validity and
  equivalence to both the reciprocal-log formula and area pi are checked in
  `PiProofs.lean`; `pi.squareStieltjes` exposes it as a
  supplementary algorithmic view, not another coverage row.
  The first arctangent--logarithm integration-by-parts strip is now a
  separate literal certified integral, not just a scaled notation:
  `arctanLogKernelIntegral` integrates `x/(1+x*x)` with Lipschitz constant
  one. `LipschitzDyadic.compute_natScale` proves the finite Darboux boxes
  respect natural scaling exactly, so the stagewise theorem
  `logTwoSquarePullbackIntegral_compute_eq_two_arctanLogKernelIntegral` and
  the endpoint theorem
  `two_arctanLogKernelIntegral_equiv_logTwoReciprocalIntegral` establish
  `2 * ∫₀¹ x/(1+x*x) dx ≡ log_rec 2`; its composition with the independent
  alternating-harmonic comparison now also gives the direct theorem
  `two_arctanLogKernelIntegral_equiv_logTwoSeries` to `log_series 2`.  The
  scaled strip has exact dyadic width `4/2^stage`, recorded by
  `two_arctanLogKernelIntegral_compute_width`.
  These are endpoint equivalences at the rational name two, not the pending
  function-level canonical-logarithm theorem. The remaining Pi-route gates
  are a general effective-FTC extension beyond the supplied unit arctangent
  triangle construction and the later canonical exp/log identification.  The
  finite predecessor and its unit construction are now checked:
  `arctanComplementKernelIntegral` is the literal 3-Lipschitz integral of
  `(1-x)/(1+x*x)`, and the exact Darboux-box addition theorem
  `LipschitzDyadic.compute_add` proves that this strip plus
  `arctanLogKernelIntegral` is stagewise the 4-Lipschitz box for
  `1/(1+x*x)`. Common uniform-left sums yield
  `arctanStripIntegrals_add_equiv_arctanKernelIntegral`. The supplied unit
  triangle construction now identifies the complementary strip with its
  arctangent integral; this is still not a new Pi-scoreboard row because the
  result is not a reusable effective-FTC theorem. The mesh-level triangle/Fubini
  reindexing is separately checked:
  `LipschitzDyadic.uniformTriangleRightSum_eq_complementUniformLeftEndpointSum`
  proves the exact identity between an outer right sum of fixed-mesh inner
  left prefixes and the complementary left sum `(1-x)*f(x)`. It is obtained
  from `finiteIntegrationByParts`, so it supplies the required finite
  rectangle geometry without importing continuous Fubini. The supplied
  direct dyadic specialization is now
  packaged as `arctanKernelTriangleRaw`: its runtime evaluator is only the
  finite triangle sum for `1/(1+x*x)`, its public stabilization radius is
  `6/2^n`, and Lean proves it equivalent to
  `arctanComplementKernelIntegral`.  Lean now also packages that exact runtime
  as `arctanIntegralTriangle`, a monotone integral construction for the
  certified `arctan.integral.rectangle` unit function.  Its finite triangle
  reindexing is recorded as the construction's explicit provenance; it does
  not assume general Fubini or integral-linearity.
  The companion raw `arctanKernelTrianglePlusLog` now adds this triangle
  computation to the certified `x/(1+x*x)` logarithmic strip.  Its proved
  equivalence to `arctanGeom(1)` makes it a finite strip/Fubini regression of
  the same arctangent endpoint.  The public theorem
  `arctanIntegralTriangle_add_logKernelIntegral_equiv_productIntegral` further
  identifies the supplied triangle integral plus that strip with the
  independently certified product-FTC integral.  This is not yet the pending
  calculus theorem `4 * ∫ arctan + 2 * log 2 = pi`: canonical exp/log
  transport and a general effective-FTC extension beyond the supplied unit
  construction remain separate work.
  The direct endpoint now packages two supplementary raw formulas:
  `Logarithm.piTriangleLogReciprocalIntegral =
  4 * arctan.integral.triangle + 2 * log_rec(2)` and
  `Logarithm.piTriangleLogSeries =
  4 * arctan.integral.triangle + 2 * log_series(2)`.
  Their formal product-FTC bridge is
  `piTriangleLogReciprocalIntegral_equiv_four_coordinateTimesArctanForwardTwoStageMonotoneIntegral`
  (and its series counterpart); both then reach the geometric arctangent
  endpoint and the circle-area pi.  The literal reciprocal-log formula is now
  the sixth `PiCoverageBridge` constructor: it tests a supplied finite
  triangle, Darboux-strip, product-FTC, and logarithm route, with direct rate
  `52/2^n`.  It still does not establish a general effective
  FTC/integration-by-parts theorem or canonical exp/log transport; those are
  the stronger remaining refinement of this row.
  The square-pullback companion
  `Logarithm.piTriangleLogSquareSubstitutionIntegral` is the seventh bridge:
  its endpoint is `2 * ∫_0^1 2*x/(1+x*x) dx`, it reaches the reciprocal-log
  formula by the finite `t = x*x` mesh correction, and its direct rate is
  `56/2^n`.  It is the concrete substitution regression, not a general
  change-of-variables theorem.
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
  the finite-interval calculus and ODE interfaces.  The concrete finite
  integral and projective/Cauchy comparison are now complete: the literal
  dyadic raw `reciprocalQuarticMinusOneCompactDyadicIntegral` is valid and
  equivalent to `cauchyFullLineIntegral`, and therefore
  `PiProofs.piReciprocalQuarticCompact_equiv_piCircleArea` makes the `a=-1`
  case another counted computation of `piCircleArea`.  The expected-value
  side remains packaged as
  `IntegralIdentities.reciprocalQuarticMinusOneExpectedPi`, with theorem
  `PiProofs.reciprocalQuarticMinusOneExpectedPi_equiv_piCircleArea`.  The
  general `ReciprocalQuarticMinusOneProjectiveRoute` is still useful as a
  parameterized interface for future projective constructions, but it is no
  longer a prerequisite for the concrete route or its scoreboard equality.
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
  partitions into their symmetric positive cores and two endpoint cells,
  while accounting for the reflected cells' right-endpoint convention.  The
  affine transport is now formally an ordered cover of `[-1, 1]`, so that
  remaining split is a finite partition calculation.  The orientation itself
  is now checked cellwise: a reflected negative left-endpoint cell is exactly
  the positive right-endpoint cell, for both compact Lipschitz brackets.
  `projectiveCompactReflectedIntervals_covers` and
  `projectiveCompactReflected_append_covers` now certify the corresponding
  ordered symmetric cover, while the two
  `projectiveCompactLipschitz*Sum_reflected_append_eq_right_add_left` theorems
  identify its complete left-endpoint sums with the positive right- plus
  left-endpoint sums.  The remaining finite identity is now proved too:
  `reciprocalQuarticMinusOneCompactAffineDyadicIntervals_succ_eq_reflected_append`
  shows that the literal affine image of stage `n + 1` is the reflected
  stage-`n` mesh followed by that mesh, and
  `reciprocalQuarticMinusOneUnitDyadicCompute_succ_eq_orientedSymmetric`
  identifies the actual candidate box with the resulting oriented symmetric
  bracket, and
  `reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_symmetric`
  connects that literal box to the existing factor-two projective core at the
  same finite stage.  The only remaining analytic assembly is to trim its two cells
  touching `±1`, couple the interior bracket to the scheduled projective
  Cauchy bracket, and absorb them using the already-valid dyadic tail raw.
  That trim is now literal rather than schematic:
  `reciprocalQuarticUnitDyadicCoreIntervals` deletes the final cell of the
  actual positive mesh, `reciprocalQuarticUnitDyadicCoreIntervals_covers`
  proves it covers `[0, 1 - 2^(-n)]`, and
  `reciprocalQuarticUnitDyadicIntervals_eq_core_append_tail` recovers the full
  mesh by appending exactly the endpoint cell.  Its factor-two compact bracket
  already overlaps the two-branch projective Cauchy bracket by
  `reciprocalQuarticUnitDyadicCore_symmetric_overlaps_projective`.  The
  formerly separate endpoint assembly is now checked at each finite stage:
  `projectiveCompactDyadicOrientedTailUpper_le` bounds the two oriented
  candidate endpoint cells by the existing tail raw,
  `projectiveCompactOrientedSymmetric_append_overlaps_tailEnclosure` is the
  finite bracket-combination lemma, and
  `reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_coreTail` proves
  that the actual candidate box at stage `n+1` overlaps the literal trimmed
  core bracket enlarged by that error budget.  What remains is the raw-level
  nesting/shrinkage construction that joins these core-and-tail boxes to the
  existing full-line Cauchy raw; this is not yet a Pi equivalence.  The next
  transfer is now direct rather than an invalid transitive use of interval
  overlap: the compact symmetric core has exact width at most `32 * 2^(-n)`,
  and `reciprocalQuarticMinusOneUnitDyadicCompute_succ_overlaps_projectiveCauchyCoreTail`
  proves that the literal candidate overlaps the projective Cauchy core after
  widening both compact-core sides by that proved width and the upper side by
  the endpoint budget.  The remaining analytic task is specifically to join
  this shrinking envelope to the completed full-line Cauchy raw.  The
  separately proved `6*n` midpoint-refinement schedule for the projective
  chart is now connected to the literal trimmed core by a genuine finite
  comparison: `reciprocalQuarticUnitDyadicCore_symmetric_overlaps_scheduled`
  applies a general rational Lipschitz-partition comparison to the two ordered
  covers of the same compact interval.  This is deliberately not transitivity
  of interval overlap.  That bridge step is now proved: the actual candidate
  reaches the two-branch scheduled Cauchy hull after adding the literal-core
  width, the scheduled-core width, and the removable-endpoint budget.  The
  remaining task is the separate finite comparison between that hull and the
  completed full-line Cauchy raw.
  The rational endpoint side of that assembly is now explicit too:
  `projectiveCompactDyadicCauchyTailRadius_le` proves that the reciprocal
  projective endpoint at compact stage `n + 1` is at most `2 * 2^(-n)`.
  After the two-branch factor this gives the intended dyadically vanishing
  Cauchy-tail scale.  Its finite reciprocal rectangle transport is now
  checked cellwise and for arbitrary finite lists of strictly positive cells:
  `cauchyReciprocalIntegralSum_overlaps` compares the original and inverted
  rectangle brackets without invoking a completed integral.  The necessary
  order bookkeeping is now checked too:
  `cauchyReciprocalReversedIntervals_covers` sends a positive ordered cover
  of `[a,b]` to one of `[1/b,1/a]`, and its reordered sum has the same
  overlap.  The refined source tail is now explicit rather than an intended
  construction: `cauchyTailDyadicIntervals a n` affinely transports the
  midpoint mesh to `[a,1]`; Lean proves its cover and strict positivity, and
  `cauchyReciprocalTailDyadicIntervals_covers` reverses it into the ordered
  far-side cover `[1,1/a]`.  Its two finite Cauchy brackets overlap by
  `cauchyReciprocalTailDyadicIntervals_overlaps`.  The projective endpoint
  selection is now checked as well: at compact stage `n+2`,
  `projectiveCompactDyadicCauchyTailStart n` is positive and at most one;
  its reciprocal is exactly the finite projective coordinate.  Consequently
  `projectiveCompactDyadicCauchyTailIntervals_covers` supplies an explicit
  ordered mesh from `1` to that coordinate, and its finite brackets overlap
  the compact-side tail.  The two finite assembly covers are now formalized:
  `cauchySplitDyadicIntervals` partitions `[0,1]` at any rational tail start
  and has a Cauchy bracket overlapping the canonical unit mesh; meanwhile
  `cauchyUnitReciprocalTailDyadicIntervals` joins that canonical unit mesh to
  the ordered reciprocal tail.  At compact stage `n+2`,
  `projectiveCompactDyadicCoreIntervals_overlaps_cauchyAssembly` proves that
  this latter mesh and the literal projective core cover exactly the same
  Cauchy interval.  The split source mesh has squared mesh at most `2^(-n)`
  and integral-box width at most `2 * 2^(-n)`.  Finally the tail start has a
  matching lower dyadic bound `2^(-(n+2))`.  The corresponding far-tail
  estimate is now proved as well: refining its source at stage `5*n + 8`
  gives a reciprocal Cauchy rectangle width at most `2 * 2^(-n)`.  This uses
  a new global nonnegative Cauchy cell-width estimate and a reciprocal mesh
  squared-sum bound; it does not appeal to an improper integral.  What
  now-shrinking scheduled core and the unit-plus-tail assembly have also been
  combined: `projectiveCompactDyadicCauchyCore_integral_width_le` gives the
  former an `8 * 2^(-2n)` Cauchy width bound, the assembly has width at most
  `4 * 2^(-n)`, and their `QInterval.hull` is a common bridge envelope with
  width at most `12 * 2^(-n)`.  Lean now scales that positive bridge for the
  two chart branches and proves
  `reciprocalQuarticMinusOneUnitDyadicCompute_succ_succ_succ_overlaps_scheduledCauchy`:
  the actual candidate reaches it after paying the literal-core width, the
  scheduled-core width, and the endpoint budget.  The remaining comparison is
  between this two-branch finite Cauchy hull and the completed full-line raw.
  The first half of that comparison is now formalized independently:
  `cauchyUnitReciprocalTailDyadicIntervals_overlaps_twoUnitEnvelope` encloses
  the positive unit-plus-reciprocal-tail mesh by two standard unit meshes.  It
  pays only the rational near-zero length and the compact tail-mesh width;
  `projectiveCompactDyadicCauchyTailStart_le_dyadic` and
  `cauchyTailDyadicIntervals_integral_width_le_dyadic` prove that both vanish
  at a certified dyadic rate.  These two sides are now combined in
  `reciprocalQuarticMinusOneUnitDyadicCompute_succ_succ_succ_overlaps_fullCauchy`:
  the actual candidate overlaps one explicit rational envelope centred on the
  four-unit-mesh Cauchy calculation.  Remaining work is raw-level enclosure
  shrinkage, not any unproved finite change-of-variables identity.
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
- The completed rational-slope half of that route is now exposed as
  `RationalCircle.GeometricTrig.FirstQuadrantArctanWitness`.
  `arctan_to_sine_cosine_coordinates` packages one arctangent equation
  `arctanGeom(u) ~ t*pi/4`, the exact stereographic formulas
  `cos = (1-u^2)/(1+u^2)` and `sin = 2u/(1+u^2)`, and the unit-circle
  identity. The special-values table consequently treats that arctangent
  equation as the only colored proof-status obligation; extending the
  witness from a rational slope to a bisection-produced raw slope remains
  the non-endpoint task.
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
  `ComputableAnalysis/ElementaryFunctions.lean`. Repeated multiplication is
  now itself checked: `PositiveRealRaw.natPow_valid_and_bounds` proves every
  natural power valid and enclosed between the corresponding powers of the
  supplied positive lower bound and initial upper endpoint, and
  `natPowPositive` packages it as a new positive raw real. Constructing the
  non-integral root layer and its epsilon--delta exponent-continuity proof
  remains the next rational-power task.
  At the constant level, `ExpProofs.eEulerNested` now gives a direct valid
  repeated-multiplication representative of (e): stage `n` evaluates
  ((1+1/(n+1)^2)^{(n+1)^2}) and carries the nested radius `8/(n+1)`.
  Its exact width is `16/(n+1)`, and it is proved equivalent to the sharp
  compound-interest evaluator before being stored in the abstract
  `ExpProofs.e` handle. This is a certified constant construction, not yet a
  function-level `exp' = exp` theorem.
  The generic rational-input power-series raw now also has its exact
  zero-input normalization checked: every series stage at `0` is precisely
  `[1,1]`, via `ExpProofs.expPowerSeries_zero_compute_eq`;
  `expPowerSeries_zero_equiv_one` packages the raw equivalence and
  `expPowerSeries_zero_valid` supplies validity.  The finite
  repeated-multiplication evaluator has center exactly `1` at zero and
  `expEuler_zero_equiv_one` proves its explicit-radius boxes overlap that
  same point.  These initial-value facts are deliberately distinct from the
  pending self-derivative and nonzero-input comparison theorems.
  The finite algebra for that nonzero comparison is now checked too:
  `fallingFactorialRat`, `eulerBinomialTerm`, and `eulerBinomialPrefix` expose
  the rational binomial coordinates, and
  `euler_binomial_prefix_nat_expansion` proves the exact expansion of
  `(1 + x)^m`.  At `x = 1/m` this is the literal Euler product in
  factorial-series coordinates. The coefficient-error bound is now checked:
  each gap is bounded by `k*(k-1)/(2*m*k!)`, its finite sum by `3/m`, and
  the square-mesh error fits the nested Euler radius. Consequently
  `ePowerSeries_equiv_eCompoundInterest` is a completed constant-level
  series/compound equivalence, and `eCertified` stores the series raw as an
  alternative alongside both repeated-multiplication raws. No completeness or
  analytic binomial theorem is assumed.
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
  The concrete reciprocal kernel is now interval-regular, and hence has
  literal rational epsilon--delta continuity, on `[1,2]`:
  `Logarithm.oneOverXOnOneTwo_intervalRegular` uses the exact enclosure
  `[1/r, 1/p]` for each rational `[p,r]`.  The logarithm-at-two bridge is now
  checked: the uniform right mesh is enclosed by the nested dyadic Darboux
  boxes and `logTwoSeries_equiv_logTwoReciprocalIntegral` completes the raw
  equivalence.  This is a finite rational comparison, not a continuity or
  topology assumption; aligning it with the selected canonical exp/log
  inverse branch remains the next distinct theorem.
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
  rather than by ad hoc estimates, specialize the constructive linear
  Picard--Lindelöf theorem to the scalar equation `f' = f` with `f(0) = 1`,
  then prove the equivalent unit-slope characterization of the base at zero.
  See
  `SolvesSelfDerivativeOnInterval` and `SelfDerivativeInitialValueUnique` in
  `ComputableAnalysis/Differential.lean`.  The reusable linear theorem is
  built from continuous Peano--Baker simplex boxes and factorial tail boxes;
  its uniqueness interface explicitly requires equality of the rational
  initial coordinate and equivalence of the two certified initial raw values.
  general nonlinear Picard--Lindelöf can later add interval-Lipschitz Picard
  iterates, rational short-interval contraction, and finite subdivision.
  Both are constructive existence-and-uniqueness data, not appeals to
  real-number completeness.

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
- The same finite layer now gives the homogeneous action a concrete transition
  matrix: `chronologicalStepProduct S 0 N = S_(N-1) * ... * S_0`, and
  `homogeneousTrajectory_eq_chronologicalStepProduct` proves that this matrix
  acts on the initial state exactly. The Euler specialization
  `chronologicalStepProduct_eulerIncrement` is the already-checked
  Peano--Baker chronological product. The strengthened sampled
  variation-of-constants theorem
  DiscreteLinearSystem.trajectory_eq_transition_add_duhamelSum now splits
  an inhomogeneous trajectory into that finite transition of its initial state
  and the literal time-ordered forcing sum
  sum_(k<N) S_(N-1) * ... * S_(k+1) * g_k.
  trajectory_zeroInitial_eq_duhamelSum separately identifies the latter
  with the recursive zero-initial response. ForcingZero makes that response
  vanish. `chronologicalStepProduct_split` additionally proves the
  time-shifted finite semigroup law
  `T(s,m+n) = T(s+m,n) * T(s,m)`, the exact sampled predecessor of the
  continuous state-transition composition law.
  The new `SolvesRecurrence` and `SolvesHomogeneousRecurrence` witnesses
  separate the recurrence specification from its recursive evaluator.
  `solvesRecurrence_eq_trajectory` proves every sampled candidate is the
  unique trajectory, and `solvesHomogeneousRecurrence_zero` proves the
  zero-initial homogeneous candidate is identically zero. This is the
  exact discrete seed for the later factorial-tail uniqueness estimate.
  `LinearODE.HarmonicOscillator` now instantiates that generic system for
  `q'' + omega^2 q = r`: `eulerStep_position` and `eulerStep_velocity`
  give the two coordinate updates, and
  `trajectory_position_secondDifference` eliminates velocity to prove the
  exact scalar Euler recurrence. This is the checked finite bridge from the
  chapter's familiar second-order model to general vector-valued
  inhomogeneous Peano--Baker; it is not a continuous convergence theorem.
  Constant increments are checked exactly by
  `chronologicalProduct_constant` and `peanoBakerDiscreteSum_constant`, giving
  `(I + B)^N`; `peanoBakerDiscreteSum_zeroCoefficient` supplies the zero
  coefficient identity case. The new `PairwiseProductZero` specialization is
  a proved finite nilpotent case: when every `B_i * B_j` is zero,
  `chronologicalProduct_pairwiseProductZero` and
  `peanoBakerDiscreteSum_pairwiseProductZero` collapse the exact transition
  to `I + matrixSequenceSum B N`.
  The constant-coefficient rotation specialization is now checked as well:
  `LinearODE.RotationSystem.generator_square` proves that the rational
  quarter-turn matrix squares to `-I`, while `generator_pow_even`,
  `generator_pow_odd`, `simplexTerm_even`, and `simplexTerm_odd` put every
  finite Peano--Baker coefficient into its alternating cosine-type or
  sine-type form. This is a finite algebraic precursor of the intended Euler
  identity, not a continuous series or ODE-identification theorem.
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
- The blueprint now fixes the chapter's proof direction: start from the
  forced second-order oscillator, turn it into the general affine vector
  equation `x' = A(t)x + b(t)`, construct Peano--Baker plus Duhamel boxes for
  that general problem, and prove uniqueness by iterating the zero-initial
  Volterra identity until the factorial estimate is below an arbitrary
  rational tolerance.  Only then specialize to the oscillator and to
  `E' = E`, `E(0) = 1`.  This recovers sine/cosine and identifies every
  exponential representative that has independently supplied the same
  derivative and initial-value certificate.  The positive inverse is the
  canonical logarithm used by the long arctangent integration-by-parts Pi
  route; this is a named dependency chain, not an extra Pi-scoreboard row.
- Next analytic target: build interval matrices for ordered-simplex
  Peano--Baker terms, prove a factorial tail enclosure from a rational
  coefficient bound, and obtain state-transition and variation-of-constants
  formulas for `x' = A(t)x + b(t)`. Together these are the effective linear
  Picard--Lindelöf theorem: the zero-initial homogeneous case gives
  uniqueness, and the factorial tail is the explicit solution modulus. The
  next specializations are the scalar `f'=f` exponential route, the analytic
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
- Next concrete integral targets, beyond the checked unit-branch arctangent
  rectangle/Lipschitz comparison and without a general integrability theorem:
  `integral 1/x = log x` on positive intervals,
  `integral 1/(1+x^2) = arctan x` on general certified branch intervals,
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

- `PiProofs.PiCoverageBridge` is the π progress measure in
  `blueprint/src/pi-scoreboard-table.tex`.  Its eight constructors have one
  checked `RealRaw.Equiv` witness per distinct bridge: Archimedean geometry,
  arctangent versus alternating series, finite definite integration, the
  supplied finite integration-by-parts formula, its finite square-substitution
  companion, compactified improper integration, the nontrivial
  reciprocal-quartic kernel, and bounded symmetric Cauchy assembly.  The theorem
  `PiCoverageBridge.equivalent` derives each witness from
  the certified presentation registry.  This is a coverage suite, not a
  completion percentage: multiple implementations can share a bridge, and a
  continuous Peano--Baker theorem or an analytic proof that `exp' = exp` would
  be major calculus progress without adding a π row.  For ordinary downstream
  use, `PiProofs.piPresentation_equiv source target` directly compares any two
  named checked presentations through the certified area representative.  It
  is a registry interoperability theorem, not an extra scoreboard witness.
  The generic `Real.Representation.equiv` compares any two certified views of
one abstract real; its pi specialization `PiProofs.pi.representations_equiv`
therefore also covers the supplementary finite integration-by-parts-mesh and
triangle-log-series views that intentionally
sit outside `PiPresentation`.
  The now-certified `pi.dirichletBeta` view records the natural Dirichlet
  formula `pi = 4 * L(1, chi4)`; its literal boxes are stagewise the Leibniz
  boxes, so it is deliberately not a ninth alternating-series capability.
  `PiPresentation.integrationFamily` and the primary registry retain the
  polygonal, stabilized, Nilakantha, and single Machin variants as executable
regressions.  `piCertified.alternatives` also literally carries the checked
`pi.integrationByPartsMesh` and `pi.triangleLogSeries` raw evaluators; those
remain outside the coverage
count.  The reciprocal-log triangle formula is instead the primary
  `pi.integrationByParts` view and the sixth finite-calculus bridge.  It is
  not a substitute for the pending general arctangent--logarithm effective-FTC
  bridge or canonical-logarithm transport.  The primary
  canonical handoff is now formalized separately:
  `PiProofs.CanonicalLogTwoCertificate` packages a valid raw value at two
  together with its equivalence to `Logarithm.logTwoReciprocalIntegral`, and
  `piFromCanonicalLogTwo_equiv_piCircleArea` then proves the canonical-form
  pi formula.  Constructing that certificate from an inverse-exponential
  logarithm remains the one explicit analytic gap; it is not an additional
  scorecard row.
  `pi.squareSubstitution` view is the seventh bridge: it preserves the
  square-pullback integral and verifies its finite substitution transport to
  the reciprocal-log view.
  The eighth bridge is `pi.symmetricCauchy`: the public general integral
  construction folds the explicitly certified increasing `[-1,0]` and
  decreasing `[0,1]` Cauchy-kernel branches.  Its direct pi raw evaluator has
  width at most `16 / (n + 1)`.  This is a concrete piecewise-monotone
  assembly regression, not another arctangent-series entry.
  The original direct perimeter is now a certified square-root-enclosure
  computation;
  arcsine/Newton and Gaussian are future inverse/integral and
  exponential/full-line probes.  Basel and Brouncker are advanced-analysis
  topics outside the scientific-calculus progress board.  Euler identity with
  the complex logarithm is instead a named but unmarked long scoreboard
  target: it should establish `exp(i * pi / 2) = i` and
  `pi = -2i * log(i)` by the complex rotation-system extension of the linear
  Peano--Baker uniqueness theorem.  The primary gates remain the
  no-completeness audit,
  epsilon--delta continuity and extension, finite integration/FTC, inverse
  functions, differentiated elementary functions, and continuous ODE
  solution operators.
- Direct `piCircumference` is now complete.  `CircumferenceBridge.innerChordLowerRefinement`
  combines exact rational checks at stages `1, 2, 4, 8` with a uniform
  fourth-order secant--curvature budget for every later dyadic stage.
  `PiProofs.piCircumference_valid` then certifies the original evaluator,
  and `PiProofs.piCircumferenceDirect_equiv_piCircleArea` supplies its
  finite Archimedean equivalence.  The named view
  `PiProofs.pi.circumferenceDirect` makes this literal path evaluator
  available through the abstract pi handle.
  `piCircumferenceDirect_equiv_piCircumferenceFan` and
  `pi.circumferenceDirect_equiv_circumference` now make its agreement with
  the default cross-fan circumference view explicit.  This is one geometry
  capability, not a new scoreboard row.


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
- The finite Archimedes comparison aligns the polygon and circumference
  computations.  `PiProofs.piCircumference_valid` now closes the original
  chord-path evaluator itself, and `PiProofs.piCircumferenceDirect` is its
  certified `Real` handle.  The cross-fan, stabilization, and reboxing
  remain useful regression views.  `PiProofs.piCertified` continues to use
  the area loop as its preferred representation and records the checked
  alternatives without treating implementation variants as extra score rows.


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
  `CirclePi.powerSeriesArctanOnePiRawAlgorithm` is `4 * arctan.series(1)`, where
  `arctan.series(x) = x - x^3/3 + x^5/5 - ...`.  This is intentionally not a
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
  `PiProofs.piMachin_compute_width_eq` gives the exact width of the one Machin
  evaluator as the sum of its two literal alternating-series widths, and
  `PiProofs.piMachin_compute_width_le_geometric_half` gives the simple public
  bound `20/2^n`.  This rate belongs to the Machin runtime boxes themselves,
  not to a width transported across its equivalence with area pi.
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
  validity theorem `Basel.geometricPiSquaredOverSixRaw_valid`.  The original
  chord-path specialization `Basel.circumferencePiSquaredOverSixRaw` is also
  valid, and `circumferencePiSquaredOverSixRaw_equiv_geometric` proves that
  the two geometric right-hand sides agree by finite nonnegative interval
  multiplication.  The conditional theorem
  `eulerBasel_circumference_iff_geometric` therefore transfers any future
  Basel proof between the direct circumference and area formulations.
- `Basel.eulerBasel_geometricPi` is the remaining constructive theorem
  statement relating these two valid computations.  It is not yet a proved
  equivalence.  Its public mathematical form is the Basel identity
  \(\zeta(2)=\pi^2/6\); a positive-normalization theorem may later expose a
  pi-presentation agreement as a registry corollary, rather than treating the
  squared identity itself as a scoreboard formula.

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
  `ComputableAnalysis/Differential.lean`.  The same examples now inhabit the
  newer interval-valued derivative interface: the exact singleton affine
  quotient is its slope, while
  `FunctionOnInterval.exactRatSquareDerivative` proves that the signed
  quotient error for `x^2` is the step itself and fits the stage precision.
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
