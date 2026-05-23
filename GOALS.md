# Computable Analysis Goalposts

This file is the prose roadmap.  Lean files should contain definitions,
certificates, and proved bridges; broad mathematical milestones live here with
references to the relevant declarations.

## Ground Layer

- Raw reals are interval algorithms `Nat -> QInterval`.  Certification is
  separate: `RealCert` packages a `RealRaw` with the validity proof needed for
  use as a higher-level `Real` representative.  See `RealRaw` and `RealCert`
  in `ComputableAnalysis/Base.lean`.
- `RealRaw.ValidCompute` no longer means “width at stage `n` is at most
  `1/n`. It means: every stage is an ordered interval, later stages are
  nested inside earlier stages, and widths shrink to zero.  Any clean bound
  such as `C/n^r` or `C*rho^n` is evidence for this, not the definition.
  `ComplexRaw.ValidCompute` has the same shape for rectangular boxes.
- `RealRaw` has a single optional `rate` metadata field.  The rate is not a
  second kind of real number: it is either unknown, eventually polynomial, or
  eventually geometric.  See `RealRaw.Rate` in
  `ComputableAnalysis/Base.lean`.
- For concrete algorithms, record public rate information as eventual upper
  bounds, not necessarily exact widths.  For pi, `piLeibnizRate` records width
  `<= 4/n`, while `piMachinRate` records width `<= 20*(1/2)^n`, i.e.
  `20/2^n`.
- Equality of raw representatives is overlap along cofinal increasing stage
  schedules.  This is `RealRaw.Equiv`: there are two schedules `a(n)` and
  `b(n)`, each eventually passing every requested stage, such that the two raw
  intervals compare as `RealRaw.CompareAt.overlap` at stages `a(n)` and `b(n)`
  for every `n`.  Same-stage overlap is the special case using the identity
  schedule, via
  `RealRaw.sameStageOverlap_equiv`.  The project-facing equality notion is
  this raw-level relation.
- The stronger all-stages notion is now formalized as
  `RealRaw.AllStagesOverlap`: every interval from one algorithm compares as
  `overlap` with every interval from the other.  For certified/nested raw algorithms it is also
  equivalent to scheduled `RealRaw.Equiv`; see
  `RealRaw.equiv_iff_allStagesOverlap` in `ComputableAnalysis/RealEquiv.lean`.
- For computation with a higher-level real number, use `Real`: it keeps a
  preferred certified representative for evaluation plus a list of certified
  equivalent alternatives.  The preferred representative should be the best
  available algorithm/rate.  `Real.Named` remains a compatibility alias.
  See `Real.compute`, `Real.rate`, `Real.computeUsing`, and
  `Real.representation_same_real` in `ComputableAnalysis/Core.lean`.
- Complex numbers mirror the same foundation: `ComplexRaw` has optional
  coordinate-rate metadata, and `Complex` keeps a preferred certified raw
  representative with optional equivalent alternatives.  See
  `ComplexRaw.Rate` and `Complex` in `ComputableAnalysis/Complex.lean`.
- Function layers are representation/domain layers.  Real and complex function
  raws carry a domain and pointwise output-rate metadata; the rate may depend
  on the input and its domain proof.

## Continuity Replacement

- Replace pointwise continuity on an interval by interval regularity:
  every small rational subinterval has a computable narrow output interval
  containing all point-values.
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
- Convex derivative: for a convex function, define the right derivative as
  the infimum of right secants `Sec_F(q,q+h)` as `h > 0` tends to zero, and
  the left derivative as the supremum of left secants.  The full two-sided
  derivative exists only where these agree; corners such as `abs` should not
  block the universal one-sided FTC.
- Convex FTC proof step: for each partition cell `[x_i,x_{i+1}]`, convexity
  gives
  `D_+F(x_i) <= Sec_F(x_i,x_{i+1}) <= D_-F(x_{i+1})`.
  Multiplying by the cell width and summing gives Darboux sums around the
  telescoping endpoint difference `F b - F a`.  Monotonicity and completeness
  shrink the Darboux gap.
- Piecewise convexity: if a function switches convexity, split the interval at
  rational breakpoints, apply the exact convex FTC on each piece, and combine
  endpoint equalities by raw-real arithmetic and transitivity.  Do not add a
  separate piecewise theorem unless the examples force a reusable abstraction.
- Formula-identification route: to identify a proposed kernel, prove that it
  lies in the same shrinking enclosures as the pointwise derivative produced
  by secants.  For arctangent, this means proving finite sector-area secant
  inequalities and comparing them with `1/(1+x^2)`.
- Hidden singularities such as `1/(x^2 - 2)` are not handled by an FTC theorem.
  They are handled before calculus by denominator-apartness or
  interval-regularity certificates on the rational interval.

## Inverse Functions

- Main calculus route: construct inverses on intervals where the function is
  interval-regular, monotone, and effectively separated.
  See `InvertibleFunctionOnInterval`, `InRangeRaw`, `InverseRaw.apply`, and
  `HasInverse` in `ComputableAnalysis/Calculus.lean`.
- Proved bridge: a bisection/search construction for every target value gives
  the inverse-function theorem.
  See `InverseBisectionSearch` and `inverse_function_from_bisection_search` in
  `ComputableAnalysis/Calculus.lean`.
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
  algorithm.  This can be specialized to exponential first; a general
  term-by-term differentiation theorem can come later.
- To prove equality of the three exponential representations by calculus
  rather than by ad hoc estimates, prove a constructive uniqueness principle
  for `f' = f` with `f(0) = 1`.  See
  `SolvesSelfDerivativeOnInterval` and `SelfDerivativeInitialValueUnique` in
  `ComputableAnalysis/Differential.lean`.

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

## Iteration-Based Construction Layers

- Alternating series now have a first iteration-style raw layer.  See
  `Series.AlternatingRaw` in `ComputableAnalysis/Series.lean`.
- Proved: if the magnitudes of an alternating series shrink to zero, then the
  intervals between consecutive partial sums shrink to zero.  See
  `Series.AlternatingRaw.intervals_shrink`.
- Next step for alternating series: prove nestedness/enclosure from
  nonnegative decreasing terms, then instantiate Leibniz/arctangent series.

## Pi Representations

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

- Euler's Basel problem now has a computable statement in
  `ComputableAnalysis/Basel.lean`.  `Basel.zetaTwoRaw` is the raw interval
  algorithm for `zeta(2)`: at stage `n`, the lower endpoint is
  `sum_{k=1}^n 1/k^2`, and the upper endpoint adds the rational tail bound
  `1/n`.  This padding is part of the raw algorithm definition; the finite
  telescoping estimate is used to prove nesting:
  `Basel.zetaTwoTerm_le_telescopeStep` proves
  `1/(m+1)^2 <= 1/m - 1/(m+1)`, and
  `Basel.zetaTwoFiniteTail_le_telescoping` proves every finite tail after
  `n` terms is at most `1/n - 1/(n+count)`.  The theorem
  `Basel.zetaTwoInterval_width` proves that the interval width is exactly
  `1/n`, and `Basel.baselSeriesRaw_valid` proves that the Basel-series raw
  algorithm is a valid `RealRaw`.
- The right-hand side is `Basel.piSquaredOverSixRaw pi`, a raw interval
  algorithm for `pi^2/6` from any chosen raw pi representative.  The current
  named geometric version is `Basel.geometricPiSquaredOverSixRaw`, built from
  `CirclePi.areaPiRawAlgorithm`.
- Integer zeta values now have the same certified raw construction:
  `Basel.zetaNatRaw p` computes `zeta(p)` for natural exponents, and
  `Basel.zetaNatRaw_validCompute p hp` proves validity whenever `2 <= p`.
  This uses the elementary comparison `1/k^p <= 1/k^2`, so the same
  telescoping padding `1/n` works for every integer `p >= 2`.  This is the
  clean finite layer beneath the eventual real-argument zeta function.
- The formal Euler statement is
  `Basel.EulerBaselStatement pi := Basel.zetaTwoRaw.Equiv
  (Basel.piSquaredOverSixRaw pi)`.  The geometric-pi specialization is
  `Basel.eulerBasel_geometricPi`; it is currently a proposition, not a proved
  theorem.  Proving it constructively likely needs Euler's sine-product
  argument, Fourier series, or later complex function theory.

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
