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

The finite `sqrt 2` bisection trace now reaches stage 24 with the exact
interval `[11863283/8388608, 23726567/16777216]` and width `1/16777216`.
This extends the isolating-interval evidence for benchmark item 1 without
treating the irrational value as an attained rational endpoint.

**Easy benchmark cluster â€” checked.**  The foundation exposes the rational
triangle inequality through `qabs_add_le`, `qabs_add_le_three`, and
`qabs_sub_le`; the list-level `qabs_ratListSum_le` now supplies the finite
sum form, with append laws for composing finite error lists.  The series layer
now exposes recursive finite arithmetic and geometric sums, including the
general rational progression identities `Series.arithmeticProgressionSum_eq`
and `Series.arithmeticProgressionSum_constant`/`Series.arithmeticProgressionSum_le_succ`/
`Series.arithmeticProgressionSum_le_of_le`/
`Series.arithmeticProgressionSum_nonneg`/`Series.arithmeticProgressionSum_pos`,
with exact identities `Series.arithmeticSum_eq`,
`Series.arithmeticSum_nonneg`/`Series.arithmeticSum_le_succ`,
`Series.arithmeticSum_pos`,
`Series.arithmeticSum_le_of_le`, `Series.arithmeticSum_reaches`, and
`Series.arithmeticSum_reaches_later`,
`Series.geometricSum_one`, `Series.geometricSum_zero_ratio`,
`Series.geometricSum_mul_sub`, and
`Series.geometricSum_tail_eq`, together with
`Series.geometricSum_le_inv_one_sub`,
`Series.geometricSum_tail_nonneg`,
`Series.geometricSum_tail_pos`,
`Series.geometricSum_tail_le_one`,
`Series.geometricSum_tail_lt_one`,
`Series.half_pow_eq_one_div_nat_two_pow`,
`Series.half_pow_le_one_div_succ`, and
`Series.geometricSum_half_tail_le_one_div_succ`, together with the comparison
theorems `Series.pow_le_half_pow` and
`Series.geometricSum_tail_le_one_div_succ_of_le_half`,
and `Series.geometricHalfRaw`/`Series.geometricHalfRaw_valid` now package
the ratio-half geometric series as an ordered, nested `RealRaw` with an
explicit (2/(n+1)) width modulus.  The general
`Series.geometricRaw` package extends this to every rational ratio
`0 <= r <= 1/2`, with exact value `1/(1-r)` and the same explicit width
schedule,
and `Series.geometricHalfRaw_equiv_two` proves that this raw series represents
the exact rational sum 2.
`Series.geometricSum_nonneg`/`Series.geometricSum_le_succ`,
`Series.geometricSum_pos`,
`Series.geometricSum_eq`; the finite binomial
identity is already exposed as
`ExpProofs.euler_binomial_prefix_nat_expansion`.  These cover the finite
certificate core of benchmark items 91, 68, 66, and 44; infinite convergence
remains a separate obligation and is not claimed by these finite theorems.
The worked identities `Series.binomial_square` and `Series.binomial_cube` give
the first quadratic and cubic instances of the finite binomial theorem in the
Infinite Series chapter.
The named finite witness now also checks the stage-10 expansion
`(2+1)^10 = 59049` and the independent stage-8 expansion
`(2+3)^8 = 390625`, extending the exact rational checkpoints for item 44.
The rational term and partial-sum constructors, their interior and boundary
recurrences, and `Series.binomialSum_eq_pow` now expose the full finite
binomial identity over the rationals. `Series.binomialSum_eq_pow_of_reached`
transports that identity to every later accumulator stage after the last
nonzero coefficient. Infinite convergence remains a separate obligation.
For benchmark item 14, `DirichletSeries.zetaTwoTerm_le_telescopeStep` and
`DirichletSeries.zetaTwoFiniteTail_le_telescoping` expose the finite reciprocal-
square telescoping and tail budget used by the certified Basel-series
representation.  The public recurrences `zetaTwoPartial_succ` and
`zetaTwoPartial_nonneg`,
`zetaTwoTerm_pos` and `zetaTwoPartial_lt_succ`,
`zetaTwoFiniteTail_succ`, together with `zetaTwoFiniteTail_nonneg`, expose the
finite accumulator and sign certificates.  The strict-tail theorem
`zetaTwoFiniteTail_pos` makes positive width explicit for every nonempty tail.
The monotonicity lemmas
`zetaTwoPartial_le_succ` and `zetaTwoPartial_le_of_le`, plus the coarse tail
bound `zetaTwoFiniteTail_le_tailBound`, expose the interval-order data used by
the representation.  The equality with pi^2/6 remains open.  The derived
`zetaTwoFiniteTail_lt_one_div` gives the strict finite tail width used by the
interval representation, and `zetaTwoInterval_width_le_one_div` exposes the
corresponding bound directly at the interval level.  The interval-level
certificate `zetaTwoInterval_width_pos` gives strict nondegeneracy at positive
stages, while `zetaTwoInterval_lo_nonneg` and `zetaTwoInterval_hi_pos` expose
the endpoint signs.  The interval-level certificates `zetaTwoInterval_nested` and
`zetaTwoRaw_validCompute` now expose
the complete ordered, shrinking finite representation boundary as well.
The public selector `zetaTwoInterval_reaches_of_positive_tolerance` now turns
the denominator budget into an explicit finite stage for every positive
rational width request.
The project-facing bridge `Basel.baselSeriesRaw_reaches_of_positive_tolerance`
exposes the same stage selector directly on the public Basel raw evaluator.
Thus the admitted item-14 core has an explicit potential-infinity precision
interface at its boundary, while the completed Basel identity remains open.
The wrappers `Basel.eulerBasel_geometric_iff_allStagesOverlap` and
`Basel.eulerBasel_circumference_iff_allStagesOverlap` now express the remaining
Basel theorem as an all-finite-stages overlap obligation between the two valid
raw algorithms. This is the project-native target for the future analytic
proof, not a hidden appeal to classical completeness.
The exact decomposition
`DirichletSeries.zetaTwoPartial_add_finiteTail_eq` now exposes every later
finite partial sum as its earlier partial sum plus the explicit intervening
tail. This makes the finite accumulator/tail interface compositional while
leaving the classical Basel equality unresolved.
The strict companion
`DirichletSeries.zetaTwoPartial_add_nonempty_finiteTail_lt_interval_hi` now
places every genuinely later partial sum strictly below the earlier padded
endpoint, preserving the same finite rational boundary.
The new `DirichletSeries.zetaTwoFiniteTail_add` theorem gives an exact
concatenation law for two finite tail blocks, shifting the second block to
the correct denominator range. This supports compositional finite error
accounting while leaving the classical Basel equality unresolved.
The new `DirichletSeries.zetaTwoPartial_le_two` gives a uniform finite bound
for every reciprocal-square partial sum, transported from the stage-one
padded endpoint. This strengthens the Basel certificate's boundedness
interface without identifying the completed sum with pi^2/6.
The convex-calculus interface now also exports
`leftDerivativeAt_mono`, the dual one-sided derivative monotonicity theorem:
the supplied least upper bound at a later point dominates every earlier left
secant through the finite bridge secant. It complements
`rightDerivativeAt_mono` without constructing a supremum or a completed
real-valued limit.
The geometric arctangent layer now exports the finite quotient bridge
`arctanIntegralRectangleCompute_tangentChart_quotient_contains` and its
kernel form `arctanIntegralRectangleCompute_tangentChart_quotient_kernel_contains`.
For positive rational steps on [0,1], the latter bounds the rectangle
difference quotient below by `integralKernel x - (h + h^2)` and above by
`integralKernel x`. This is the next finite certificate toward item 15's
derivative/FTC bridge, not a classical limit claim.
The companion `leftDerivativeAt_le_rightDerivativeAt` now formalizes the
convex-corner inequality: every left secant is a lower bound for every right
secant, so the supplied left derivative lies below the supplied right
derivative. This preserves the project's explicit one-sided treatment of
corners such as `abs x`.
The companion `DirichletSeries.zetaTwoTerm_antitone` and
`DirichletSeries.zetaTwoFiniteTail_le_firstTerm_block` lemmas expose the
monotone-term and rectangular block bounds used by finite error schedules.
The stage-10000 enclosure
`DirichletSeries.zetaTwoInterval_contains_basel_decimal_10000` tightens the
earlier stage-1000 decimal certificate to the rational target `1.6449340668`.
The higher-stage certificate
`DirichletSeries.zetaTwoInterval_contains_basel_decimal_100000` contains the
same target at stage 100,000, strengthening the finite evidence while leaving
the Basel identity open.
The worked `FiniteBaselExample` now packages the tolerance `1/1000` at stage
`1001` and checks that stage `2000` remains inside its rational enclosure.
The same finite certificate also contains the stage-100000 reciprocal-square
interval while retaining the `1/1000` width budget.
This makes the item-14 potential-infinity schedule executable as a named
certificate, without asserting the completed Basel sum.
The high-precision companion repeats the construction at width `1/100000`,
with stage `100001` and a verified later-stage containment at `200000`.
Euler's completed identity remains deferred.
The integer-exponent family now has matching executable stage selectors
`DirichletSeries.zetaNatInterval_width_le_of_denominator_budget` and
`DirichletSeries.zetaNatInterval_reaches_of_positive_tolerance`: every fixed
exponent `p >= 2` gets a rational interval stage for any requested positive
tolerance, using the same potential-infinity denominator schedule. This is a
finite strengthening of the Dirichlet-series boundary, not a claim that a
completed zeta value has been constructed.
The propagation certificates
`DirichletSeries.zetaNatInterval_later_contained_in_target_of_budget` and
`DirichletSeries.zetaNatPartial_later_in_target_of_budget` now transport an
earlier target enclosure to every later stage, including its explicit width
budget. This supplies the same compositional target interface for the
integer-exponent family without introducing a completed infinite sum.
The matching generic finite-tail accumulator
`DirichletSeries.zetaNatFiniteTail` and decomposition
`DirichletSeries.zetaNatPartial_add_finiteTail_eq` now make that family
compositional at every fixed exponent, not only at `p = 2`.  The comparison
theorems `DirichletSeries.zetaNatFiniteTail_le_zetaTwoFiniteTail` and
`DirichletSeries.zetaNatFiniteTail_le_tailBound` transfer the explicit
reciprocal-square tail budget to every `p >= 2`.
The endpoint bridge
`DirichletSeries.zetaNatPartial_add_finiteTail_le_interval_hi` then places
each later finite partial sum directly below the corresponding generic
interval upper endpoint.
The paired enclosure theorem
`DirichletSeries.zetaNatInterval_contains_partial_add_finiteTail` records both
endpoints explicitly for each finite tail-extended partial sum.
The finite triangular telescoping identity
`Series.triangularTelescopingTerm_eq_reciprocal` and
`Series.triangularTelescopingSum_eq` now cover benchmark item 42 at the finite
certificate level.  The explicit remainder
`Series.triangularTelescopingSum_tail_eq` and strict bound
`Series.triangularTelescopingSum_lt_two` expose the finite convergence
boundary.  The new
`Series.triangularTelescopingRaw` packages the same sums as a valid raw-real
interval algorithm, with exact value 2 certified by
`Series.triangularTelescopingRaw_equiv_two`. The public selector
`Series.triangularTelescopingRaw_reaches_of_positive_tolerance` now exposes a
finite stage for every requested positive rational width.
The worked `FiniteTriangularExample` instantiates stage four with exact sum
`8/5` and tail `2/5`, making the reciprocal-triangular boundary directly
checkable as a named finite witness.
The same witness now includes stage eight: the exact sum is `16/9` and the
remaining finite tail is `2/9`, giving a second explicit checkpoint for item
42 while preserving the potential-infinity interpretation.
It now also includes stage 16: the exact sum is `32/17` and the remaining
tail is `2/17`, extending the same finite error schedule to a third checkpoint.
It now also includes stage 32: the exact sum is `64/33` and the remaining
tail is `2/33`, extending the same finite error schedule once more.
It now also includes stage 64: the exact sum is `128/65` and the remaining
tail is `2/65`, providing the next explicit rational precision checkpoint
while preserving the potential-infinity interpretation.
The alternating-series layer now also proves even partial sums are monotone,
odd partial sums are antitone, and the endpoint intervals are explicitly
nested via `Series.AlternatingRaw.intervals_nested`; this supplies the order
half of the generic alternating interval construction used by the Leibniz
route.  `Series.AlternatingRaw.toRealRaw` and
`Series.AlternatingRaw.toRealRaw_valid` now package that construction directly
as a valid `RealRaw`.  The concrete
`Series.AlternatingRaw.leibnizAlternatingRaw` instance supplies the
nonnegative, decreasing, shrinking term certificate for (1/(2n+1)), the
finite alternating-series core of benchmark item 26.
The exact square inequality `am_gm_square_bound` covers the rational core of
benchmark item 38, and `sqrtRaw_le_am_gm` now lifts it to the certified
nonnegative square-root representation.
Its normalized form `am_gm_rational_half` now exposes the direct rational
inequality `a*b <= ((a+b)/2)^2` used by later certificate estimates.
The equality condition is also checked by
`am_gm_rational_half_eq_iff`, namely equality exactly when `a=b`.  For the
represented square-root branch, `sqrtRaw_am_gm_eq_of_eq` certifies the matching
equality when the two inputs coincide, and `sqrtRaw_am_gm_eq_iff` proves that
this is the only equality case.  The paired finite certificate `am_gm_four`
extends the same rational boundary to four nonnegative inputs:
  `a*b*c*d <= ((a+b+c+d)/4)^4`, without invoking a general real-valued AM--GM
  theorem.
The worked four-variable checkpoints now verify equality for `(3,3,3,3)` and
strictness for `(2,3,4,5)`, exercising the same finite interface on both
branches.
The new `DyadicAMGM` binary-tree certificate extends this to every finite
  power-of-two number of nonnegative rational leaves:
  `product_le_average_pow` proves the exact (2^k)-term bound by recursive
  pairing.  It remains a finite rational theorem, not arbitrary-(n) AM--GM.
The worked `dyadicAMGMExample` instantiates the depth-two tree with leaves
`1,2,3,4`, checks sum `10` and product `24`, and invokes the generic bound.
The same worked layer now includes a depth-three tree with leaves `1` through
`8`, sum `36`, product `40320`, and its exact eight-term dyadic AM--GM bound.
The depth-four witness now uses leaves `1` through `16`, checks sum `136`,
product `20922789888000`, and its exact sixteen-term dyadic AM--GM bound.
The generic `consecutiveDyadic` constructor now supplies a depth-five witness
with leaves `1` through `32`, sum `528`, product `263130836933693530167218012160000000`,
and the corresponding thirty-two-term AM--GM bound.
The two-coordinate rational inequality `cauchy_schwarz_2d` covers the finite
certificate core of benchmark item 78 without expanding the project's scope
to functional analysis.  Its equality characterization
`cauchy_schwarz_2d_eq_iff` is also checked: equality holds exactly when
`a*d=b*c`.
The three-coordinate extension `cauchy_schwarz_3d` is now checked by an
explicit sum of three rational squares.  It deepens the finite inequality
support for item 78 while remaining entirely coordinate-level and avoiding
any functional-analysis infrastructure.
Its equality characterization `cauchy_schwarz_3d_eq_iff` is also checked:
equality is equivalent to vanishing of the three rational (2\times2) minors
`a*y-b*x`, `a*z-c*x`, and `b*z-c*y`.
The four-coordinate inequality `cauchy_schwarz_4d` is now checked by the
corresponding six-minor rational sum-of-squares certificate, further extending
the same finite support without introducing an inner-product space.  Its
equality characterization `cauchy_schwarz_4d_eq_iff` records exactly the six
vanishing rational minors.
The five-coordinate extension `cauchy_schwarz_5d` adds the corresponding ten
minor sum-of-squares certificate, still entirely rational and finite.
The six-coordinate extension `cauchy_schwarz_6d` adds the corresponding
fifteen-minor certificate, extending the same finite rational support without
introducing a general vector-space layer.
The companion `cauchy_schwarz_6d_eq_of_minors` records the corresponding
fifteen-minor equality witness explicitly.
The interval primitive `QInterval.intersection_ordered_of_overlaps` likewise
proves that an explicit intersection of two ordered overlapping rational
intervals is ordered, preserving the project's data-first treatment of finite
common enclosures.
Its equality form `cauchy_schwarz_5d_eq_iff` records the ten vanishing minors
as the exact finite equality condition.
The generic executable finite evaluator `Series.powerSum`, with its
`powerSum_succ` recurrence, `powerSum_nonneg`, `powerSum_le_succ`, and
`powerSum_le_of_le` certificates, now covers the
finite recursive core of benchmark item 77 for every fixed exponent.  The
strict certificate `Series.powerSum_pos` additionally records positivity for
positive exponents and sums of length greater than one.  The
bridge lemmas `Series.powerSum_zero_exponent` and
`Series.powerSum_one_exponent` recover the counting sum and the existing
arithmetic-sum evaluator from this common definition, while
`Series.powerSum_two_exponent` through `Series.powerSum_eight_exponent`
identify the generic evaluator with the named low-degree power sums.  The
closed forms `Series.squareSum_eq`, `Series.cubeSum_eq`,
`Series.fourthPowerSum_eq`, and
`Series.fifthPowerSum_eq`/`Series.sixthPowerSum_eq`/`Series.seventhPowerSum_eq`
remain the checked low-degree formulas. The new
`Series.powerSum_four_closed_form` exposes the fourth-power formula directly
through the generic executable evaluator. The matching
`Series.powerSum_five_closed_form`, `Series.powerSum_six_closed_form`, and
`Series.powerSum_eight_finite_bridge` now exposes the eighth-power finite
accumulator through the generic evaluator.  The explicit eighth-power
polynomial identity is now checked as `Series.eighthPowerSum_eq` and
`Series.powerSum_eight_closed_form`.
low-degree family; a general Faulhaber formula remains open.
The exact rational identities `RationalCircle.pythagoreanTriple_identity` and
`RationalCircle.pythagoreanTriple_positive` cover the polynomial and positive
rational core of benchmark item 23; primitive-integral classification remains
separate.
The coordinate identities `RationalCircle.rightTriangle_axis_pythagorean` and
`RationalCircle.rightTriangle_pythagorean` cover the rational orthogonality
core of benchmark item 4; general Euclidean-space formulations remain outside
the current boundary.
The worked `rightTriangle_rotated_three_four_six_eight_certificate` instantiates
the same identity on the non-axis legs `(3,4)` and `(-8,6)`: their dot product
is zero, their squared lengths are `25` and `100`, and the squared hypotenuse
is `125`.
The symmetry and base-length identities
`RationalCircle.isosceles_axis_symmetry` and
`RationalCircle.isosceles_base_normSq` are the rational-coordinate core of
benchmark item 65; equality of the associated angles remains outside the
current boundary.
The companion `isosceles_axis_pythagorean` identifies the equal-leg square as
the sum of the squared axis and half-base segments, making the perpendicular
median calculation explicit in rational coordinates.
The worked isosceles certificate now includes a third rational instance with
height/half-base `(7,24)`: both legs have squared length `625`, the axis is
orthogonal to a leg, and the base has squared length `2304`.  The equality of
the associated geometric angles remains a separate deferred bridge.
The existing squared-coordinate law of cosines
`RationalCircle.Stage.segmentNormSq_law_of_cosines` covers the exact rational
geometry core of benchmark item 94; the accompanying equilateral specialization
`RationalCircle.Stage.dot_eq_half_of_unit_equilateral` is already formalized,
while normalized-angle semantics remain a separate layer.
The worked `finiteLawOfCosines_unit_orthogonal_certificate` adds a second
coordinate checkpoint: the unit rational points `(3/5,4/5)` and `(-4/5,3/5)`
have dot product `0` and squared separation `2`, with the law-of-cosines
identity checked by exact rational computation.
The same worked module now checks the antipodal pair `(3/5,4/5)` and
`(-3/5,-4/5)`, with dot product `-1` and squared separation `4`, providing a
non-orthogonal finite checkpoint for item 94.
It also checks the coordinate pair `(3,0)` and `(0,4)`: squared norms `9` and
`16`, dot product `0`, and squared separation `25`, making the `3-4-5` law of
cosines specialization explicit.
The Heron witness now adds the `13-14-15` triangle with vertices
`(0,0),(14,0),(5,12)`: twice-area `168`, Heron product `7056`, and finite
square-root raw equivalent to area `84`.
The exact rational identities `RationalCircle.heron_squared_identity` and
`RationalCircle.heron_product_nonneg` cover the squared algebraic and
nonnegative rational core of benchmark item 57.  The new
`RationalCircle.heronAreaRaw` packages the nonnegative square-root area as a
valid raw-real output with an explicit square-root specification.  The concrete certificate
`RationalCircle.heron_three_four_five` evaluates the Heron product for the
3-4-5 triangle to 36 (squared area 36), while
`RationalCircle.heron_three_four_five_area_witness` exposes the exact rational
area witness 6 without claiming a general square-root construction, and
`RationalCircle.heron_three_four_five_area_raw_equiv_six` transports the
computed Heron square-root raw directly to that witness, while
`RationalCircle.heron_three_four_five_strict_pos` records nondegeneracy.
The new `FiniteHeronExample` adds a non-3-4-5 instance: the rational triangle
with vertices `(-3,0)`, `(3,0)`, and `(0,4)` has sides `6,5,5`, area `12`,
and Heron product `144`; Lean transports its finite square-root raw to `12`.
The algebraic bridge `sqrt_thirty_six_eq_six` now identifies the projectâ€™s
certified square-root representation with that same rational witness.
The exact rational identity
`RationalCircle.ptolemy_oriented_chord_numerator` is the common-denominator
oriented-chord core of benchmark item 95; the full chord-length statement
remains open. `RationalCircle.ptolemy_squared_coordinate_certificate` now
adds a square-root-free squared shadow for the concrete cyclic quadrilateral,
including an explicit rational witness for the four-side cross-term.
The second finite Ptolemy example uses the ordered parameters
`(0,5/12,3/4,4/3)`. Its six squared chord lengths are rational squares with
length witnesses `10/13, 32/65, 14/25, 8/5, 6/5, 66/65`, and Lean checks the
corresponding rational Ptolemy identity independently.  The new
`secondPtolemy_length_certificate` also transports all six witnesses through
the raw square-root length interface.
The rational power-of-a-point identity
`RationalCircle.horizontalChord_power_identity` covers the directed-segment
core of benchmark item 55. The new
`RationalCircle.horizontalChord_power_nonneg_of_outside` supplies the finite
sign certificate when the external point is outside the chord interval, and
`RationalCircle.horizontalChord_power_neg_of_inside` supplies the strict
interior sign. `RationalCircle.horizontalChordPowerSqrtRaw` and
`RationalCircle.horizontalChordPowerSqrtRaw_valid` now lift the nonnegative
outside product to a certified square-root raw algorithm; its Euclidean-length
interpretation remains open. `RationalCircle.horizontalChordPowerSqrtRaw_spec`
also exposes the square-root specification for later composition.
`RationalCircle.horizontalChordPowerSqrtRaw_equiv_of_square` now identifies
that output with the nonnegative rational representative whenever a supplied
rational square witness exists. The concrete
`horizontalChordPowerSqrtRaw_equiv_four_fifths` specialization checks the
outside-point instance (16/25mapsto4/5) by exact rational arithmetic.
The companion `FiniteChordPowerExample` checks the second rational instance
with radius `4/5`: the external point `1` gives product `9/25`, whose certified
square-root output is `3/5`.
It now also records the interior point `t=1/2`, where the directed product is
`-39/100`; this concrete sign witness keeps item 55's directed-segment core
distinct from the later unsigned-length interpretation.

**Additional computable-analysis target â€” Gaussian route to (n)-ball volume.**
The `FiniteNBallVolume` module adds a literal finite two-dimensional
product-sum evaluator.  The reusable theorem
`finiteProductSum2D_factorized` proves the separable-kernel identity for
arbitrary finite sample lists; the concrete sample-grid calculation is only a
regression witness, not a standalone finite-sum milestone.  This is the
rectangular algebra needed before attaching cell widths and error schedules to
a genuine multiple-integral construction.  Its weighted companion
`finiteProductIntegralSum2D` attaches rational cell widths and
`finiteProductIntegralSum2D_factorized` proves the corresponding weighted
rectangle factorization.  The module also records the exact finite product law for (n) independent
one-dimensional Gaussian approximants and the rational coefficient recurrence
for the (n)-ball volume model.  The one-dimensional Gaussian integral, its
square-to-Ï€ bridge, radial shell estimates, and unbounded tails remain explicit
future interfaces rather than being smuggled in as Lebesgue integration.
The first low-dimensional recurrence cases are now explicit: the disk and
3-ball identities are joined by `nBallVolumeModel_four`, giving
`(1/2) * piApprox^2 * radius^4`, and `nBallVolumeModel_five`, giving
`(8/15) * piApprox^2 * radius^5`. These remain finite recurrence identities;
the Gaussian integral and square-to-Ï€ bridge are separate targets.
The next parity pair is now checked as well: `nBallVolumeModel_six` gives
`(1/6) * piApprox^3 * radius^6`, while `nBallVolumeModel_seven` gives
`(16/105) * piApprox^3 * radius^7`. The Gaussian integral and radial
shell/tail bridge remain separate computable targets.
The following pair is explicit too: `nBallVolumeModel_eight` gives
`(1/24) * piApprox^4 * radius^8`, while `nBallVolumeModel_nine` gives
`(32/945) * piApprox^4 * radius^9`. These are still finite recurrence
checkpoints, not a claim about Gaussian integration or unbounded volume.
The finite recurrence now reaches dimensions ten and eleven as well, with
`nBallVolumeModel_ten` and `nBallVolumeModel_eleven`, plus exact `355/113`
stage witnesses. These remain finite rational models; the Gaussian square-
to-Ï€ bridge and any unbounded volume theorem are still separate targets.
It now reaches dimensions twelve and thirteen as well, with exact recurrence
identities and `355/113` stage witnesses. The extension remains an algebraic
finite model, not a claim that the Gaussian integral or unbounded volume has
been constructed.
The homogeneity theorem `nBallVolumeModel_scale` now records the expected
radius-scaling law exactly: scaling the radius by `s` scales the finite model
by `s^n`. This is the algebraic volume property needed before any analytic
Gaussian or radial-shell bridge is introduced.
The `FiniteNBallVolume` and `FiniteGaussianIntegral` modules are now included
in the umbrella `ComputableAnalysis` import. Their finite product, recurrence,
and bounded Gaussian-prefix certificates are therefore available through the
public project build; no Lebesgue measure or completed improper integral has
been added.

The companion `FiniteGaussianIntegral` module now supplies the bounded analytic
prefix: it integrates the even Taylor polynomial for `exp (-x^2)` term by term
over `[-1,1]`.  The four-term and six-term prefixes are exactly `52/35` and
`31049/20790`.  This is the first concrete Gaussian integral object in the
project; the full-line tail and square-to-Ï€ theorem remain the next bridges.
The stage-eight prefix is additionally `1009219/675675`, and the exact
stage-six-minus-stage-four refinement gap is `23/2970`.
The same file adds the finite reciprocal-square tail partial sum at cutoff `1`:
four terms give `1669/3600 < 1`.  This is deliberately a transport layer,
not yet a Gaussian claim; it awaits the pointwise proof
`exp (-x^2) â‰¤ 1/x^2` for `x â‰¥ 1`.
The reciprocal-square prefix now also reaches six terms (`90281/176400`) and
eight terms (`3427741/6350400`), with the latter still below `1`.
The existing tail-enclosed exponential evaluator also now checks the concrete
point `x=2`: its stage-20 upper endpoint for `exp (-4)` is at most `1/4`.
The same stage also verifies `exp (-9) â‰¤ 1/9` and `exp (-16) â‰¤ 1/16`, packaged
as `gaussianTailPointLadder_stage_twenty`.
The reusable `gaussianTailBoxUpper` interface packages each certified upper
endpoint as a function of the rational tail point and stage, with the same
three-point ladder exported by `gaussianTailBoxUpper_stage_twenty_ladder`.
The finite transport theorem
`gaussianTailBoxUpper_stage_twenty_three_point_sum` sums those three certified
upper boxes into the rational tail budget `61/144`.
The seven-point ladder now extends the stage-20 checks through `x=5` and uses
stage 100 for `x=6,7,8`, where the tighter evaluator precision is needed.
`gaussianTailBoxUpper_stage_twenty_eight_point_sum` packages their combined
rational bound. This lengthens the finite tail evidence while the
general inequality `exp(-x^2) â‰¤ 1/x^2` and the completed Gaussian integral
remain separate bridges.
The finite (n)-ball recurrence now exposes its first geometric cases:
`nBallVolumeModel_two` gives the disk model (pi r^2), and
`nBallVolumeModel_three` gives the 3-ball model ((4/3)pi r^3), with the
symbol `piApprox` still an explicit rational approximation rather than a
completed real constant.
The ladder now includes `x=5`, with `exp (-25) â‰¤ 1/25`; the four-point sum is
bounded by `1669/3600`, exactly matching the reciprocal-square tail prefix.
The finite ladder now extends to `x=9` and `x=10` at exponential stage 200,
with upper boxes bounded by `1/81` and `1/100`; their combined budget is
`181/8100`. This remains finite tail evidence, not the general inequality
`exp(-x^2) â‰¤ 1/x^2` or a completed full-line Gaussian integral.
The reusable `PiProofs.pointSegmentLengthRaw` interface now applies the same
certified square-root algorithm to any rational-coordinate squared distance,
with validity and `SqrtRawSpec` theorems for later Ptolemy and polygonal-length
work. The full Euclidean Ptolemy identity remains open.
The finite Ptolemy length certificate now closes that gap for one concrete
rational cyclic quadrilateral: all six raw chord lengths are equivalent to
explicit rational witnesses satisfying Ptolemyâ€™s identity. The general
Euclidean theorem remains outside the current boundary.
The checked rational unit-circle group law and stereographic chart addition
formulas in `RationalCircle.Trigonometry` are the finite geometric core of
benchmark item 17; the represented complex-exponential bridge remains open.
The executable point-power package `RationalCircle.Trigonometry.pointPow`,
with `pointPow_add` and `pointPow_normSq`, now supplies the corresponding
finite de Moivre-style power core: powers compose by exponent addition and
preserve unit norm; `pointPow_normSq_of_unit` exposes that final unit-circle
conclusion directly. The product-power law `pointPow_mul` now also checks
the finite identity `(P*Q)^n = P^n*Q^n`.
The explicit `pointPow_three` identity adds the first nontrivial odd-power
coordinate formula, (P^3=(x^3-3xy^2,\;3x^2y-y^3)), as a finite rational
triple-angle shadow of de Moivre's law.
The new `FiniteDeMoivreExample` module makes item 17 concrete at the rational
point `(3/5,4/5)`: its exec^;Û¾í¢G§²ÚîÆ­yÕ±åÍ¥Ì¹½¹…Ù•Q•ÉÑ¥™¥…Ñ”¹Ñ½•É¥Ù…Ñ¥Ù•	½Õ¹‘Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹…Ù•Q•ÉÑ¥™¥…Ñ”¹•ÅÕ¥Ù}•¹‘Á½¥¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹½¹ÍÑÉÕÑ¥½¹½É}½™}‘•É¥Ù…Ñ¥Ù•	½Õ¹‘Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}‘•É¥Ù…Ñ¥Ù•	½Õ¹‘Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}‘•É¥Ù…Ñ¥Ù•	½Õ¹‘Q}•¹‘Á½¥¹ÑÉ••µ•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}‘•É¥Ù…Ñ¥Ù•	½Õ¹‘Q}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹•¹•É…±•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}‘•É¥Ù…Ñ¥Ù•	½Õ¹‘Q}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹½¹ÍÑÉÕÑ¥½¹½É}½™}…¹‘¥‘…Ñ••É¥Ù…Ñ¥Ù•Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}…¹‘¥‘…Ñ••É¥Ù…Ñ¥Ù•Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}…¹‘¥‘…Ñ••É¥Ù…Ñ¥Ù•Q}•¹‘Á½¥¹ÑÉ••µ•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}…¹‘¥‘…Ñ••É¥Ù…Ñ¥Ù•Q}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹•¹•É…±•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}…¹‘¥‘…Ñ••É¥Ù…Ñ¥Ù•Q}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹½¹ÍÑÉÕÑ¥½¹½É}½™}ÕÉÙ…ÑÕÉ•Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}ÕÉÙ…ÑÕÉ•Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}ÕÉÙ…ÑÕÉ•Q}•¹‘Á½¥¹ÑÉ••µ•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}ÕÉÙ…ÑÕÉ•Q}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹•¹•É…±•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}ÕÉÙ…ÑÕÉ•Q}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹½¹ÍÑÉÕÑ¥½¹½É}½™}½¹Ù•áQ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}½¹Ù•áQ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}½¹Ù•áQ}•¹‘Á½¥¹ÑÉ••µ•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}½¹Ù•áQ}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹•¹•É…±•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}½¹Ù•áQ}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹½¹ÍÑÉÕÑ¥½¹½É}½™}½¹…Ù•Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}½¹…Ù•Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}½¹…Ù•Q}•¹‘Á½¥¹ÑÉ••µ•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹‘•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}½¹…Ù•Q}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%¹Ñ•É…°¹•¹•É…±•™¥¹¥Ñ•%‘•¹Ñ¥Ñå½É}½™}½¹…Ù•Q}ÍÑ…•M¡•‘Õ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹Ù•áQ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹…Ù•Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•1•™ÑMÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”á}±•}¥¹Ñ•É…±}Ù…±Õ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ÄØ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ÄÙ}±•}¥¹Ñ•É…±}Ù…±Õ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ÌÈ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ÌÉ}±•}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ØÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ØÑ}±•}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ÄÈà)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ÄÈá}±•}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ÈÔØ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Í•áÑ¥•É¥Ù…Ñ¥Ù•1•™ÑMÕµ}ÍÑ…”ÈÔÙ}±•}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•I¥¡ÑMÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•1•™ÑMÕµ}•Ä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•1•™ÑMÕµ}•ÉÉ½É}•Ä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•1•™ÑMÕµ}•ÉÉ½É}¹½¹¹•œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•1•™ÑMÕµ}•ÉÉ½É}±•}Ñ¡É••}¡…±Ù•Í}‘¥Ø)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•I¥¡ÑMÕµ}•Ä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•I¥¡ÑMÕµ}•ÉÉ½É}•Ä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•I¥¡ÑMÕµ}•ÉÉ½É}¹½¹¹•œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•1•™ÑMÕµ}±•}½¹•}±•}É¥¡ÑMÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q¹Õ‰••É¥Ù…Ñ¥Ù•1•™ÑMÕµ}É¥¡ÑMÕµ}…Á}±•}Ñ¡É••}‘¥Ø)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹Ù•áQ•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹Ù•áQ•ÉÑ¥™¥…Ñ”¹Ñ½ÕÉÙ…ÑÕÉ•Q•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹Ù•áQ•ÉÑ¥™¥…Ñ”¹Ñ½•É¥Ù…Ñ¥Ù•	½Õ¹‘Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹Ù•áQ•ÉÑ¥™¥…Ñ”¹•ÅÕ¥Ù}•¹‘Á½¥¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹…Ù•Q•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹…Ù•Q•ÉÑ¥™¥…Ñ”¹Ñ½ÕÉÙ…ÑÕÉ•Q•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹…Ù•Q•ÉÑ¥™¥…Ñ”¹Ñ½•É¥Ù…Ñ¥Ù•	½Õ¹‘Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹…Ù•Q•ÉÑ¥™¥…Ñ”¹•ÅÕ¥Ù}•¹‘Á½¥¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹Ù•áQ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½¹…Ù•Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Q…å±½È¹%Ñ•É…Ñ•‘Q¡…¥¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹¥¹Ñ•É…Ñ•‘Q…å±½ÉAÉ•™¥á}•¹‘Á½¥¹Ñ¥™™•É•¹•}ÍÕŒ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹¥¹Ñ•É…Ñ•‘Q…å±½ÉAÉ•™¥á}¡…Í•É¥Ù…Ñ¥Ù•=¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹Ñ…å±½ÉAÉ•™¥á}ÍÕŒ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹Ñ…å±½ÉAÉ•™¥áM¡¥™Ñ}ÍÕ}•Å}½™}½•™™¥¥•¹ÑM¡¥™Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹Ñ…å±½ÉAÉ•™¥á}¡…Í•É¥Ù…Ñ¥Ù•=¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹Ñ…å±½ÉAÉ•™¥áÑ}¡…Í•É¥Ù…Ñ¥Ù•=¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹Í¥¹•Q…å±½ÉAÉ•™¥á}¡…Í•É¥Ù…Ñ¥Ù•=¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹½Í¥¹•Q…å±½ÉAÉ•™¥á}¡…Í•É¥Ù…Ñ¥Ù•=¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹•áÁQ…å±½ÉEÕ…‘É…Ñ¥}¡…Í•É¥Ù…Ñ¥Ù•=¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•A½±å¹½µ¥…°¹•áÁQ…å±½ÉAÉ•™¥á}•¹‘Á½¥¹Ñ¥™™•É•¹•}ÍÕŒ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Q…å±½È¹ÉÑ…¹-•É¹•°¹™¥¹¥Ñ•I•µ…¥¹‘•ÉI½ÕÑ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Q…å±½È¹ÉÑ…¹-•É¹•°¹™¥¹¥Ñ•}É•µ…¥¹‘•É}•ÉÉ½É}‰Õ‘•Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥ÉÍÑe•…É…±Õ±ÕÌ¹…ÉÑ…¹-•É¹•±}•ÉÉ½É}‰½à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±ä¹½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹%Í½µÁÕÑ…‰±•I½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…‘É…Ñ¥A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…‘É…Ñ¥}±•™Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…‘É…Ñ¥}É¥¡Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…‘É…Ñ¥}¡…Í}½µÁÕÑ…‰±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘Õ‰¥A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘Õ‰¥A½±å¹½µ¥…±}•Ù…±}•Å}ÁÉ½‘ÕÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘Õ‰¥A½±å¹½µ¥…±}•Ù…±}•Å}é•É½}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘Õ‰¥A½±å¹½µ¥…±}¡…Íá…ÑI½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘Õ‰¥}±•™Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘Õ‰¥}µ¥‘‘±•}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘Õ‰¥}É¥¡Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘Õ‰¥}¡…Í}½µÁÕÑ…‰±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥A½±å¹½µ¥…±}•Ù…±}•Å}ÁÉ½‘ÕÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥A½±å¹½µ¥…±}•Ù…±}•Å}é•É½}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥A½±å¹½µ¥…±}¡…Íá…ÑI½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥}±•™Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥}Í•½¹‘}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥}Ñ¡¥É‘}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥}É¥¡Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥}¡…Í}½µÁÕÑ…‰±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹™…Ñ½É¥é•‘Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹™…Ñ½É¥é•‘Ù…±}É½½Ñ}Ý¥Ñ¹•ÍÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹™…Ñ½É¥é•‘Ù…±}…ÁÁ•¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Á½±å‘)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Á½±åM…±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Á½±åM¡¥™Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Á½±å1¥¹•…É5Õ±Ñ¥Á±ä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±ä¹•Ù…±}½¹Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±ä¹•Ù…±}Á½±å‘)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±ä¹•Ù…±}Á½±åM…±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±ä¹•Ù…±}Á½±åM¡¥™Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±ä¹•Ù…±}Á½±å1¥¹•…É5Õ±Ñ¥Á±ä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±}•Ù…±}•Å}ÁÉ½‘ÕÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±}•á…Ñ}É½½Ñ}½™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±}½µÁÕÑ…‰±•}É½½Ñ}½™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±}…±±}½µÁÕÑ…‰±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±}¡…Í}…±•‰É…¥}É½½Ñ}½™}¹½¹•µÁÑä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±}¡…Í}½µÁÕÑ…‰±•}É½½Ñ}½™}¹½¹•µÁÑä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±}…±•‰É…¥}É½½Ñ}½™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E½µÁ±•à¹µÕ±}•Å}é•É¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±}•Ù…±}•Å}é•É½}¥™™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±}¡…Íá…ÑI½½Ñ}¥™™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QUÁÁ•ÉI½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Q1½Ý•ÉI½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}ÕÁÁ•É}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}±½Ý•É}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}É½½ÑÍ}…É•}‘¥ÍÑ¥¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}Á½¥¹Ñ}•Ù…±}ÕÁÁ•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}Á½¥¹Ñ}•Ù…±}±½Ý•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}É½½Ñ}Í•…É¡}ÕÁÁ•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}É½½Ñ}Í•…É¡}Í½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}É½½Ñ}Í•…É¡}Í­¥ÁÍ}¹½¹É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}é•É½}•á±ÕÍ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QEÕ…‘É…Ñ¥}é•É½}¥Í}•á±Õ‘•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…‘É…Ñ¥A½±å¹½µ¥…±}¡…Íá…ÑI½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•á…ÑI½½ÑM•…É )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•á…ÑI½½ÑM•…É¡}Í½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•á…ÑI½½ÑM•…É¡}½µÁ±•Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•á…ÑI½½ÑM•…É¡}¹½¹•}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É¡}Í½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É¡}É•ÑÕÉ¹Í}ÍÕÁÁ±¥•‘}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É¡}½µÁ±•Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É¡}¹½¹•}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É¡}Í•±™}Í½µ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É¡}½µÁ±•Ñ•}½µÁÕÑ…‰±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É¡}Í•±™}Í½µ•}½µÁÕÑ…‰±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É¡}Í•±™}Í½µ•}½µÁÕÑ…‰±•}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ…ÉÑ¥A½±å¹½µ¥…±}É½½Ñ}Í•…É¡}Í½µ•}½µÁÕÑ…‰±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘Õ‰¥A½±å¹½µ¥…±}É½½Ñ}Í•…É¡}Í½µ•}½µÁÕÑ…‰±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘A½±å¹½µ¥…±I½½ÑM•…É¡}É•ÑÕÉ¹Í}½µÁÕÑ…‰±•}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…±}•Ù…±}•Å}ÁÉ½‘ÕÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…±}•Ù…±}•Å}é•É½}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…±}•Ù…±}•Å}é•É½}¥™™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…±}¡…Íá…ÑI½½Ñ}¥™™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…±}•á…Ñ}É½½Ñ}½™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…±}½µÁÕÑ…‰±•}É½½Ñ}½™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…±}¡…Í}½µÁÕÑ…‰±•}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…±}¡…Í}…±±}½µÁÕÑ…‰±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÁ½Ý}µÕ°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹¥Í9Ñ¡I½½Ñ}µÕ°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹•á…ÑI½½Ñ}µÕ°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹½¹©Õ…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÁ½Ý}½¹©Õ…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹¥Í9Ñ¡I½½Ñ}½¹©Õ…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹•á…ÑI½½Ñ}½¹©Õ…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹…‘‘I…Ü)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹¹•I…Ü)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹µÕ±I…Ü)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹…‘‘I…Ý}Ù…±¥)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹¹•I…Ý}Ù…±¥)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹5Õ±I…ÝY…±¥)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹…‘‘}…¹¹¥¡¥±…Ñ½É}•á¥ÍÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹¹•}…¹¹¥¡¥±…Ñ½É}•á¥ÍÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹µÕ±}…¹¹¥¡¥±…Ñ½É}•á¥ÍÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹…‘)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹¹•œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹µÕ°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥½µÁ±•à¹¥¹Ù}•á¥ÍÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±A½±ä¹•á¥ÍÑÍ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹±¥¹•…É}É•µ…¥¹‘•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹±¥¹•…É}™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹±¥¹•…É}É½½Ñ}¥™™}½¹ÍÑ…¹Ñ}•Å}¹•}µÕ°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…‘É…Ñ¥}™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…‘É…Ñ¥}É•µ…¥¹‘•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Õ‰¥}É•µ…¥¹‘•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Õ‰¥}™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…‘É…Ñ¥}•Ù…±}É½½Ñ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Õ‰¥}½µÁ±•Ñ¥½¹}É½½ÑÍ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Õ‰¥}½µÁ±•Ñ¥½¹}•á…µÁ±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Õ‰¥}½µÁ±•Ñ¥½¹}•á…µÁ±•}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥MÁ±¥Ñ=¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥MÁ±¥Ñ5¥¹ÕÍ=¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥MÁ±¥Ñi•É¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥MÁ±¥Ñ5¥¹ÕÍ½ÕÈ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥MÁ±¥ÑQÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥MÁ±¥Ñ5¥¹ÕÍQÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥}ÍÁ±¥Ñ}•á…µÁ±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥}ÍÁ±¥Ñ}•á…µÁ±•}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥}µ¥á•‘}ÍÁ±¥Ñ}•á…µÁ±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥}µ¥á•‘}ÍÁ±¥Ñ}•á…µÁ±•}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥5¥á•‘M…±•‘QÝ½%µ…¥¹…Éä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥5¥á•‘M…±•‘5¥¹ÕÍQÝ½%µ…¥¹…Éä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥5¥á•‘M…±•‘Q¡É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥5¥á•‘M…±•‘5¥¹ÕÍQ¡É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥}µ¥á•‘}Í…±•‘}ÍÁ±¥Ñ}•á…µÁ±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ…ÉÑ¥}µ¥á•‘}Í…±•‘}ÍÁ±¥Ñ}•á…µÁ±•}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}‘•É¥Ù…Ñ¥Ù•}±¥¹•…È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹‘•É¥Ù…Ñ¥Ù•Ù…±Õà)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹‘•É¥Ù…Ñ¥Ù•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Á½Ý}µÕ±}•Ù…±}é¥Á%‘á}•Å}‘•É¥Ù…Ñ¥Ù•Ù…±Õà)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}‘•É¥Ù…Ñ¥Ù•}•Å}‘•É¥Ù…Ñ¥Ù•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}‘•É¥Ù…Ñ¥Ù•}ÅÕ…‘É…Ñ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…‘É…Ñ¥}Í•…¹Ñ}ÅÕ½Ñ¥•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…‘É…Ñ¥}Í•…¹Ñ}µ¥¹ÕÍ}‘•É¥Ù…Ñ¥Ù”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}‘•É¥Ù…Ñ¥Ù•}Õ‰¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}‘•É¥Ù…Ñ¥Ù•}ÅÕ…ÉÑ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}‘•É¥Ù…Ñ¥Ù•}ÅÕ¥¹Ñ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}‘•É¥Ù…Ñ¥Ù•}Í•áÑ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}‘•É¥Ù…Ñ¥Ù•}Í•ÁÑ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Õ‰¥}•á…µÁ±•}™…Ñ½É¥é…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Õ‰¥}•á…µÁ±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Õ‰¥}•á…µÁ±•}É½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…ÉÑ¥}•á…µÁ±•}™…Ñ½É¥é…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…ÉÑ¥}•á…µÁ±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…ÉÑ¥}•á…µÁ±•}É½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ%¹½É¥¹i•É½Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ}é•É½}½™}¹½¹¹•œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ%¹½É¥¹i•É½Í}é•É½}½™}¹½¹¹•}½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ}é•É½}½™}¹½¹Á½Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ%¹½É¥¹i•É½Í}é•É½}½™}¹½¹Á½Í}½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ%¹½É¥¹i•É½Í}ÅÕ…‘É…Ñ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…‘É…Ñ¥}É½½Ñ}‘¥ÍÉ¥µ¥¹…¹Ñ}¹½¹¹•œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹¹½}É…Ñ¥½¹…±}É½½Ñ}½™}ÅÕ…‘É…Ñ¥}‘¥ÍÉ¥µ¥¹…¹Ñ}¹•œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…‘É…Ñ¥}Ñ¡É••}‘¥ÍÑ¥¹Ñ}É½½ÑÍ}¥µÁ½ÍÍ¥‰±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}¹½¹¹•}½™}¹½¹¹•}½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}¹½¹Á½Í}½™}¹½¹Á½Í}½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}Á½Í}½™}¹½¹¹•}½•™™Í}½™}Á½Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}¹•}é•É½}½™}¹½¹¹•}½•™™Í}½™}Á½Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹¹½}Á½Í¥Ñ¥Ù•}É½½Ñ}½™}¹½¹¹•}½•™™Í}½™}Á½Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}Á½Í}½™}¹½¹¹•}½¹Í}½™}Á½Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹¹½}¹½¹¹•…Ñ¥Ù•}É½½Ñ}½™}¹½¹¹•}½¹Í}½™}Á½Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}¹•}½™}¹½¹Á½Í}½•™™Í}½™}¹•œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹¹½}Á½Í¥Ñ¥Ù•}É½½Ñ}½™}¹½¹Á½Í}½•™™Í}½™}¹•œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ}ÅÕ…‘É…Ñ¥}•á…µÁ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ%¹½É¥¹i•É½Í}•á…µÁ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Íå¹Ñ¡•Ñ¥¥Ù¥‘”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}ÍÁ•Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}É•µ…¥¹‘•É}•Å}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}É•µ…¥¹‘•É}•Å}é•É½}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}Í•…¹Ñ}ÅÕ½Ñ¥•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹I•µ…¥¹‘•É•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Íå¹Ñ¡•Ñ¥I•µ…¥¹‘•É•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹I•µ…¥¹‘•É•ÉÑ¥™¥…Ñ”¹™…Ñ½É}É•µ…¥¹‘•É}…Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹I•µ…¥¹‘•É•ÉÑ¥™¥…Ñ”¹É•µ…¥¹‘•É}•Å}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹I•µ…¥¹‘•É•ÉÑ¥™¥…Ñ”¹™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹I•µ…¥¹‘•É•ÉÑ¥™¥…Ñ”¹É•µ…¥¹‘•É}•Å}é•É½}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Íå¹Ñ¡•Ñ¥I•µ…¥¹‘•É•ÉÑ¥™¥…Ñ•}™…Ñ½É}É•µ…¥¹‘•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Íå¹Ñ¡•Ñ¥I•µ…¥¹‘•É•ÉÑ¥™¥…Ñ•}™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹Íå¹Ñ¡•Ñ¥¥Ù¥‘”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}ÍÁ•Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}É•µ…¥¹‘•É}•Å}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}É•µ…¥¹‘•É}•Å}é•É½}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}ÅÕ½Ñ¥•¹Ñ}±•¹Ñ )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}ÅÕ½Ñ¥•¹Ñ}Á…‘‘•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹Íå¹Ñ¡•Ñ¥¥Ù¥‘•}™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹•™±…Ñ¥½¹•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹Íå¹Ñ¡•Ñ¥•™±…Ñ¥½¹•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹•™±…Ñ¥½¹•ÉÑ¥™¥…Ñ”¹™…Ñ½É}…Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹•™±…Ñ¥½¹•ÉÑ¥™¥…Ñ”¹™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•Q	½Õ¹‘…Éä¹Íå¹Ñ¡•Ñ¥•™±…Ñ¥½¹•ÉÑ¥™¥…Ñ•}™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹¡…¥¸¹‘•™±…Ñ•‘½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹¡…¥¸¹%Í•™±…Ñ¥½¹¡…¥¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹¡…¥¸¹É½½Ñ…Ñ½ÉAÉ½‘ÕÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹¡…¥¸¹‘•™±…Ñ•‘½•™™Í}±•¹Ñ )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹¡…¥¸¹¡½É¹•É}™…Ñ½É¥é…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹¡…¥¸¹•á…ÑI½½Ñ}½™}•á…ÑI½½Ñ}½™}¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ¥¹Ñ¥	½Õ¹‘…ÉåA½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ¥¹Ñ¥}‰½Õ¹‘…Éå}Á½±å¹½µ¥…±}½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ¥¹Ñ¥}‰½Õ¹‘…Éå}•Ù…±}…Ñ}ÑÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ¥¹Ñ¥}‰½Õ¹‘…Éå}‘•™±…Ñ¥½¹}¡…¥¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ¥¹Ñ¥}‰½Õ¹‘…Éå}‘•™±…Ñ•‘}½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ¥¹Ñ¥}‰½Õ¹‘…Éå}¡½É¹•É}™…Ñ½É¥é…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÅÕ¥¹Ñ¥}‰½Õ¹‘…Éå}•á…Ñ}™…Ñ½É¥é…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±•}ÍÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±•}ÁÉ½‘ÕÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±•}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±•}¹Õµ•É¥}‰½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡Q¡É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡Q¡É••}ÍÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡Q¡É••}ÁÉ½‘ÕÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡Q¡É••}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡Q¡É••}¹Õµ•É¥}‰½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡½ÕÈ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡½ÕÉ}ÍÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡½ÕÉ}ÁÉ½‘ÕÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡½ÕÉ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥55á…µÁ±••ÁÑ¡½ÕÉ}¹Õµ•É¥}‰½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”Ñ}ÍÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”Ñ}Ñ…¥°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”Ñ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”á}ÍÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”á}Ñ…¥°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”á}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”ÄÙ}ÍÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”ÄÙ}Ñ…¥°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”ÄÙ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”ÌÉ}ÍÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”ÌÉ}Ñ…¥°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÑÉ¥…¹Õ±…É}ÍÑ…”ÌÉ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±A…ÉÑ¥…±á…µÁ±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±A…ÉÑ¥…±á…µÁ±•}•á…Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±A…ÉÑ¥…±á…µÁ±•}Á½Í¥Ñ¥Ù•}…¹‘}‰•±½Ý}ÑÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±½µÁ…É¥Í½¹á…µÁ±•5¥‘Á½¥¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±½µÁ…É¥Í½¹á…µÁ±•5¥‘Á½¥¹Ñ}¥¹}‰½Ñ )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±½µÁ…É¥Í½¹á…µÁ±•}Ý¥‘Ñ¡}±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹Õ‰¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹É½½Ñ=¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹É½½ÑQÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹É½½ÑQ¡É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹Õ‰¥}É½½Ñ}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹Õ‰¥}‘•™±…Ñ¥½¹}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹Õ‰¥}‘•™±…Ñ¥½¹}½¹•}É•µ…¥¹‘•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹Õ‰¥}™…Ñ½É}…Ñ}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹Õ‰¥}‘•™±…Ñ¥½¹}¡…¥¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹Õ‰¥}‘•™±…Ñ•‘}½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ••™±…Ñ¥½¹á…µÁ±”¹Õ‰¥}¡½É¹•É}™…Ñ½É¥é…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Qi•É½9•¥¡‰½É¡½½)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Qi•É½9•¥¡‰½É¡½½‘}½É‘•É•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Qi•É½9•¥¡‰½É¡½½‘}•á±ÕÍ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Qi•É½9•¥¡‰½É¡½½‘}¥Í}É½½Ñ}™É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QI½½ÑM•…É¡½µ…¥¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QI½½ÑM•…É¡½µ…¥¹}½É‘•É•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QUÁÁ•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}ÑÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Q1½Ý•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}ÑÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QUÁÁ•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}Ñ¡É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Q1½Ý•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}Ñ¡É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QUÁÁ•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}™½ÕÈ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Q1½Ý•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}™½ÕÈ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QUÁÁ•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}™¥Ù”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Q1½Ý•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}™¥Ù”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•QUÁÁ•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}Í¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Q1½Ý•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}Í¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•Q1½Ý•ÉI½½Ñ}ÍÕÉÙ¥Ù•Í}‘•ÁÑ¡}Ñ¡É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…Ñ¥½¹…±I½½ÑM•…É ¹É…Ñ¥½¹…±I½½ÑM•…É )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…Ñ¥½¹…±I½½ÑM•…É ¹É…Ñ¥½¹…±I½½ÑM•…É¡}Í½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…Ñ¥½¹…±I½½ÑM•…É ¹É…Ñ¥½¹…±I½½ÑM•…É¡}½µÁ±•Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…Ñ¥½¹…±I½½ÑM•…É ¹É…Ñ¥½¹…±I½½ÑM•…É¡}½µÁ±•Ñ•}½™}µ•´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…Ñ¥½¹…±I½½ÑM•…É ¹É…Ñ¥½¹…±I½½ÑM•…É¡}¹½¹•}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…Ñ¥½¹…±I½½ÑM•…É ¹É…Ñ¥½¹…±I½½ÑM•…É¡•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…Ñ¥½¹…±I½½ÑM•…É ¹É…Ñ¥½¹…±I½½ÑM•…É¡•ÉÑ¥™¥…Ñ•}Í½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…Ñ¥½¹…±I½½ÑM•…É ¹É…Ñ¥½¹…±I½½ÑM•…É¡•ÉÑ¥™¥…Ñ•}½µÁ±•Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹¥Í9Ñ¡I½½Ñ}µÕ±}½¹©Õ…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹•á…ÑI½½Ñ}µÕ±}½¹©Õ…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…ÑÕ¸¹Á½±å¹½µ¥…±}‘•™¥¹•‘}…±°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…ÑÕ¸¹Á½±å¹½µ¥…±}•Ù…±=¹½µ…¥¹}•Ä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…ÑÕ¸¹Á½±å¹½µ¥…±=¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I…ÑÕ¸¹Á½±å¹½µ¥…±=¹%¹Ñ•ÉÙ…±}½µÁÕÑ•}•Ä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}Í¥¹}½Õ¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}Á½Í¥Ñ¥Ù•}É½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Ñ¡É••Y…É¥…Ñ¥½¹Õ‰¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Ñ¡É••Y…É¥…Ñ¥½¹Õ‰¥}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Ñ¡É••Y…É¥…Ñ¥½¹Õ‰¥}Í¥¹}½Õ¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Ñ¡É••Y…É¥…Ñ¥½¹Õ‰¥}Á½Í¥Ñ¥Ù•}É½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Ñ¡É••Y…É¥…Ñ¥½¹Õ‰¥}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹™½ÕÉY…É¥…Ñ¥½¹EÕ…ÉÑ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹™½ÕÉY…É¥…Ñ¥½¹EÕ…ÉÑ¥}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹™½ÕÉY…É¥…Ñ¥½¹EÕ…ÉÑ¥}Í¥¹}½Õ¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹™½ÕÉY…É¥…Ñ¥½¹EÕ…ÉÑ¥}Á½Í¥Ñ¥Ù•}É½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹™½ÕÉY…É¥…Ñ¥½¹EÕ…ÉÑ¥}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹½¹•Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹½¹•Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}Í¥¹}½Õ¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹½¹•Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}•¹‘Á½¥¹Ñ}‰É…­•Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹½¹•Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}Õ¹¥ÅÕ•}Á½Í¥Ñ¥Ù•}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ%¹½É¥¹i•É½Í}…‘‘}½¹•}±•}™¥±Ñ•É}±•¹Ñ )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ½¹¥1¥¹•…É}¡…Í}½µÁÕÑ…‰±•}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•á1¥¹•…ÉA½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•á1¥¹•…É}Á½Í¥Ñ¥Ù••É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•á1¥¹•…É}•á…Ñ}É½½Ñ}½™}¥¹Ù•ÉÍ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•á1¥¹•…É}¡…Í}½µÁÕÑ…‰±•}É½½Ñ}½™}¥¹Ù•ÉÍ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E½µÁ±•à¹•á¥ÍÑÍ}µÕ±}¥¹Ù•ÉÍ•}½™}¹½ÉµMÅ}¹•}é•É¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E½µÁ±•à¹µÕ±}…ÍÍ½}•ÉÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E½µÁ±•à¹µÕ±}…‘‘}•ÉÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E½µÁ±•à¹…‘‘}µÕ±}•ÉÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E½µÁ±•à¹µÕ±}½¹•}•ÉÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E½µÁ±•à¹µÕ±}¹•}•ÉÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E½µÁ±•à¹¹•}µÕ±}•ÉÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•á1¥¹•…É}¡…Í}½µÁÕÑ…‰±•}É½½Ñ}½™}¹½ÉµMÄ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E½µÁ±•à¹¹½ÉµMÅ}•Å}é•É½}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•á1¥¹•…É}¡…Í}½µÁÕÑ…‰±•}É½½Ñ}½™}¹•}é•É¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•á1¥¹•…È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•á1¥¹•…É%¹Ù•ÉÍ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•á1¥¹•…ÉI½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•á1¥¹•…É}±•…‘¥¹}¥¹Ù•ÉÍ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•á1¥¹•…É}É½½Ñ}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•á1¥¹•…É}É½½Ñ}™É½µ}¥¹Ù•ÉÍ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±1¥¹•…ÉA½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±1¥¹•…É}Á½Í¥Ñ¥Ù••É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±1¥¹•…É}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±1¥¹•…É}¡…Í}½µÁÕÑ…‰±•}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥}±•™Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥}É¥¡Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥}¡…Í}½µÁÕÑ…‰±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥}Á½Í¥Ñ¥Ù••É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥}É½½Ñ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥}¡…Í}½µÁÕÑ…‰±•}É½½Ñ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥}½Ñ¡•É}É½½Ñ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥}¡…Í}½µÁÕÑ…‰±•}É½½ÑÍ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…‘É…Ñ¥}¡…Í}…±•‰É…¥}É½½ÑÍ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•áEÕ…‘É…Ñ¥A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•áEÕ…‘É…Ñ¥}Á½Í¥Ñ¥Ù••É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•áEÕ…‘É…Ñ¥}É½½Ñ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•áEÕ…‘É…Ñ¥}¡…Í}½µÁÕÑ…‰±•}É½½Ñ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•áEÕ…‘É…Ñ¥}¡…Í}½µÁÕÑ…‰±•}É½½Ñ}½™}‘¥ÍÉ¥µ¥¹…¹Ñ}…¹‘}¹½ÉµMÄ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•áEÕ…‘É…Ñ¥}½Ñ¡•É}É½½Ñ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•áEÕ…‘É…Ñ¥}¡…Í}½µÁÕÑ…‰±•}É½½ÑÍ}½™}‘¥ÍÉ¥µ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Å½µÁ±•áEÕ…‘É…Ñ¥}¡…Í}½µÁÕÑ…‰±•}É½½ÑÍ}½™}‘¥ÍÉ¥µ¥¹…¹Ñ}…¹‘}¹½ÉµMÄ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•áEÕ…‘É…Ñ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•áEÕ…‘É…Ñ¥UÁÁ•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•áEÕ…‘É…Ñ¥1½Ý•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•áEÕ…‘É…Ñ¥}ÕÁÁ•É}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•áEÕ…‘É…Ñ¥}±½Ý•É}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•áEÕ…‘É…Ñ¥}É½½ÑÍ}‘¥ÍÑ¥¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•áEÕ…‘É…Ñ¥}™…Ñ½É¥é…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•áEÕ…‘É…Ñ¥}É½½Ñ}Í•…É¡}ÕÁÁ•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•½µÁ±•áEÕ…‘É…Ñ¥}É½½Ñ}Í•…É¡}Í½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±Õ‰¥A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±Õ‰¥}Á½Í¥Ñ¥Ù••É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±Õ‰¥}±•™Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±Õ‰¥}µ¥‘‘±•}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±Õ‰¥}É¥¡Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±Õ‰¥}¡…Í}½µÁÕÑ…‰±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±Õ‰¥}¡…Í}…±•‰É…¥}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥=¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥%µ…¥¹…Éä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥5¥¹ÕÍ%µ…¥¹…Éä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥A½±å¹½µ¥…±}½•™™¥¥•¹ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘}Õ‰¥}•á…µÁ±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘}Õ‰¥}•á…µÁ±•}•áÁ±¥¥Ñ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥QÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥QÝ½%µ…¥¹…Éä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥QÝ½5¥¹ÕÍ%µ…¥¹…Éä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥QÝ½A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘Õ‰¥QÝ½A½±å¹½µ¥…±}½•™™¥¥•¹ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘}Õ‰¥}ÑÝ½}•á…µÁ±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹µ¥á•‘}Õ‰¥}ÑÝ½}•á…µÁ±•}•áÁ±¥¥Ñ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…ÉÑ¥A½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…ÉÑ¥}Á½Í¥Ñ¥Ù••É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…ÉÑ¥}±•™Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…ÉÑ¥}Í•½¹‘}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…ÉÑ¥}Ñ¡¥É‘}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…ÉÑ¥}É¥¡Ñ}•á…Ñ}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…ÉÑ¥}¡…Í}½µÁÕÑ…‰±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…Ñ¥½¹…±EÕ…ÉÑ¥}¡…Í}…±•‰É…¥}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…ÉÑ¥}™…Ñ½É}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…ÉÑ¥}É•µ…¥¹‘•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•EÕ…ÉÑ¥EÕ…‘É…Ñ¥MÁ±¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•EÕ…ÉÑ¥EÕ…‘É…Ñ¥MÁ±¥Ñ}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™¥¹¥Ñ•EÕ…ÉÑ¥EÕ…‘É…Ñ¥MÁ±¥Ñ}¡…Íá…ÑI½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹µ½¹¥}ÅÕ…‘É…Ñ¥}É½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹µ½¹¥}ÅÕ…‘É…Ñ¥}É½½Ñ}½Õ¹Ñ}±•}ÑÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ}Õ‰¥}½¹•}Ù…É¥…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Õ‰¥}…Ñ}µ½ÍÑ}½¹•}Á½Í¥Ñ¥Ù•}É½½Ñ}½™}Í¥¹}Á…ÑÑ•É¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ}ÅÕ…ÉÑ¥}½¹•}Ù…É¥…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…ÉÑ¥}…Ñ}µ½ÍÑ}½¹•}Á½Í¥Ñ¥Ù•}É½½Ñ}½™}Í¥¹}Á…ÑÑ•É¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}¹½¹¥¹É•…Í¥¹}½™}¹½¹Á½Í}½•™™Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹•Ù…±}ÍÑÉ¥Ñ±å}‘•É•…Í¥¹}½™}¹½¹Á½Í}Ñ…¥°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹…Ñ}µ½ÍÑ}½¹•}Á½Í¥Ñ¥Ù•}É…Ñ¥½¹…±}É½½Ñ}½™}¹½¹Á½Í}Ñ…¥°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ}½¹•}½™}Á½Í}½¹Í}½™}¹•œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í¥¹¡…¹•½Õ¹Ñ%¹½É¥¹i•É½Í}½¹•}½™}Á½Í}½¹Í}¹½¹Á½Í}Ñ…¥°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹½¹•}Á½Í¥Ñ¥Ù•}Ù…É¥…Ñ¥½¹}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹é•É½}Ù…É¥…Ñ¥½¹}É½½Ñ}•á±ÕÍ¥½¹}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÅÕ…‘É…Ñ¥}ÑÝ½}Ù…É¥…Ñ¥½¹}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}Í¥¹}½Õ¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}Á½Í¥Ñ¥Ù•}É½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹ÑÝ½Y…É¥…Ñ¥½¹EÕ…‘É…Ñ¥}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…ÉåA½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…Éå…¹‘¥‘…Ñ•Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…Éå}•Ù…±Õ…Ñ¥½¹}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…Éå}¹½}…¹‘¥‘…Ñ•}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…Éå}É…Ñ¥½¹…±I½½ÑM•…É¡}¹½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹éMÅA±ÕÍ=¹•}¡…Í}½µÁÕÑ…‰±•}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…ÉåA½±å¹½µ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…Éå…¹‘¥‘…Ñ•Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…Éå}•Ù…±Õ…Ñ¥½¹}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…Éå}¹½}…¹‘¥‘…Ñ•}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½½ÑÍ=™U¹¥Ñä¹ÅÕ¥¹Ñ¥	½Õ¹‘…Éå}É…Ñ¥½¹…±I½½ÑM•…É¡}¹½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™…Ñ½É¥é•‘EÕ¥¹Ñ¥A½±å¹½µ¥…±}¡…Í}…±±}½µÁÕÑ…‰±•}É½½ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½µÁÕÑ…‰±•Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹±•‰É…¥Q}½™}™…Ñ½É¥é•‘]¥Ñ¹•ÍÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½µÁÕÑ…‰±•Q}½™}±•‰É…¥Q)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E	½à¹•Ù…±A½±ä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E	½à¹•Ù…±A½±å}Á½¥¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E	½à¹•Ù…±A½±å}½¹Ñ…¥¹Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E	½à¹•Ù…±A½±å}¹½}É½½Ñ}½™}¹½Ñ}½Ù•É±…ÁÍ}é•É¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E	½à¹¥¹¥Ñ•I½½Ñá±ÕÍ¥½¹•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E	½à¹¥¹¥Ñ•I½½Ñá±ÕÍ¥½¹•ÉÑ¥™¥…Ñ”¹¹½}É½½Ñ}¥¹}‘½µ…¥¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E	½à¹=¹•MÕÉÙ¥Ù½É•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹E	½à¹=¹•MÕÉÙ¥Ù½É•ÉÑ¥™¥…Ñ”¹É½½Ñ}µ•µ}ÍÕÉÙ¥Ù½È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥¡¥±‘É•¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥¡¥±‘É•¹}½É‘•É•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥¡¥±‘É•¹}¹•ÍÑ•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥¡¥±‘É•¹}½Ù•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥¡¥±‘É•¹}Ý¥‘Ñ¡}¡•¥¡Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹ÍÕÉÙ¥Ù¥¹¡¥±‘É•¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹ÍÕÉÙ¥Ù¥¹¡¥±‘É•¹}½É‘•É•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹É½½Ñ}µ•µ}ÍÕÉÙ¥Ù¥¹¡¥±‘É•¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹ÍÕÉÙ¥Ù¥¹MÕ‰‘¥Ù¥‘”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹É½½Ñ}µ•µ}ÍÕÉÙ¥Ù¥¹MÕ‰‘¥Ù¥‘”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹ÍÕÉÙ¥Ù¥¹MÕ‰‘¥Ù¥‘•}¹½¹•µÁÑå}½™}É½½Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹ÍÕÉÙ¥Ù¥¹MÕ‰‘¥Ù¥‘•}¹•ÍÑ•‘%¹}Á…É•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹ÍÕÉÙ¥Ù¥¹MÕ‰‘¥Ù¥‘•}½É‘•É•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹ÍÕÉÙ¥Ù¥¹MÕ‰‘¥Ù¥‘•}Ý¥‘Ñ¡}¡•¥¡Ñ}•á…Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥MÕ‰‘¥Ù¥‘”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥MÕ‰‘¥Ù¥‘•}¹½¹•µÁÑä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥MÕ‰‘¥Ù¥‘•}¹•ÍÑ•‘%¹}Á…É•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥MÕ‰‘¥Ù¥‘•}½É‘•É•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥MÕ‰‘¥Ù¥‘•}Ý¥‘Ñ¡}¡•¥¡Ñ}±•}Á…É•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•QMÕ‰‘¥Ù¥Í¥½¸¹‘å…‘¥MÕ‰‘¥Ù¥‘•}Ý¥‘Ñ¡}¡•¥¡Ñ}•á…Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É}ÑÝ½}‰å}ÑÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É}ÑÝ½}‰å}ÑÝ½}Õ¹¥ÅÕ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹Ñ¡É••Y•Ñ½È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹…ÁÁ±å}Ñ¡É••	åQ¡É••}•áÁ±¥¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹Ñ¡É••	åQ¡É••}É…µ•É}É½Ý}•áÁ…¹Í¥½¹Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹Ñ¡É••	åQ¡É••É…µ•ÉM½±ÕÑ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹Ñ¡É••	åQ¡É••}É…µ•É}Í½±Ù•Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹Ñ¡É••	åQ¡É••}É…µ•É}Í½±Ù•Í}½™}‘•Ñ•Éµ¥¹…¹Ñ}¹•}é•É¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É|É|Å|Å|Í}‘•Ñ•Éµ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É|É|Å|Å|Í}Í½±ÕÑ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É|É|Å|Å|Í}™½ÉµÕ±„)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É|É|Å|Å|Í}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É|Í|É|Å|É}‘•Ñ•Éµ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É|Í|É|Å|É}Í½±ÕÑ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É|Í|É|Å|É}™½ÉµÕ±„)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É…µ•É|Í|É|Å|É}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹ÑÝ½	åQÝ½}…å±•å}¡…µ¥±Ñ½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹ÑÝ½	åQÝ½}µÕ±}¥¹Ù•ÉÍ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹ÑÝ½	åQÝ½}¥¹Ù•ÉÍ•}µÕ°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹ÑÝ½	åQÝ½}¥¹Ù•ÉÍ•}Õ¹¥ÅÕ•}É¥¡Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹ÑÝ½	åQÝ½}¥¹Ù•ÉÍ•}Õ¹¥ÅÕ•}±•™Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹ÑÝ½	åQÝ½}¥¹Ù•ÉÍ•}Í½±Ù•Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹ÑÝ½	åQÝ½}Í½±ÕÑ¥½¹}Õ¹¥ÅÕ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹É…Ñ5…ÑÉ¥áQÝ½QÉ…”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹É…Ñ5…ÑÉ¥áQÝ½•Ñ•Éµ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹É…Ñ5…ÑÉ¥á}ÑÝ½	åQÝ½}•Å}•áÁ±¥¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹É…Ñ5…ÑÉ¥á}ÑÝ½	åQÝ½}…å±•å}¡…µ¥±Ñ½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹É…Ñ5…ÑÉ¥á}ÑÝ½	åQÝ½}µ…ÑÉ¥áA½Ý}ÍÕ}ÍÕ}É•ÕÉÉ•¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹É…Ñ5…ÑÉ¥á}ÑÝ½	åQÝ½}µ…ÑÉ¥áA½Ý}É•ÕÉÉ•¹•}Õ¹¥ÅÕ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹Ñ¡É••	åQ¡É••5…ÑÉ¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹Ñ¡É••	åQ¡É••QÉ…”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹Ñ¡É••	åQ¡É••M•½¹‘½•™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹Ñ¡É••	åQ¡É•••Ñ•Éµ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹Ñ¡É••	åQ¡É••}…å±•å}¡…µ¥±Ñ½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹É…Ñ5…ÑÉ¥áQ¡É••QÉ…”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹É…Ñ5…ÑÉ¥áQ¡É••M•½¹‘½•™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹É…Ñ5…ÑÉ¥áQ¡É•••Ñ•Éµ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹É…Ñ5…ÑÉ¥á}Ñ¡É••	åQ¡É••}•Å}•áÁ±¥¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹É…Ñ5…ÑÉ¥á}Ñ¡É••	åQ¡É••}…å±•å}¡…µ¥±Ñ½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹É…Ñ5…ÑÉ¥á}Ñ¡É••	åQ¡É••}µ…ÑÉ¥áA½Ý}É•ÕÉÉ•¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹ÑÝ½	åQÝ½}µ…ÑÉ¥áA½Ý}Ñ¡É•”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹!…Éµ½¹¥=Í¥±±…Ñ½È¹ÑÝ½	åQÝ½}µ…ÑÉ¥áA½Ý}™½ÕÈ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹Ñ¡É••	åQ¡É••}µ…ÑÉ¥áA½Ý}ÍÕ}ÍÕ}ÍÕ}É•ÕÉÉ•¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹µ…ÑÉ¥áA½±å¹½µ¥…±MÕ´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹µ…ÑÉ¥áA½±å¹½µ¥…±MÕµ}µÕ±}µ…ÑÉ¥áA½Ü)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹µ…ÑÉ¥áA½±å¹½µ¥…±MÕµ}Í¡¥™Ñ•‘}…¹¹¥¡¥±…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹¥¹¥Ñ•…å±•å!…µ¥±Ñ½¹•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹¥¹¥Ñ•…å±•å!…µ¥±Ñ½¹•ÉÑ¥™¥…Ñ”¹Í¡¥™Ñ•‘}…¹¹¥¡¥±…Ñ•Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹¥¹¥Ñ•…å±•å!…µ¥±Ñ½¹•ÉÑ¥™¥…Ñ”¹Á½Ý•É}É•ÕÉÉ•¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•…å±•å5…ÑÉ¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•…å±•å5…ÑÉ¥á}ÑÉ…”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•…å±•å5…ÑÉ¥á}‘•Ñ•Éµ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•…å±•å5…ÑÉ¥á}¥‘•¹Ñ¥Ñä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•…å±•å5…ÑÉ¥á}¥‘•¹Ñ¥Ñå}™É½µ}•¹•É¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••…å±•å5…ÑÉ¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••…å±•å5…ÑÉ¥á}ÑÉ…”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••…å±•å5…ÑÉ¥á}Í•½¹‘½•™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••…å±•å5…ÑÉ¥á}‘•Ñ•Éµ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••…å±•å5…ÑÉ¥á}¥‘•¹Ñ¥Ñä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••…å±•å5…ÑÉ¥á}™½ÕÉÑ¡}Á½Ý•È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••9½¹¥…½¹…±…å±•å5…ÑÉ¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••9½¹¥…½¹…±…å±•å5…ÑÉ¥á}ÑÉ…”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••9½¹¥…½¹…±…å±•å5…ÑÉ¥á}Í•½¹‘½•™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••9½¹¥…½¹…±…å±•å5…ÑÉ¥á}‘•Ñ•Éµ¥¹…¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•Q¡É••9½¹¥…½¹…±…å±•å5…ÑÉ¥á}¥‘•¹Ñ¥Ñä)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•½ÕÉ…å±•å5…ÑÉ¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•½ÕÉ…å±•å•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹É•Ñ•½ÕÉ…å±•å5…ÑÉ¥á}…¹¹¥¡¥±…Ñ•Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹É½Ñ…Ñ¥½¹•¹•É…Ñ½É}Á½Ý}™½ÕÉ}å±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹Ñ¡É••	åQ¡É••}µ…ÑÉ¥áA½Ý}ÍÕ}ÍÕ}ÍÕ}É•ÕÉÉ•¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹Á•…¹½	…­•É…Ñ½É¥…±Q…¥±}Í¡¥™Ñ•‘}±•}•ÁÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹é•É½%¹¥Ñ¥…±Y½±Ñ•ÉÉ…%Ñ•É…Ñ¥½¹	½Õ¹‘}•Å}é•É¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥¹¥Ñ•5•Í ¹ÍÕµUÁQ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥¹¥Ñ•5•Í ¹ÍÕµUÁQ½}¥¹É•µ•¹ÑÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥¹¥Ñ•5•Í¡¥™™•É•¹•	½Õ¹)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥¹¥Ñ•5•Í¡¥™™•É•¹•	½Õ¹¹Ñ½M¡½ÉÑ	±½­5•Í¡MÝ••À)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥¹¥Ñ•5•Í¡¥™™•É•¹•	½Õ¹¹¹•áÑ}±•}¡…±˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹M¡½ÉÑ	±½­5•Í¡MÝ••À)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹M¡½ÉÑ	±½­5•Í¡MÝ••À¹¹•áÑ}±•}¡…±˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥É•Ñ5•Í¡!…±Ù¥¹•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥É•Ñ5•Í¡!…±Ù¥¹•ÉÑ¥™¥…Ñ”¹½™M¡½ÉÑ	±½­MÝ••ÁÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥É•Ñ5•Í¡!…±Ù¥¹•ÉÑ¥™¥…Ñ”¹‰½Õ¹‘}±•}•½µ•ÑÉ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥É•Ñ5•Í¡!…±Ù¥¹•ÉÑ¥™¥…Ñ”¹•ÉÉ½É}±•}•ÁÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹¥É•Ñ5•Í¡!…±Ù¥¹•ÉÑ¥™¥…Ñ”¹•ÉÉ½É}•Å}é•É¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹M•±™•É¥Ù…Ñ¥Ù•¥É•Ñ5•Í¡½µÁ…É¥Í½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹M•±™•É¥Ù…Ñ¥Ù•¥É•Ñ5•Í¡½µÁ…É¥Í½¸¹•ÅÕ¥Ù…±•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M…±…É=¹Í•±™•É¥Ù…Ñ¥Ù•%¹¥Ñ¥…±Y…±Õ•U¹¥ÅÕ•}½™}‘¥É•Ñ5•Í )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•áÀ¹Á½Ý•ÉM•É¥•Í}•ÅÕ¥Ù}±½%¹Ñ•É…±%¹Ù•ÉÍ•}½¹}¥¹Ñ•ÉÙ…±}½™}‘¥É•Ñ5•Í )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹½¹ÍÑ…¹ÑA•…¹½	…­•ÉM¥µÁ±•áQ•Éµ}ÍÕŒ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹1¥¹•…É=¹I½Ñ…Ñ¥½¹MåÍÑ•´¹Í¥µÁ±•áA…ÉÑ¥…±}•Ù•¹}ÍÁ±¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹•áÁA…ÉÑ¥…±}¥µ…¥¹…Éå}•Ù•¹}ÍÁ±¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹É½Ñ…Ñ¥½¹áÁI…Ý}Ù…±¥)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹É½Ñ…Ñ¥½¹áÁI…Ý}Ý¥‘Ñ¡}±•}•½µ•ÑÉ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹•¹Ñ•É}•Å}•áÁA…ÉÑ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹áÁI…Ý}Ù…±¥)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹•¹Ñ•É}¥¹ÁÕÑ}±¥ÁÍ¡¥Ñè)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹	½á}½¹Ñ…¥¹•‘}•áÁ…¹‘}½™}¥¹ÁÕÑ}¹•…È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹	½á}™ÕÑÕÉ•}½¹Ñ…¥¹•‘}•áÁ…¹‘}½™}¥¹ÁÕÑ}¹•…È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹	½á•Í}Ý¥‘Ñ¡Í}Í¡É¥¹­}Õ¹¥™½É´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹½Í=¹QÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹M¥¹=¹QÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹9•M¥¹=¹QÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹½Í=¹QÝ½}•ÁÍ¥±½¹•±Ñ…½¹Ñ¥¹Õ½ÕÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹M¥¹=¹QÝ½}•ÁÍ¥±½¹•±Ñ…½¹Ñ¥¹Õ½ÕÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Í¥¹•AÉ•™¥á}•Å}Ñ…å±½ÉAÉ•™¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹½Í¥¹•AÉ•™¥á}•Å}Ñ…å±½ÉAÉ•™¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Í¥¹•AÉ•™¥áM¡¥™Ñ}•Å}½Í¥¹•AÉ•™¥à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹M¥¹•¹Ñ•É}Í•…¹Ñ}•ÉÉ½È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹M¥¹•¹Ñ•É}Í•…¹Ñ}•ÉÉ½É}±•}Ñ¡¥ÉÑå}™½ÕÈ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹M¥¹=¹QÝ½}¡…Í•É¥Ù…Ñ¥Ù•=¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹½Í¥¹•AÉ•™¥á}Í•…¹Ñ}•ÉÉ½É}±•}Ñ¡¥ÉÑå}™½ÕÈ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹½Í•¹Ñ•É}Í•…¹Ñ}•ÉÉ½É}±•}Ñ¡¥ÉÑå}™½ÕÉ}Á±ÕÍ}•‘”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹½Í=¹QÝ½}¡…Í•É¥Ù…Ñ¥Ù•=¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹½Í=¹QÝ½}é•É½}•ÅÕ¥Ù}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹M¥¹=¹QÝ½}é•É½}•ÅÕ¥Ù}é•É¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹9•M¥¹=¹QÝ½}•ÅÕ¥Ù}¹•}Í¥¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹I½Ñ…Ñ¥½¹•É¥Ù…Ñ¥Ù•%¹¥Ñ¥…±•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹Õ¹¥™½ÉµI½Ñ…Ñ¥½¹=¹QÝ½}É½Ñ…Ñ¥½¹%¹¥Ñ¥…±•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹É½Ñ…Ñ¥½¹½ÍI…Ý}Ù…±¥)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹M•É¥•Ì¹É½Ñ…Ñ¥½¹M¥¹I…Ý}Ù…±¥)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹I½Ñ…Ñ¥½¹A•…¹½	…­•É	É¥‘”¹É½Ñ…Ñ¥½¹•¹Ñ•É}•Å}½¹ÍÑ…¹ÑA•…¹½	…­•ÉA…ÉÑ¥…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ½µÁ±•á}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ½µÁ±•á•É¥Ù…Ñ¥Ù•}•Å}Í•Ñ½ÉÉ•…MÁ••‘}É½Ñ…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹ÑI•}‘¥™™•É•¹•EÕ½Ñ¥•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ%µ}‘¥™™•É•¹•EÕ½Ñ¥•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹ÑI•}‘¥™™•É•¹•EÕ½Ñ¥•¹Ñ}ÍÕ‰}‘•É¥Ù…Ñ¥Ù”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ%µ}‘¥™™•É•¹•EÕ½Ñ¥•¹Ñ}ÍÕ‰}‘•É¥Ù…Ñ¥Ù”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹ÑI•}Í•…¹Ñ}•ÉÉ½É}±•}ÑÝ•±Ù”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ%µ}Í•…¹Ñ}•ÉÉ½É}±•}ÑÝ•±Ù”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹ÑI•}¡…Í•É¥Ù…Ñ¥Ù•=¹U¹¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ%µ}¡…Í•É¥Ù…Ñ¥Ù•=¹U¹¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ}¡…Í½µÁ±•á•É¥Ù…Ñ¥Ù•=¹U¹¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹½µÁ±•áÕ¹Ñ¥½¹=¹%¹Ñ•ÉÙ…°¹ÅÕ¥Ù…±•¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ¹Õ±…ÉY•±½¥Ñå=¹U¹¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ•É¥Ù…Ñ¥Ù•=¹U¹¥Ñ}•ÅÕ¥Ù}Á½¥¹Ñ¹Õ±…ÉY•±½¥Ñå=¹U¹¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹MåÍÑ•µ•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹=¹Á½¥¹Ñ=¹U¹¥Ñ}•½µ•ÑÉ¥I½Ñ…Ñ¥½¹MåÍÑ•µ•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹½µÁ±•áI…Ü¹¥µ…¥¹…Éåá¥Í}Ù…±¥)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥É½µÉÑ…¹•½´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥É½µÉÑ…¹•½µ}•ÅÕ¥Ù}¡…±™A¤)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹ÑÝ½ÉÑ…¹•½µ=¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥}•ÅÕ¥Ù}ÑÝ½ÉÑ…¹•½µ=¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥}•ÅÕ¥Ù}•½µ•ÑÉ¥EÕ…ÉÑ•ÉQÕÉ¹=¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥}•ÅÕ¥Ù}•½µ•ÑÉ¥!…±™A¤)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¥µ…¥¹…Éå!…±™}•ÅÕ¥Ù}•½µ•ÑÉ¥%µ…¥¹…Éå!…±˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥}µ¥‘Á½¥¹Ñ}Å…‰Í}±•}ÑÝ¼)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥}µ¥‘Á½¥¹Ñ}ÍÕ‰}±•}Ý¥‘Ñ )½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¹…¹‘¥‘…Ñ•}½É‘•É•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¹…¹‘¥‘…Ñ•}Ý¥‘Ñ¡Í}Í¡É¥¹¬)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¹…¹‘¥‘…Ñ•}½¹Ñ…¥¹•‘}•áÁ…¹‘}•½µ•ÑÉ¥I½Ñ…Ñ¥½¹…¹‘¥‘…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹•½µ•ÑÉ¥I½Ñ…Ñ¥½¹…¹‘¥‘…Ñ•}½¹Ñ…¥¹•‘}•áÁ…¹‘}¡…±™A¥I½Ñ…Ñ¥½¹…¹‘¥‘…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¹}•ÅÕ¥Ù}•½µ•ÑÉ¥I½Ñ…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¹I…‘¥ÕÌ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¹I…‘¥ÕÍ}Í¡É¥¹­Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¹}Ù…±¥)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¹}½¹Ñ…¥¹Í}ÕÉÉ•¹Ñ}…¹‘¥‘…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I•Á…É…µ•ÑÉ¥é…Ñ¥½¸¹…¹±•=¹U¹¥Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I•Á…É…µ•ÑÉ¥é…Ñ¥½¸¹…¹±•=¹U¹¥Ñ}¡…Í•É¥Ù…Ñ¥Ù”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I•Á…É…µ•ÑÉ¥é…Ñ¥½¸¹ÍÁ••‘=¹U¹¥Ñ}½µÁÕÑ•}•Å}Í•Ñ½ÉÉ•…MÁ••)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I•Á…É…µ•ÑÉ¥é…Ñ¥½¸¹…¹±•Ñ}•ÅÕ¥Ù}ÑÝ½}…ÉÑ…¹•½´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I•Á…É…µ•ÑÉ¥é…Ñ¥½¸¹…¹±•=¹U¹¥Ñ}‰½á•Í}ÍÑÉ¥Ñ±å}Í•Á…É…Ñ•)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I•Á…É…µ•ÑÉ¥é…Ñ¥½¸¹…¹±•=¹U¹¥Ñ}•™™•Ñ¥Ù•%¹Ù•ÉÍ•M•Á…É…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I•Á…É…µ•ÑÉ¥é…Ñ¥½¸¹…¹±•=¹U¹¥ÑI•Õ±…É}¥¹Ñ•ÉÙ…±I•Õ±…È)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I•Á…É…µ•ÑÉ¥é…Ñ¥½¸¹…¹±•=¹U¹¥ÑI•Õ±…É}¥¹Ù•ÉÑ¥‰±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I•Á…É…µ•ÑÉ¥é…Ñ¥½¸¹É•Õ±…É¹±•Ñ}½¹•}•ÅÕ¥Ù}ÅÕ…ÉÑ•ÉQÕÉ¹I…Ý}½¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I½Ñ…Ñ¥½¸¹¡…±™A¤)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I½Ñ…Ñ¥½¸¹¡…±™A¥}‰½Õ¹‘Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I½Ñ…Ñ¥½¸¹Á¥I…Ý}•ÅÕ¥Ù}™½ÕÉÉÑ…¹•½µ=¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹M•Ñ½ÉÉ•…I½Ñ…Ñ¥½¸¹É½Ñ…Ñ¥½¹}•ÅÕ¥Ù}•½µ•ÑÉ¥I½Ñ…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¡…±™A¥I½Ñ…Ñ¥½¹}•ÅÕ¥Ù}Í•Ñ½ÉÉ•…I½Ñ…Ñ¥½¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹¥µ…¥¹…Éå!…±™}•ÅÕ¥Ù}Í•Ñ½ÉÉ•…I½Ñ…Ñ¥½¹%µ…¥¹…Éå!…±˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹Í•Ñ½ÉÉ•…A¥I…Ý}•ÅÕ¥Ù}Á¥¥É±•É•„)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A¥AÉ½½™Ì¹Á¤¹Í•Ñ½ÉÉ•…¹±•=¹•}•ÅÕ¥Ù}¡…±™A¤)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥ÁÁÉ½…¡}ÍÑ…”ÄÙ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥ÁÁÉ½…¡}ÍÑ…”ÌÉ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥ÁÁÉ½…¡}ÍÑ…”ØÑ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‘å…‘¥ÁÁÉ½…¡}ÍÑ…”ÄÈá}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™½ÕÉA½¥¹Ñ½ÕÉ¥•ÉMÕµ}™¥™Ñ¡}µ½‘”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™½ÕÉA½¥¹Ñ½ÕÉ¥•ÉQÉ…¹Í™½É´)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™½ÕÉA½¥¹Ñ½ÕÉ¥•ÉQÉ…¹Í™½Éµ}µ½‘•Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹™½ÕÉA½¥¹Ñ½ÕÉ¥•ÉQÉ…¹Í™½Éµ}Á…ÉÍ•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹Á¥­QÉ¥…¹±•½ÕÉ}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹ÁÉ¥µ•I•¥ÁÉ½…±MÕµ}ÑÝ•±Ù•}ÁÉ¥µ•Í}Ñ}Ñ¡É••}¡…±Ù•Ì)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‰•ÉÑÉ…¹‘}ÍÑ…”ØÀ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‰•ÉÑÉ…¹‘}ÍÑ…”ÜÀ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‰•ÉÑÉ…¹‘}ÍÑ…”àÀ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‰•ÉÑÉ…¹‘}ÍÑ…”ÄÀÀ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‰•ÉÑÉ…¹‘}•áÑ•¹‘•‘}™¥¹¥Ñ•}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹‰•ÉÑÉ…¹‘}™ÕÉÑ¡•É}™¥¹¥Ñ•}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹É•Ñ…¹±•}¥Í½Á•É¥µ•ÑÉ¥}…À)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í•Ù•¹Y…É¥…Ñ¥½¹M•ÁÑ¥Œ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í•Ù•¹Y…É¥…Ñ¥½¹M•ÁÑ¥}•Ù…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í•Ù•¹Y…É¥…Ñ¥½¹M•ÁÑ¥}Í¥¹}½Õ¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í•Ù•¹Y…É¥…Ñ¥½¹M•ÁÑ¥}Á½Í¥Ñ¥Ù•}É½½Ñ}¥™˜)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹A½±å¹½µ¥…°¹Í•Ù•¹Y…É¥…Ñ¥½¹M•ÁÑ¥}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•I½Ñ…Ñ¥½¹EÕ…ÉÑ•ÉQÕÉ¹á…µÁ±”¹ÅÕ…ÉÑ•ÉQÕÉ¹%¹ÁÕÐ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•I½Ñ…Ñ¥½¹EÕ…ÉÑ•ÉQÕÉ¹á…µÁ±”¹ÅÕ…ÉÑ•ÉQÕÉ¹	½à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•I½Ñ…Ñ¥½¹EÕ…ÉÑ•ÉQÕÉ¹á…µÁ±”¹Õ¹¥Ñ%µ…¥¹…ÉåA½¥¹Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•I½Ñ…Ñ¥½¹EÕ…ÉÑ•ÉQÕÉ¹á…µÁ±”¹ÅÕ…ÉÑ•ÉQÕÉ¹Q½±•É…¹”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•I½Ñ…Ñ¥½¹EÕ…ÉÑ•ÉQÕÉ¹á…µÁ±”¹ÅÕ…ÉÑ•ÉQÕÉ¹áÁ…¹‘•‘	½à)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•I½Ñ…Ñ¥½¹EÕ…ÉÑ•ÉQÕÉ¹á…µÁ±”¹ÅÕ…ÉÑ•ÉQÕÉ¹	½á}½¹Ñ…¥¹Í}Õ¹¥Ñ}¥µ…¥¹…Éå}ÍÑ…•}•¥¡Ð)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•I½Ñ…Ñ¥½¹EÕ…ÉÑ•ÉQÕÉ¹á…µÁ±”¹ÅÕ…ÉÑ•ÉQÕÉ¹	½á}½¹Ñ…¥¹Í}Õ¹¥Ñ}¥µ…¥¹…Éå}ÍÑ…•}ÑÝ•±Ù”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•I½Ñ…Ñ¥½¹EÕ…ÉÑ•ÉQÕÉ¹á…µÁ±”¹ÅÕ…ÉÑ•ÉQÕÉ¹	½á}½¹Ñ…¥¹Í}Õ¹¥Ñ}¥µ…¥¹…Éå}ÍÑ…•}Í¥áÑ••¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹¥¹¥Ñ•I½Ñ…Ñ¥½¹EÕ…ÉÑ•ÉQÕÉ¹á…µÁ±”¹ÅÕ…ÉÑ•ÉQÕÉ¹	½á}Ý¥‘Ñ¡}ÍÑ…•}Í¥áÑ••¸)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±5¥±±¥½¹½µµ½¹%¹Ñ•ÉÙ…°)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹é•Ñ…QÝ½%¹Ñ•ÉÙ…±}½Ù•É±…ÁÍ}ÁÉ½©•ÑA¥MÅÕ…É•‘=Ù•ÉM¥á|ÄÀÀÀÀÀÁ|ÄØ)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±5¥±±¥½¹½µµ½¹%¹Ñ•ÉÙ…±}•ÉÑ¥™¥…Ñ”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±5¥±±¥½¹½µµ½¹%¹Ñ•ÉÙ…±}Ý¥‘Ñ¡}±”)½µÁÕÑ…‰±•¹…±åÍ¥Ì¹	…Í•±¥¹¥Ñ•½µÁ…É¥Í½¸¹‰…Í•±5¥±±¥½¹½µµ½¹%¹Ñ•ÉÙ…±}µ¥‘Á½¥¹Ñ}•ÉÑ¥™¥…Ñ”(