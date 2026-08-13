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

**Easy benchmark cluster — checked.**  The foundation exposes the rational
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
The algebraic bridge `sqrt_thirty_six_eq_six` now identifies the project’s
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

**Additional computable-analysis target — Gaussian route to (n)-ball volume.**
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
square-to-π bridge, radial shell estimates, and unbounded tails remain explicit
future interfaces rather than being smuggled in as Lebesgue integration.
The first low-dimensional recurrence cases are now explicit: the disk and
3-ball identities are joined by `nBallVolumeModel_four`, giving
`(1/2) * piApprox^2 * radius^4`, and `nBallVolumeModel_five`, giving
`(8/15) * piApprox^2 * radius^5`. These remain finite recurrence identities;
the Gaussian integral and square-to-π bridge are separate targets.
The next parity pair is now checked as well: `nBallVolumeModel_six` gives
`(1/6) * piApprox^3 * radius^6`, while `nBallVolumeModel_seven` gives
`(16/105) * piApprox^3 * radius^7`. The Gaussian integral and radial
shell/tail bridge remain separate computable targets.
The following pair is explicit too: `nBallVolumeModel_eight` gives
`(1/24) * piApprox^4 * radius^8`, while `nBallVolumeModel_nine` gives
`(32/945) * piApprox^4 * radius^9`. These are still finite recurrence
checkpoints, not a claim about Gaussian integration or unbounded volume.
The homogeneity theorem `nBallVolumeModel_scale` now records the expected
radius-scaling law exactly: scaling the radius by `s` scales the finite model
by `s^n`. This is the algebraic volume property needed before any analytic
Gaussian or radial-shell bridge is introduced.

The companion `FiniteGaussianIntegral` module now supplies the bounded analytic
prefix: it integrates the even Taylor polynomial for `exp (-x^2)` term by term
over `[-1,1]`.  The four-term and six-term prefixes are exactly `52/35` and
`31049/20790`.  This is the first concrete Gaussian integral object in the
project; the full-line tail and square-to-π theorem remain the next bridges.
The stage-eight prefix is additionally `1009219/675675`, and the exact
stage-six-minus-stage-four refinement gap is `23/2970`.
The same file adds the finite reciprocal-square tail partial sum at cutoff `1`:
four terms give `1669/3600 < 1`.  This is deliberately a transport layer,
not yet a Gaussian claim; it awaits the pointwise proof
`exp (-x^2) ≤ 1/x^2` for `x ≥ 1`.
The reciprocal-square prefix now also reaches six terms (`90281/176400`) and
eight terms (`3427741/6350400`), with the latter still below `1`.
The existing tail-enclosed exponential evaluator also now checks the concrete
point `x=2`: its stage-20 upper endpoint for `exp (-4)` is at most `1/4`.
The same stage also verifies `exp (-9) ≤ 1/9` and `exp (-16) ≤ 1/16`, packaged
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
general inequality `exp(-x^2) ≤ 1/x^2` and the completed Gaussian integral
remain separate bridges.
The finite (n)-ball recurrence now exposes its first geometric cases:
`nBallVolumeModel_two` gives the disk model (pi r^2), and
`nBallVolumeModel_three` gives the 3-ball model ((4/3)pi r^3), with the
symbol `piApprox` still an explicit rational approximation rather than a
completed real constant.
The ladder now includes `x=5`, with `exp (-25) ≤ 1/25`; the four-point sum is
bounded by `1669/3600`, exactly matching the reciprocal-square tail prefix.
The reusable `PiProofs.pointSegmentLengthRaw` interface now applies the same
certified square-root algorithm to any rational-coordinate squared distance,
with validity and `SqrtRawSpec` theorems for later Ptolemy and polygonal-length
work. The full Euclidean Ptolemy identity remains open.
The finite Ptolemy length certificate now closes that gap for one concrete
rational cyclic quadrilateral: all six raw chord lengths are equivalent to
explicit rational witnesses satisfying Ptolemy’s identity. The general
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
point `(3/5,4/5)`: its executable square is `(-7/25,24/25)`, with unit norm
certificates and an exact bridge to the finite `QComplex` natural power. The
angle/exponential interpretation remains deferred.
The same module now checks the cubic witness
`(3/5+4i/5)^3 = -117/125 + (44/125)i`, including coordinate and unit-norm
certificates. This exercises the general `pointPow_three` identity at a
fully explicit rational point.
The fourth-power witness is now checked as well:
`(3/5+4i/5)^4 = -527/625 - (336/625)i`, with unit norm and a direct
`QComplex.natPow` bridge.  The angle/exponential interpretation remains
deferred.
The fifth-power witness is now checked too:
`(3/5+4i/5)^5 = -237/3125 - (3116/3125)i`, with its unit-norm and finite
`QComplex.natPow` bridge.  This extends the rational de Moivre computation
without adding the deferred angle/exponential interpretation.
The sixth-power witness is now checked as well:
`(3/5+4i/5)^6 = 11753/15625 - (10296/15625)i`, with the same unit-norm and
finite natural-power bridges. The angle/exponential interpretation remains
deferred.
The seventh-power witness continues the same finite chain:
`(3/5+4i/5)^7 = 76443/78125 + (16124/78125)i`, with exact coordinates,
unit norm, and a finite `QComplex.natPow` bridge. The angle/exponential
interpretation remains deferred.
`RationalCode.encode`/`RationalCode.decode` round trip and
`RationalCode.encode_injective`/`RationalCode.encode_eq_iff` show that the
canonical code is unique, while
`rationalCode_decode_surjective` gives every rational an explicit
integer-numerator/positive-denominator code, covering the
representation core of benchmark item 3.  The checked
`diagonalPair`/`diagonalUnpair` inverse, `diagonalPair_injective`,
`integerCode_injective`/`integerCode_surjective`, and
`rationalNatCode_injective` now certify the code path itself, while
`rationalNatCode_decode_surjective` now combine these components into an
explicit natural-number surjection onto the project's rationals.
The stronger `rationalNatCode_encode_surjective` theorem shows that every
canonical `RationalCode.encode q` is hit exactly before decoding.
The packaged `rationalNatCode_existsUnique_canonical_index` theorem records
the corresponding unique natural-number index for each canonical code.
The explicit `rationalNatIndex`, `rationalNatCode_index`, and
`rationalNatIndex_injective` now provide the matching injection from canonical
rationals to natural indices using the normalized numerator/denominator code;
the finite coding-level denumerability interface is therefore complete.
The worked `FiniteRationalCodeExample` makes this interface concrete:
`rationalNatIndex (3/5) = 61`, and decoding the code at index `61` returns
`3/5`.
The certified rational circle-area exhaustion `piCircleArea`, together with
`PiProofs.AreaLoopValidity.areaValid`, is the project's computable core of
benchmark item 9; its interpretation as a classical Euclidean measure theorem
is kept at the chapter's explicit algorithm/area bridge.
The worked `FiniteCircleAreaExample` now evaluates the area enclosure exactly
at stages 1, 2, 3, and 4, with rational endpoints, giving a concrete finite
checkpoint schedule for item 9 without asserting a completed area limit.
The explicit terminating loop `euclideanGcd`, together with
`euclideanGcd_eq_gcd`, `Nat.gcd_rec`, and the gcd divisibility laws covers the
algorithmic part of benchmark item 69.  Its public recurrence
`euclideanGcd_step` and zero-boundary theorems now expose the executable loop
directly, together with its positivity certificate
`euclideanGcd_pos_of_pos` (positive left input suffices) and its symmetry
theorem `euclideanGcd_comm`.  The exact nondegeneracy characterization
`euclideanGcd_pos_iff` additionally reduces positivity to the finite input
condition `a ≠ 0 ∨ b ≠ 0`.  The
coprimality bridge `euclideanGcd_eq_one_iff_coprime` identifies the executable
unit-gcd test with Lean's finite `Nat.Coprime` predicate.  The
direct divisibility theorems `euclideanGcd_dvd_left` and
`euclideanGcd_dvd_right` expose the two input certificates directly.  The
greatestness direction is exposed by `euclideanGcd_dvd_of_dvd`: every common
divisor of the inputs divides the executable result.  The packaged iff
`euclideanGcd_dvd_iff` identifies the executable gcd's divisors exactly with
the common divisors of the two inputs.  The
recursive certificate
`bezout_exists` supplies integer coefficients for the exact identity
`x*a + y*b = Nat.gcd a b`, covering benchmark item 60.
The bridge `euclideanGcd_bezout_exists` identifies the same coefficient
certificate with the executable Euclidean-loop result.
The worked `FiniteGcdSecondExample` computes `gcd(252,198)=18` and checks the
back-substitution identity `4*252 - 5*198 = 18` for item 69.
The same worked module now checks `gcd(1071,462)=21` with the independent
back-substitution identity `-3*1071 + 7*462 = 21`, strengthening the finite
Euclidean/Bézout evidence for items 60 and 69.
It now also checks `gcd(12345,6789)=3` with the explicit identity
`-903*12345 + 1642*6789 = 3`, adding a larger remainder-chain example.
The natural-number theorem `three_dvd_three_digit` is the three-digit decimal
core of benchmark item 85. `decimalDigitSum` now supplies a terminating
decimal digit-sum evaluator with its small-digit reduction lemmas, including
`decimalDigitSum_eq_self_of_lt_ten` and
`decimalDigitSum_succ_of_not_lt_ten`, and
`decimalDigitSum_mod_three` proves global residue preservation modulo 3;
`three_dvd_iff_decimalDigitSum_dvd` exposes the resulting divisibility test.
The worked decimal certificate now includes a second pattern, `321`, whose
digit sum is `6` and which is divisible by 3, alongside the negative control
`322`.  This gives item 85 two distinct finite decision checkpoints.
The same certificate now checks the boundary pair `999` and `1000`: digit sum
`999 = 27` gives divisibility by 3, while `1000` is not divisible by 3.
The worked decimal certificate now also checks `decimalDigitSum 123456 = 21`
and `3 ∣ 123456`, together with the neighboring non-divisibility witness
`¬3 ∣ 123457`, extending item 85 to a six-digit terminating checkpoint.
The new `basePositionalValue_mod_sub_one` theorem generalizes this finite
digit-sum congruence to arbitrary bases (b\ge2) modulo (b-1), with
`decimalPositionalValue_mod_nine` as its decimal specialization.
The list-based theorem `rationalDot_cauchy_schwarz_of_length_eq` now extends
the fixed-dimensional Cauchy--Schwarz certificates to every finite rational
vector of equal length, with the residual represented as a sum of squared
two-by-two minors.
The worked `FiniteCauchySchwarzExample` checks equality for the proportional
rational vectors `(1,2)` and `(2,4)`, including the explicit minor-zero witness.
The companion `FiniteCauchySchwarzThreeExample` checks the non-proportional
vectors `(1,2,3)` and `(3,1,2)`: the dot product is `11`, both squared norms
are `14`, and the explicit minor-square residual is `75`. This gives item 78
both an equality and a strict finite certificate.
The new `FiniteCauchySchwarzFourExample` checks vectors `(1,2,3,4)` and
`(4,3,2,1)`: both squared norms are `30`, the dot product is `20`, and the
explicit minor-square residual is `500`.
The new `FiniteCauchySchwarzSixExample` checks vectors `(1,2,3,4,5,6)` and
`(6,5,4,3,2,1)`: both squared norms are `91`, the dot product is `56`, and
the explicit minor-square residual is `5145`.
The reusable induction principle `nat_induction_schema` is the checked finite
proof/programming core of benchmark item 74.
The worked `FiniteInductionExample` applies that schema to the arithmetic
sum: it re-proves `arithmeticSum n = n*(n-1)/2` and checks the stage-5 value
`10`.
The same induction witness now checks stage 10 exactly as `45`, providing a
larger executable checkpoint for item 74.
The same induction witness now checks stage 20 exactly as `190`, extending the
finite arithmetic-sum checkpoint.
It now also checks stage 40 exactly as `780`, extending the explicit induction
witness while keeping the conclusion entirely finite and rational.
It now also checks stage 80 exactly as `3160`, extending the finite item-74
induction schedule.
The same induction witness now checks stage 160 exactly as `12720`, extending
the finite schedule while retaining the terminating proof.
The finite-counting namespace now supplies `subsetCount_eq_pow` for benchmark
item 52 and the Pascal recurrence/boundary lemmas
`combination_pascal`/`combination_rat_pascal`/`combination_outside`/
`combination_rat_outside` and the diagonal bridge
`combination_rat_self` for the finite certificate core of
benchmark item 58.  The boundary values `combination_self` and
`combination_one` are now also checked, giving the diagonal and first-row
binomial coefficients; `combination_two_rat` supplies the closed rational
second-row formula, and `combination_three_rat`/`combination_four_rat`/
`combination_five_rat`/`combination_six_rat`/`combination_seven_rat`/
`combination_eight_rat` supply the corresponding third- through eighth-row
formulas.  A general finite-set
cardinality API remains out of scope.
The worked `FiniteSubsetCountExample` evaluates the subset recurrence at stage
8, checking `subsetCount 8 = 2^8 = 256` as a concrete item-52 certificate.
The same recurrence now has a stage-10 checkpoint,
`subsetCount 10 = 2^10 = 1024`, making the finite counting refinement
explicit.
It now also has stage 12, with `subsetCount 12 = 2^12 = 4096`, extending the
same executable finite-counting checkpoint.
It now also has stage 16, with `subsetCount 16 = 2^16 = 65536`, extending the
same finite recurrence witness.
It now also has stage 20, with `subsetCount 20 = 2^20 = 1048576`, extending
the executable item-52 counting schedule.
It now also has stage 32, with `subsetCount 32 = 2^32 = 4294967296`, extending
the same finite recurrence witness.
The stage-64 witness now checks `subsetCount 64 = 2^64 = 18446744073709551616`,
continuing the terminating recurrence certificate without introducing a
general finite-set cardinality API.
The worked `FinitePascalExample` evaluates `C(8,3)=56` and checks the Pascal
decomposition `C(8,3)=C(7,2)+C(7,3)=21+35` for item 58.
The Pascal witness now also checks `C(10,3)=120` through
`C(10,3)=C(9,2)+C(9,3)=36+84`, extending the finite recurrence checkpoint.
The same witness now checks `C(15,3)=455` through
`C(15,3)=C(14,2)+C(14,3)=91+364`, adding a larger finite Pascal checkpoint.
It now also checks `C(20,3)=1140` through
`C(20,3)=C(19,2)+C(19,3)=171+969`, extending the finite item-58 recurrence
checkpoint.
It now also checks `C(25,3)=2300` through
`C(25,3)=C(24,2)+C(24,3)=276+2024`, extending the finite Pascal schedule.
The Pascal witness now also checks
`C(32,3)=C(31,2)+C(31,3)=465+4495=4960`, extending the terminating
finite recurrence schedule.
The concrete theorem `sqrt_two_irrational` instantiates the certified square-root
criterion at $2$, proving benchmark item 1 in the project's `RealRaw`
representation.  The stronger public classifications
`sqrt_rational_iff_square` and `sqrt_rational_iff_lowest_terms_square`, along
with the corresponding irrationality criterion in lowest terms, now expose
the full finite square-test boundary in Foundations.
The worked `FiniteSqrtTwoBisectionExample` adds the matching executable trace:
after four exact dyadic comparisons, the target $x^2=2$ is enclosed by
`[11/8, 23/16]` with width `1/16`.  This is the project's computational
alternative to invoking a general completeness theorem.
The same trace now exports stage eight, enclosing the target in
`[181/128,363/256]` with width `1/256`. This gives item 1 a tighter exact
rational checkpoint without changing the potential-infinity semantics.
The same trace now exports stage twelve, enclosing the target in
`[181/128,5793/4096]` with width `1/4096`, strengthening the finite item-1
precision schedule.
The same trace now exports stage sixteen, enclosing the target in
`[92681/65536,46341/32768]` with width `1/65536`.
It now also exports stage twenty, enclosing the target in
`[741455/524288,1482911/1048576]` with width `1/1048576`, extending the
potential-infinity schedule without treating the limit as an attained value.
The public finite-Riemann bridge
`PiProofs.four_arctanSeries_one_equiv_piCircleArea` identifies the Leibniz
series presentation with the certified circle-area presentation, covering the
project-relevant core of benchmark item 26.
The harmonic evaluator now has the explicit dyadic growth certificate
`Logarithm.harmonicSum_two_pow_lower`, derived from
`Logarithm.harmonicSum_double_lower`; this is the finite-growth core of
benchmark item 34 (harmonic-series divergence).  The stronger
`Logarithm.harmonicSum_two_pow_reaches` now returns an explicit stage
`2^(2 * target)` reaching every natural target.  This is the project's
effective, potential-infinity formulation of divergence: every requested
finite height is reached by a finite computation, without asserting an
attained infinite sum.
The named witness now instantiates the next checkpoint explicitly:
`harmonicSum_stage1024_reaches_five` proves `H_1024 >= 5`, extending the
dyadic potential-infinity schedule beyond the stage-256 height-four witness.
The next named witness `harmonicSum_stage4096_reaches_six` proves
`H_4096 >= 6`, extending the same finite height schedule once more.
The new `harmonicSum_stage16384_reaches_seven` witness proves `H_16384 >= 7`,
continuing the explicit finite growth schedule.
The new `harmonicSum_stage65536_reaches_eight` witness proves
`H_65536 >= 8`, extending the same potential-infinity ladder.
The monotonicity theorem `Logarithm.harmonicSum_le_of_le` and its propagation
corollary `Logarithm.harmonicSum_two_pow_reaches_later` now transport each
finite target certificate to every later harmonic stage. This makes the
divergence witness compositional rather than tied to one selected dyadic
index.
The geometric-series layer now has the matching finite reachability package
`Series.geometricSum_finiteApprox_reaches_of_power_budget`: an explicit power
budget on a rational stage returns both the finite partial-sum upper bound and
the remaining error bound.  This strengthens benchmark item 66 in the same
potential-infinity style, with no completed-real limit object.
The public monotonicity certificates `Series.geometricSum_le_of_le` and
`Series.geometricSum_gap_le_of_le` now make the finite approximation target
stable under later stages: partial sums increase and their rational gaps to
the endpoint decrease, for every nonnegative ratio below one.
The half-ratio specialization `Series.geometricSum_finiteApprox_reaches` now
constructs that stage from any requested positive rational tolerance using the
executable dyadic schedule, so the budget is no longer an implicit supplied
witness. The raw representation theorem
`Series.geometricRaw_reaches_of_positive_tolerance` exposes the same finite
stage selector directly at the `RealRaw` interface.
The rational-circle determinant package
`RationalCircle.triangleTwiceArea_cyclic`,
`RationalCircle.triangleTwiceArea_swap_neg`, and
`RationalCircle.triangleTwiceArea_zero_of_collinear` and
`RationalCircle.triangleTwiceArea_pos_of_oriented` supply the finite
orientation/area core of benchmark item 27; completed angle-sum semantics
remain deferred.
The worked `FiniteTriangleOrientationExample` instantiates this package at
`(1,0)`, `(0,1)`, and `(-1,0)`: the signed twice-area is `2`, cyclic
permutation preserves it, swapping two vertices negates it, and the positive
orientation certificate is checked directly.
For benchmark item 80, `MultiplicativeCertificate` now records finite lists of
nontrivial factors and their product, with the checked example
`factorizationCertificate60`.  The finite primality search and recursive
constructor `primeFactorCertificate_exists` now establish existence of a
prime-labelled certificate for every `n>1`.
The public corollary `exists_basicPrime_dvd` extracts the corresponding
basic-prime divisor theorem for every `n>1`.
The constructor `MultiplicativeCertificate.append` now composes two such
finite certificates for a product.  The corresponding
`factors_nonempty` lemmas for both certificate structures show that a
certificate for `n>1` contains at least one factor.
The companion `MultiplicativeCertificate.factor_dvd` theorem shows that every
listed nontrivial factor divides the certified product.
The reusable `natProduct_perm` lemma proves that finite factor products are
invariant under list permutation.  The list-level theorem
`primeFactorList_perm_of_same_product` and the packaged theorem
`PrimeFactorCertificate.factor_perm` then prove full repeated-factor
uniqueness up to permutation for prime-labelled certificates.
The list-member divisibility theorem `list_mem_dvd_natProduct` and the
corollary `PrimeFactorCertificate.exists_prime_dvd` then produce a certified
basic-prime divisor for every nontrivial prime-labelled certificate.
The packaged extraction theorem `PrimeFactorCertificate.exists_factor_dvd`
also returns the factor's list membership, prime label, and divisibility in
one result, ready for recursive certificate construction.
The uniqueness groundwork `basicPrime_eq_of_dvd` proves that divisibility
between two basic primes forces equality.
The corollary `basicPrime_eq_factor_of_dvd_primeFactorization` upgrades this:
a basic prime dividing a prime-labelled certificate equals one of its listed
factors.
The combined characterization `basicPrime_dvd_primeFactorization_iff` makes
this an iff: prime divisors of the certified number are exactly the listed
prime factors.
The cross-certificate lemma
`PrimeFactorCertificate.factor_mem_of_factor_mem` now shows that every factor
in one prime-labelled certificate occurs with the same value in any other
certificate for the same number.  Its symmetric package
`PrimeFactorCertificate.factor_mem_iff` gives
the corresponding occurrence-level iff.  The Nat-list helpers
`natList_perm_cons_of_mem` and `natList_perm_of_nodup_of_mem_iff` now lift this
to `PrimeFactorCertificate.factor_perm_of_nodup`: multiplicity-free
prime-labelled certificates have the same factors up to permutation, and
`PrimeFactorCertificate.factor_perm` extends this to repeated factors.
The worked certificate is now also prime-labelled by `BasicPrime` proofs for
2, 3, and 5 and `primeFactorizationCertificate60`.  The first reusable
Euclid-lemma step is now present as `basicPrime_dvd_of_dvd_mul`; this remains
a concrete example, not a general Fundamental Theorem of Arithmetic proof.
The new `FinitePrimeFactorExample` adds the prime-labelled factor list
`[2,2,2,3,3,5]` for `360`, verifies its product, and records divisibility by
each distinct prime.  This makes the certificate-level item-80 boundary
concrete beyond the earlier `60` example.
The same worked module now checks the larger certificate
`27720 = 2^3 * 3^2 * 5 * 7 * 11`, including terminating primality searches
for the newly introduced factors `7` and `11`.
The criterion `basicPrime_of_no_proper_divisor` now isolates the logical
primality test that a future bounded divisor search must establish.
The iff form `basicPrime_iff_no_proper_divisor` exposes that criterion in both
directions for later executable-search correctness proofs.
The finite evaluator `properDivisorSearch` now checks candidates through the
input bound; its soundness, completeness, and `none` characterization are
proved by `properDivisorSearch_some_is_proper`,
`properDivisorSearch_some_of_proper`, and
`properDivisorSearch_none_iff_no_proper`.  Consequently,
`basicPrime_of_properDivisorSearch_none` converts a finite search miss into a
certified basic-prime proof.  Together with
`PrimeFactorCertificate.factor_perm`, the recursive existence layer
`primeFactorCertificate_exists` now closes the certificate-level existence
and uniqueness core of #80.
Its immediate power consequence, `basicPrime_dvd_of_dvd_pow`, is also checked
and will support later uniqueness arguments.
The finite list product `natProduct` and
`basicPrime_dvd_of_dvd_natProduct` lift this to a prime dividing one member of
a finite factor list; this is still certificate-level FTA groundwork.
The corollary `basicPrime_dvd_of_dvd_primeFactorization` connects it directly
to a `PrimeFactorCertificate`.
The construction `PrimeFactorCertificate.append` now composes certificates
for `m` and `n` into one for `m*n`, preserving the prime labels and product
equation.
The converse certificate interface `PrimeFactorCertificate.factor_dvd` now
shows that every listed factor divides the certified number, complementing
the prime-divisor extraction and uniqueness groundwork.
The companion bound `PrimeFactorCertificate.factor_le` places every listed
factor below the certified number whenever `1 < n`, making the certificate
list explicitly bounded for finite search and validation.
The Euclid-style finite construction
`exists_basicPrime_not_mem_of_all_basicPrime` now returns a certified prime
outside every finite list whose members are certified prime: it factors the
finite product plus one and rules out every listed factor by divisibility of 1.
This is the potential-infinity core of the infinitude-of-primes theorem, with
no completed infinite set or classical existence principle.
The specialized `shiftedRangeProduct` construction now turns that list-level
result into `exists_basicPrime_gt`: every finite bound `n` has a certified
prime strictly above it.  This is the direct potential-infinity form of prime
unboundedness.

**Current benchmark count.** At this certificate boundary, 48 entries have a
checked project-relevant core: 1, 2, 3, 4, 9, 14, 15, 16, 17, 23, 26, 27, 34, 35, 37, 38, 42, 43, 44, 46, 49, 55, 57, 60, 64, 65, 66, 68,
69, 73, 74, 75, 76, 77, 78, 79, 80, 81, 85, 89, 91, 92, 94, 95, 97, 98, and 100. This counts finite and rational-coordinate cores
honestly; it does not claim full classical theorem statements for every item.
The admission rule is strict: every counted entry must have a project-native
statement over `RealRaw`/abstract `Real`, rational interval data, or a finite
certificate. A scoped constructive replacement is counted under its scoped
statement, never as an unrestricted theorem over completed real numbers.

The new `monotone_of_succ_le` and `antitone_of_succ_ge` lemmas propagate a
successor-step rational order bound across every finite index interval.  The
explicit `ascendingNaturalSequence` stages 64 and 128 provide the executable
checkpoint for item 73.  The bounded dyadic sequence `1 - (1/2)^n` adds a
computable potential-infinity witness: it is monotone, bounded by 1, and its
stage-8 error is exactly `1/256`; convergence as an attained real limit is
intentionally left outside this finite boundary.
Stages 16 and 32 now extend this ladder with exact errors `1/65536` and
`1/4294967296`, still without asserting an attained limit.
Stages 64 and 128 extend it further, with errors `1/2^64` and `1/2^128`.
The new `dyadicApproach_error_shrinks` theorem upgrades these checkpoints to
an explicit potential-infinity schedule: for every positive rational tolerance,
the denominator-derived stage bound makes the remaining error small enough.
It still produces no attained limit or completeness principle.

The finite four-point transform in `FiniteFourierCertificate.lean` adds the
item-76 core: the zero mode sums to `4`, modes `1`, `2`, and `3` cancel exactly,
and mode `4` returns to `4` at the rational quarter-turn roots.  This is a
finite Fourier orthogonality and periodicity certificate, not a claim about
convergence of an infinite Fourier series.
The same module now adds a Parseval-style finite energy check for the signal
`(1,2,3,4)`: its unnormalized quarter-turn coefficients have energies
`100, 8, 4, 8`, summing to `120 = 4*(1+4+9+16)`.  This strengthens the finite
transform core without introducing an infinite Fourier limit.
The transform checkpoint now also verifies mode `5`, whose four-point sum is
again zero. This extends the finite periodicity evidence beyond one complete
mode cycle while remaining a rational-complex calculation.
The parameterized `fourPointFourierTransform_parseval` theorem now proves the
same unnormalized energy identity for arbitrary rational samples, extending
the concrete `(1,2,3,4)` check to a reusable four-point transform law.
The companion `fourPointFourierTransform_modes` exposes the four exact mode
formulas in rational coordinates, so the finite cancellation is available as
an explicit computational interface.

The exact lattice triangles in `FinitePickCertificate.lean` add item 92's
finite coordinate core.  The `(4,3)` triangle has area `6`, boundary count `8`,
and interior count `3`; the independent `(5,2)` triangle has area `5`,
boundary count `8`, and interior count `2`.  A non-axis-aligned triangle with
vertices `(0,0),(4,1),(1,4)` has area `15/2`, boundary count `5`, and
interior count `6`; all three satisfy Pick's identity.
The fourth finite witness uses vertices `(0,0),(6,0),(2,5)`: area `15`,
boundary count `8`, and interior count `12`, again satisfying Pick's identity
with a different non-primitive edge pattern.
The unrestricted lattice-polygon theorem remains deferred.

The prime-reciprocal accumulator in `FinitePrimeReciprocalCertificate.lean`
adds item 81's potential-infinity core: every finite certified prime list has
a new certified prime whose positive reciprocal strictly increases the exact
rational sum.  The explicit six-prime checkpoint reaches `40361/30030`
through prime `13`, with a strict increase from the five-prime stage.  This
does not claim the completed infinite divergence theorem.  The eight-prime
checkpoint through `19` now reaches `14117683/9699690`, with a strict increase
from the six-prime stage.  The ten-prime checkpoint through `29` now reaches
`9920878441/6469693230`, with a structural strict increase from the eight-prime
stage.
The twelve-prime checkpoint now verifies that the explicit accumulator exceeds
`3/2`, extending the finite growth ladder without asserting divergence of an
infinite prime series.

The finite primality-search witnesses in `FiniteBertrandCertificate.lean`
add item 98's core at (n=10), (n=20), (n=30), (n=40), (n=50), and (n=60):
primes 11, 23, 31, 41, 53, and 61 are checked inside the corresponding
doubled intervals.
`bertrand_extended_finite_certificate` packages all six interval witnesses as
one reusable finite proposition, including the new `(60,120)` stage.
The general postulate remains deferred.

The rational rectangle inequality in `FiniteIsoperimetricCertificate.lean`
adds item 43's finite geometric core: \(16A\le P^2\), with equality exactly
for a square and an explicit \(3\times4\) certificate.  The general
plane-region isoperimetric theorem remains deferred.  The companion (5\times12)
certificate records area (60), perimeter (34), and strict defect
`34^2 - 16*60 = 196`.
The quantitative defect identity `rectangle_isoperimetric_gap` strengthens
this core: the perimeter-square excess is exactly `4 * (a-b)^2`, making the
equal-side equality case an explicit rational stability statement.

The finite occupancy evaluator in `FiniteBirthdayCertificate.lean` adds item
93's core: 4 people over 10 days give 5040 collision-free assignments and
4960 collision assignments, with exact ratios `63/125` and `62/125`.  The
five-person extension gives 30240 collision-free assignments and 69760
collisions out of 100000, with ratios `189/625` and `436/625` that again
partition the total exactly.

**Parallel formalization batch.** The series, effective-calculus, geometry,
algebra, and finite-ODE workstreams have added the following potential-infinity
certificates: `Series.powerSum_le_mul_pow`,
`ExactFunction.cube_secant_derivative_bracket`,
`RationalCircle.point_power_line_parameter_identity`,
`Polynomial.quartic_factor_of_root`, and
`LinearODE.twoByTwo_cayley_hamilton`. Each is a finite rational
statement; none asserts an attained infinite limit.

The next batch extends the same boundary with
`DirichletSeries.zetaTwoPartial_add_finiteTail_le_interval_hi`,
`ExactFunction.square_secant_derivative_bracket`,
`RationalCircle.triangleTwiceArea_quadrilateral_diagonal_additivity`, and
`Polynomial.quartic_remainder`. The Peano--Baker recurrence was attempted but
is not counted until its shared-module proof succeeds.

The latest batch adds five more finite certificates at the same boundary:
`DirichletSeries.zetaTwoInterval_contains_basel_decimal_1000` records a
stage-1000 rational enclosure containing the decimal $1.644934$;
`Series.AlternatingRaw.leibnizAlternatingRaw_width_le_one_div_succ` gives an
explicit finite width schedule for the Leibniz evaluator;
`rationalBisectionWidth_le_error_budget` bounds a finite rational bisection
width under a supplied budget;
`Polynomial.eval_pos_of_nonneg_cons_of_pos` and
`Polynomial.no_nonnegative_root_of_nonneg_cons_of_pos` provide a rational
nonnegative-root exclusion certificate; and
`factorizedQuadratic_has_computable_roots` supplies explicit roots for a
factorized rational-complex quadratic. None uses completeness or an attained
infinite object.

The next formalization pass strengthens existing entries rather than inflating
the benchmark count: `Series.geometricSum_gap_le_of_power_budget` turns a
finite power budget into a geometric-tail error bound;
`Series.AlternatingRaw.leibnizAlternatingRaw_width_eq_reciprocal` and its
budget corollary expose the exact finite Leibniz width;
`Series.AlternatingRaw.leibnizAlternatingRaw_reaches_of_positive_tolerance`
now constructs a natural stage for every positive rational width request;
`Differential.quartic_secant_derivative_bracket` gives a quartic finite
mean-value bracket; `RationalCircle.heron_three_four_five_coordinate_certificate`
checks Heron's identity against explicit 3--4--5 coordinates; and
`Polynomial.monic_quadratic_root_iff` characterizes the rational roots of a
monic quadratic by its two supplied factors. These remain certificate-level
substitutes for the corresponding classical theorems.

This pass also adds closed forms for the squared and cubed power sums, an
exact rational factor-cancellation quotient certificate, a non-equilateral
coordinate law-of-cosines example, the finite QComplex power law
`QComplex.natPow_mul`, and explicit roots for a factorized QComplex cubic.
These extend items 17, 37, 64, 77, and 94 without introducing completed
trigonometric functions, limits, or completeness.

The current boundary pass adds a denominator-budget modulus for the Basel
interval evaluator, an explicit Taylor kernel remainder budget, a generic
factorized QComplex quartic certificate, and the bridge
`eulerCenter_eq_natPow` from Euler-center approximants to finite repeated
multiplication. These sharpen items 2, 14, 17, 35, and 46 while preserving
the project’s certificate-level interpretation.

The next finite-schema pass adds a generic monomial secant/derivative bracket,
a root-count-at-most-two consequence for a monic quadratic, a reusable
stage-to-stage Basel target-interval propagation theorem, and an explicit
Ptolemy coordinate certificate. These extend items 14, 75, 95, and 100 while
remaining entirely rational and finite.

The finite Mean Value interface is now sharpened by
`Polynomial.finiteCubic_secant_derivative_enclosure_of_budget`: an explicit
rational mesh budget places a cubic secant inside an epsilon-neighborhood of
the endpoint derivative, without asserting an attained real intermediate
point.  The dyadic AM--GM core also exposes
`DyadicAMGM.product_mul_card_pow_le_sum_pow`, a denominator-free form useful
for finite exact-arithmetic certificates.
The generic `Polynomial.finitePolynomial_secant_qabs_error_le_derivative_gap`
now packages the corresponding absolute secant error for every
nonnegative-coefficient Horner polynomial: the secant's distance from the
left endpoint derivative is bounded by the finite derivative bracket width.
This is the reusable rational MVT error interface behind the degree-specific
budget theorems.

The Mean Value target is now explicitly layered: the constructive FTC
endpoint identity comes first, followed by an integral-average derivative
certificate, with a pointwise Lagrange witness reserved for an effectively
continuous monotone derivative (or an effectively differentiable convex
function).  Mere convexity is handled through one-sided derivatives or subgradients rather
than an unjustified exact value of `f'` at an intermediate point.
The reusable theorem
`Integral.ExactCellOrderPreservation.integral_average_between_bounds` now
formalizes that middle layer: on a positive rational cell, lower and upper
pointwise bounds imply that the certified endpoint integral divided by the
cell length lies between the same bounds.  It is an average-value enclosure,
not an assertion that a point attaining the average exists.
For the unit cubic, the new `cubicUnit_mvt_bisection_search` packages the
corresponding potential-infinity witness: the secant slope is `1`, the
normalized derivative target is `1/3`, and the existing certified square
bisection searches an interval whose squared values enclose that target.  This
is an approximate MVT witness for the generally irrational intermediate point,
not a rational exact-root claim.
The quartic companion now uses the generic monotone-target bisection interface:
`quarticUnit_mvt_bisection_tolerance_certificate` accepts every positive
rational tolerance and returns a rational interval bracketing the normalized
derivative target `1/4`, with the width budget proved explicitly.  This is a
reusable higher-degree MVT search pattern, still expressed through potential
infinity rather than an attained irrational point.
The general `FiniteMonomialMVTSearch` module now packages this pattern for
every monomial `x^(n+1)` on `[0,1]`: its normalized derivative average is
`1/(n+1)`, the endpoint target bracket is proved uniformly, and
`monomialUnit_mvt_bisection_tolerance_certificate` supplies a rational
interval of any requested positive width.  This promotes the cubic and
quartic examples to a reusable higher-degree MVT certificate.

For benchmark item 90, `finiteStirlingRatio_pos` now makes the positivity of
the finite Stirling-shaped ratio explicit for every natural index and every
positive rational scale input.  This provides the denominator gate for a
future finite interval transport.  The concrete n=10 certificate is now also
sharpened by `finiteStirlingRatioAtTen_unit_enclosure`, which places the
computed ratio in `[1, 101/100]` while leaving Stirling's asymptotic theorem
deferred.
The companion `finiteStirlingRatioAtTen_unit_error` exports this as the
explicit rational error budget `qabs (R₁₀ - 1) <= 1/100`.
The companion `FiniteStirlingStageEight` certificate repeats the bounded
calculation at `n=8`, with a rational square-root bracket for `sqrt(16*pi)`
and a checked ratio enclosure `[1/2,2]`.
The new `FiniteStirlingStageTwelve` certificate repeats the same finite
transport at `n=12`, using the rational square-root bracket anchored at
`217/25` for `sqrt(24*pi)` and the enclosure `[1/2,2]`.
The new `FiniteStirlingStageSixteen` certificate extends the same bounded
transport to `n=16`, using the bracket `1003/100` for `sqrt(32*pi)` and again
checking the ratio enclosure `[1/2,2]`.
The new `FiniteStirlingStageTwenty` certificate continues this bounded
transport to `n=20`, using the bracket `1121/100` for `sqrt(40*pi)` and again
checking the ratio enclosure `[1/2,2]`; Stirling's asymptotic limit remains
deferred.
The new `FiniteStirlingStageTwentyFour` certificate extends the same bounded
transport to `n=24`, using the bracket `12279/1000` for `sqrt(48*pi)` and again
checking the ratio enclosure `[1/2,2]`.
The `FiniteStirlingStageThirtyTwo` certificate continues the same finite
transport to `n=32`, using the bracket `1418/100` for `sqrt(64*pi)` and again
checking the ratio enclosure `[1/2,2]`; the asymptotic limit remains deferred.

The matrix workstream also adds
`LinearODE.HarmonicOscillator.twoByTwo_matrixPow_three`, reducing the third
power of an explicit rational (2\times2) matrix to its trace, determinant,
the matrix, and the identity. This advances the finite Cayley--Hamilton core
without introducing a general matrix recurrence. The companion
`LinearODE.HarmonicOscillator.twoByTwo_matrixPow_four` carries the same
reduction through the fourth power, with coefficients generated by the finite
Cayley--Hamilton recurrence.
The new `HarmonicOscillator.ratMatrix_threeByThree_eq_explicit` bridge and
`ratMatrix_threeByThree_cayley_hamilton` theorem transport the explicit
3-by-3 identity to arbitrary rational matrix data, while keeping the
characteristic coefficients as finite entry formulas.
The worked `FiniteThreeByThreeCayleyExample` adds the diagonal rational
matrix `diag(1,2,3)`: Lean checks trace `6`, second coefficient `11`,
determinant `6`, and the explicit identity `A^3 - 6A^2 + 11A - 6I = 0`.
The same module now checks the non-diagonal upper-triangular matrix
`[[1,1,0],[0,2,1],[0,0,3]]` with the same coefficients and Cayley--Hamilton
identity, demonstrating the finite matrix layer beyond diagonal data.
The diagonal witness also computes its fourth finite power exactly:
`A^4 = diag(1,16,81)`, providing a concrete consumer of the finite
matrix-power recurrence.
The companion `ratMatrix_threeByThree_matrixPow_recurrence` transports the
finite third-order power recurrence to the same arbitrary matrix input.
The companion `LinearODE.HarmonicOscillator.twoByTwo_inverse_unique_right`
proves uniqueness of the finite inverse certificate among all right inverses
of a nonsingular rational two-by-two matrix.
The symmetric `twoByTwo_inverse_unique_left` theorem supplies the corresponding
left-inverse uniqueness certificate.
The solution interface `twoByTwo_inverse_solves` then certifies that applying
the executable inverse to any finite rational state solves the original system.
`twoByTwo_solution_unique` completes the finite system interface by proving
that two rational solutions with the same right-hand side coincide.

The bridge pass also adds a logarithm mesh error budget, strict arctangent
branch separation for inverse search, finite root-of-unity multiplication
closure, exact (2\times2) inverse identities, and an explicit arctangent
kernel error box. These advance the effective versions of items 17, 49, 64,
75, and 79 without asserting a classical IVT, completed logarithm, or general
algebraic closure theorem.

The function-level pass now adds a finite exponential difference-quotient
enclosure, represented-target square-root search, `RealFunRaw` addition
closure, an FTC endpoint-stage transport theorem, and a four-step rational
rotation cycle. These are constructive bridge lemmas for items 15, 17, 49,
64, 75, and 79; they do not assert the corresponding completed-real theorems.

The named-item pass accepts generic factored quotient cancellation for the
L'Hopital boundary and a restricted one-variation cubic sign/root bound for
Descartes. These are explicit finite substitutes for items 64 and 100.
The worked `quadratic_linear_worked_remainder` example now instantiates the
L'Hopital certificate with the finite quotient analogue of `(x^2-1)/(x-1)`:
the residual error from the base value `2` is exactly the computable step, and
the stage-indexed version makes that error `1/n`. No limit theorem is added.
The companion cubic certificate records the finite residual `3*step + step^2`
after cancelling `(x-1)` from `x^3-1`, together with its stage-indexed form at
`step = 1/n`.  This strengthens item 64 without adding the deferred limit
theorem.
The new `cubic_linear_worked_remainder_at_stage_error_le_four_div` turns that
identity into an explicit precision schedule:
`qabs (R_n - 3) <= 4/n` for every positive stage `n`. This is the finite
algorithmic remainder bound needed before any future limit assembly.
The quartic companion now has the matching bound
`qabs (Q_n - 4) <= 11/n`, certifying the finite residual
`6/n + 4/n^2 + 1/n^3` at every positive stage. This extends the precision
schedule across the next cancellation degree without claiming a limit.
The worked `FiniteSepticMVTExample` now instantiates the finite Mean Value
interface at degree seven: Lean computes the secant of `x^7` on `[0,1]` as
`1` and checks the endpoint derivative enclosure `[0,7]`.  This is a concrete
item-75 benchmark witness while retaining the project's finite, rational
algorithmic boundary.
The new `FiniteNonicMVTExample` extends the finite polynomial ladder to degree
nine: the secant of `x^9` is `1` on `[0,1]` with derivative bracket `[0,9]`,
and is `511` on `[1,2]` with endpoint bracket `[9,2304]`. No intermediate
real point is selected.
The cubic MVT pass now also checks the signed interval `[-1,1]`: the secant
is `1`, and the finite derivative enclosure is `[0,3]`. This broadens item
75's rational-domain coverage without selecting an intermediate point.
It now also includes a genuine pointwise checkpoint on `[2,11]`: the cubic
secant slope is `147`, attained by the monotone derivative `3*x^2` at the
rational interior witness `t = 7`. This is the first explicit pointwise MVT
certificate in the project's monotone-derivative direction.
The reusable `Differential.cube_secant_supplied_mvt_witness` now packages this
pattern for arbitrary rational endpoints and a supplied rational interior
point: checking `a^2 + a*b + b^2 = 3*t^2` is enough to certify the cubic
secant identity at `t`. This makes the pointwise witness an interface rather
than a one-off numerical example, while still avoiding an existential real
intermediate-point theorem.
The new `FiniteQuinticMVTExample` adds the intermediate degree-five witness:
the secant of `x^5` on `[0,1]` is `1`, and the finite derivative bracket is
`[0,5]`. This extends item 75’s worked polynomial ladder without selecting an
intermediate point.
The new `FiniteQuarticMVTExample` fills the intermediate degree-four case:
the secant of `x^4` on `[0,1]` is `1`, with finite derivative bracket `[0,4]`.
The Descartes examples now include `threeVariationCubic`: the finite list for
`(x-1)(x-2)(x-3)` has three sign variations, and exact factorization proves
that its positive rational roots are precisely `1`, `2`, and `3`.
The finite integration-by-parts ladder now includes
`FiniteQuarticQuinticIntegrationByParts`: the two endpoint-weighted rational
grid sums for `x^4` and `x^5` telescope to the endpoint product `1` at every
positive stage, with stage four checked explicitly.  This extends the finite
FTC/product-rule core of item 15 without introducing a completed integral or
a real-number limit.
The existing `FiniteFTCQuintic` certificate is now surfaced as the next
item-15 checkpoint: finite left and right endpoint sums for `x^5` on `[0,1]`
enclose `1/6`, with stage twenty linked explicitly in the Blueprint.  This
keeps the quintic FTC construction discoverable alongside the quartic and
sextic checkpoints.
The new `FiniteComplexQuadraticExample` supplies the next worked FTA
boundary: Lean checks both distinct rational-coordinate roots of
`z^2 - 2*z + 5`, the factorization into the two supplied linear factors, and
the exact finite root-search result.  This strengthens items 2 and 37 while
keeping arbitrary-polynomial root existence deferred.
The new `FiniteComplexLinearExample` adds the explicit non-real linear base
case `-2 + (1+i)z`, with inverse witness `(1-i)/2` and exact root `1-i`.
This instantiates the general complex-linear FTA interface entirely in
rational coordinates, without adding a completed complex division operation.
The new `FiniteCoordinateInequality` module adds the reusable rational
Cauchy--Schwarz certificate, its `QComplex` dot-product specialization, and
the squared-norm addition expansion.  The proof exposes the finite
sum-of-squares remainder and strengthens supporting item 78 and the norm
kernel behind item 91 without introducing a completed Euclidean norm.
The item-80 witness now includes a second prime-labelled factor ordering for
`360`, and `PrimeFactorCertificate.factor_perm` proves the two finite lists
are permutation-equivalent.  This makes the certificate-level uniqueness
boundary executable rather than merely documented.
The same witness now includes `720 = 2^4 * 3^2 * 5`, with its prime-labelled
factor list, product identity, and divisibility checks verified directly.
It now also includes `600 = 2^3 * 3 * 5^2`, with an independent
prime-labelled factor list, product identity, and divisibility checks.
The same finite factorization pass now includes `126 = 2 * 3^2 * 7`, with
its product and divisibility witnesses checked by terminating computation.
The new `FiniteMonotoneSquareIntegral` module promotes the exact square
integral on `[0,1]` to a `MonotoneConstructionFor`: Lean checks the rational
monotonicity factorization, validity of the resulting monotone integral, and
its equivalence to `1/3`.  This advances the constructive FTC core of item 15.
The same bridge now covers `x^3` on `[0,1]`: its finite difference factorization
proves nondecreasingness, and the promoted monotone construction is valid and
equivalent to `1/4`.  Together the square and cubic cases establish the first
non-affine polynomial instances of the monotone-integrability interface.
The ladder now reaches `x^4`: its rational difference factorization proves
monotonicity, and the promoted finite construction is valid and equivalent to
`1/5`.  This extends the item-15 monotone bridge through the quartic FTC
checkpoint.
The new `FiniteMonomialMonotonicity` module generalizes the order component
of that ladder: `exactRat_monomial_nondecreasing` proves that every rational
monomial `x^n` is nondecreasing on `[0,1]`.  This is a reusable finite-input
lemma for later monomial integral and MVT certificates, not a standalone
finite-sum milestone or a completed-real limit theorem.
The new `fourVariationQuartic` continues the finite certificate ladder with
`(x-1)(x-2)(x-3)(x-4)`: Lean checks sign count four and identifies all four
positive rational roots.  This strengthens item 100 without claiming general
real-root counting.
The new `fiveVariationQuintic` extends the same finite pattern to
`(x-1)(x-2)(x-3)(x-4)(x-5)`: Lean checks five sign variations and identifies
all five positive rational roots, while unrestricted Descartes root counting
remains deferred.
- The new `sixVariationSextic` extends the item-100 certificate ladder once
  more: Lean checks six sign variations for
  `(x-1)(x-2)(x-3)(x-4)(x-5)(x-6)` and identifies all six positive rational
  roots.  The unrestricted Descartes theorem remains deferred.
The finite Leibniz pass now also records the stage-10 rational enclosure
`3 <= piLeibniz.compute 10 <= 16/5` and its width bound `1/10`. This is a
concrete item-26 computation; the infinite alternating-series identity remains
a separate theorem.
The same evaluator now has a stage-20 enclosure with width at most `1/20`,
making the potential-infinity refinement explicit while keeping every stage
finite and rational.
The evaluator now also exports a stage-40 enclosure inside `[3,16/5]` with
width at most `1/40`, adding a third explicit potential-infinity checkpoint
for item 26.
The harmonic certificate now also exposes stage 32 exactly as
`586061125622639/144403552893600`, with the explicit lower witness
`H_32 >= 2`.  This extends the finite divergence checkpoints for item 34.
The geometric-series pass now records the exact ratio-`1/2` stage-5 sum
`31/16`, together with its exact tail `1/16` to the finite upper value `2`.
It now also includes the unequal-ratio checkpoint
`geometricSum (2/3) 4 = 65/27`, whose finite tail to the rational target `3`
is `16/27`.
The arithmetic-progression witness now also checks stage 10: the progression
with initial term `3` and difference `2` sums to `120`, with its closed form
and finite upper checkpoint `121` verified over the rationals.
The ratio-`1/2` certificate now also records stage 10:
`geometricSum (1/2) 10 = 1023/512` with exact tail `1/512`.  This strengthens
the finite refinement evidence for item 66 without treating the limit as an
attained infinite sum.
The same certificate now reaches stage 20, with exact sum `1048575/524288`
and tail `1/524288`, making the geometric error schedule visible at a third
finite precision checkpoint.
It now also reaches stage 40, with exact sum `1099511627775/549755813888`
and tail `1/549755813888`, providing a substantially finer finite error budget
for item 66 while retaining the potential-infinity interpretation.
It now also reaches stage 80, with exact sum
`1208925819614629174706175/604462909807314587353088` and tail
`1/604462909807314587353088`.
It now also reaches stage 160, with exact sum
`1461501637330902918203684832716283019655932542975/730750818665451459101842416358141509827966271488`
and tail `1/730750818665451459101842416358141509827966271488`, extending the
same finite geometric error schedule.
It now also reaches stage 320, with the exact dyadic tail
`1/1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288`,
extending the finite item-66 precision schedule.
The stage-640 witness now uses the reusable tail formula: the gap to `2` is
exactly `(1/2)^639`, and the finite sum remains below `2`.
The Pythagorean-triple example now also checks the classic `5-12-13` witness,
both directly and from the parametrization at `(m,n)=(3,2)`.  This gives the
rational-coordinate core of items 4 and 23 a second independent finite
checkpoint.
The arithmetic-progression certificate now reaches stage 40 as well:
`arithmeticProgressionSum 3 2 40 = 1680`, with its closed form and finite
upper checkpoint `1681`.  This extends the explicit potential-infinity error
schedule for item 68 beyond stage 20.
The same certificate now reaches stage 320:
`arithmeticProgressionSum 3 2 320 = 103040`, with closed form and upper
checkpoint `103041`, extending the finite item-68 schedule.
It now also reaches stage 640:
`arithmeticProgressionSum 3 2 640 = 410880`, with closed form and upper
checkpoint `410881`, continuing the finite potential-infinity schedule.
The Basel comparison example now also exports the exact stage-8 partial sum
`1077749/705600` and checks its elementary positive/below-two bounds.  This
is an explicit finite reciprocal-square computation for item 14; Euler's
completed Basel identity remains deferred.
This is the finite rational core of item 66.
The harmonic-series pass now includes the inspectable stage-8 witness
`H_8 = 761/280 > 2`, a concrete finite certificate for item 34 alongside the
general dyadic lower-bound theorem.
The same finite checkpoint is now extended to stage 16:
`H_16 = 2436559/720720 >= 2`.  This is another inspectable potential-infinity
witness for item 34, not a completed infinite-sum argument.
The harmonic witness now also instantiates the general reachability theorem at
target `3`: stage `64 = 2^(2*3)` satisfies `H_64 >= 3`, adding a height-three
potential-infinity checkpoint without evaluating an attained infinite sum.
The same stage now has an exact inspectable value,
`H_64 = 623171679694215690971693339/131362987122535807501262400`,
with the direct inequality `H_64 >= 3` checked by finite rational arithmetic.
It now also reaches target `4` at stage `256 = 2^(2*4)`, extending the finite
height schedule without asserting an attained infinite sum.
The item-79 bisection layer now has a concrete affine trace: for
`f(x)=x-1/2` on `[0,1]`, stage 3 returns `[3/8,1/2]`, preserves the sign
bracket, and has width `1/8`.
The cubic target witness now reaches stage 8 for `x^3 = 2`: the rational
bracket is `[161/128,323/256]`, its width is `1/256`, and both endpoint
comparisons with the target are checked.
The same witness now reaches stage 16 with bracket
`[41285/32768,82571/65536]` and width `1/65536`, strengthening the finite
item-79 precision schedule without introducing an attained real root.
The Cayley--Hamilton pass now includes the worked rational matrix
`[[1,2],[0,3]]`, with trace `4`, determinant `3`, and an independently checked
finite identity `A^2 - 4A + 3I = 0`, also transported through the generic
two-by-two theorem. This is a concrete item-49 witness.
The Bézout pass now includes the explicit Euclidean certificate
`gcd(84,30)=6` with coefficients `(-1)*84 + 3*30 = 6`, a worked finite core
for item 60.
The Bézout certificate now also checks `gcd(99991,12345)=1` through the
explicit identity `2116*99991 - 17139*12345 = 1`.
The binomial pass now includes the stage-5 instance
`binomialSum 5 2 1 6 = 3^5 = 243`, a concrete finite certificate for item 44.
The same worked layer now checks the larger stage-8 evaluation
`binomialSum 8 2 1 9 = 3^8 = 6561`, extending the finite binomial witness.
It now also checks the stage-12 evaluation
`binomialSum 12 2 1 13 = 3^12 = 531441`, making the precision ladder explicit.
The same `2+1` ladder now reaches stage 16:
`binomialSum 16 2 1 17 = 3^16 = 43046721`, another exact finite checkpoint.
The same ladder now reaches stage 20:
`binomialSum 20 2 1 21 = 3^20 = 3486784401`.
It also checks a distinct base pair: `binomialSum 6 2 3 7 = 5^6 = 15625`,
showing the finite identity beyond the `2+1` specialization.  The stage-5
`(4+3)` instance, `binomialSum 5 4 3 6 = 7^5 = 16807`, adds a second
independent base pair.
The decimal divisibility pass now includes the executable examples
`decimalDigitSum 123 = 6` and `3 | 123`, together with the contrasting
non-divisibility of `124`. This is the worked finite core of item 85.
The power-sum pass now includes the stage-6 evaluations
`fourthPowerSum 6 = 979` and `fifthPowerSum 6 = 4425`, a concrete finite core
for item 77.
The same worked certificate now checks `eighthPowerSum 6 = 462979`, extending
the finite power-sum witness to the highest closed-form power currently in
the series layer.
The generic recurrence also checks the ninth-power stage directly:
`powerSum 9 6 = 2235465`.  This is a finite item-77 computation; no infinite
power-series identity is being asserted.
The ninth-power witness now reaches stage 32 as well, with exact sum
`powerSum 9 32 = 95821687265536`, extending the finite item-77 checkpoint.
The same certificate now checks `powerSum 9 8 = 52666768`, adding a larger
exact finite checkpoint for the power-sum family.
The ninth-power witness now reaches stage 64 as well, with exact sum
`powerSum 9 64 = 106496009343230976`, extending the terminating rational
item-77 checkpoint schedule.
It now also checks `powerSum 9 10 = 574304985`, extending the ninth-power
finite checkpoint while retaining the fixed-stage interpretation.
The next checkpoint is `powerSum 9 12 = 3932252676`, extending the same
finite ninth-power computation without introducing an infinite identity.
The next checkpoint now reaches `powerSum 9 16 = 78800938560`, extending the
same exact finite evaluator while retaining the fixed-stage interpretation.
The schedule now reaches `powerSum 9 128 = 113501516170343845888`, continuing
the terminating rational checkpoint family.
The AM--GM pass now includes the exact finite witness
`2*8 <= ((2+8)/2)^2` and the equality case for equal inputs `3,3`, a worked
certificate for item 38.
The Pythagorean-triple pass now includes the scaled (6,8,10) witness and its
parameter realization from (m=2,n=1), a concrete finite core for item 23.
The isosceles-triangle pass now includes the coordinate witness with height
`3` and half-base `4`: both squared legs are `25`, the axis dot product is
`0`, and the squared base is `64`. This is a concrete item-65 certificate.
The companion `5-12-13` coordinate instance checks equal squared legs `169`,
axis dot product `0`, and squared base `576`.
The Cramer pass now includes the rational system `2u+v=5`, `u+3v=10`:
the determinant is `5`, Cramer’s formulas return `u=1,v=3`, and direct
substitution verifies both equations. This is a concrete item-97 certificate.
The triangle-inequality pass now also has a concrete three-term rational
witness: `qabs(-3+4-2)=1`, while the sum of termwise absolute values is `9`.
This is the worked finite core of item 91.
The same list-level certificate now checks the five-term list `(-3,4,-2,7,-5)`:
its sum is `1`, its absolute-value sum is `21`, and the triangle bound holds.
The reusable `qabs_perturbed_sub_le` corollary now propagates two rational
perturbation budgets: replacing `x,y` by `x+e,y+f` increases the separation
bound by at most the certified bounds for `e` and `f`. This is the interval
error-budget form of item 91's finite triangle inequality.
The new `FiniteComplexTriangleExample` lifts the worked layer to rational
complex coordinates: `(3,4)` and `(5,12)` have squared norms `25` and `169`,
their sum has squared norm `320`, and the squared triangle bound is checked
against `(5+13)^2`.
The arithmetic-series pass now includes the progression (3,5,7,9,11): its
stage-5 evaluator is exactly `35`, and the closed-form identity is checked over
the rationals. This is the worked finite core of item 68.
The same progression now has a stage-20 checkpoint: the sum is `440`, its
closed form is checked, and the finite certificate records the upper bound
`441`. This extends the potential-infinity arithmetic-series witness.
The same progression now reaches stage 80: the exact sum is `6560`, the
closed form is checked, and the finite upper checkpoint is `6561`.
It now also reaches stage 160: the exact sum is `25920`, the closed form is
checked, and the finite upper checkpoint is `25921`.
The finite half-pi rotation-input certificate is now available as
`GeometricPiRotation.halfPiInput_certificate`; it packages validity, the
`[1,2]` enclosure, the `2/(n+1)` width modulus, and equivalence with the
rational-circle quarter turn.  The missing shared `PiProofs.olean` artifact
still prevents an authoritative aggregate-root build, but the standalone
geometry module and certificate build successfully.  The full classical
identities remain correctly marked as deferred.
The supplied-target Basel candidate is now checked: the later zeta interval
is contained in an explicitly widened geometric pi-squared-over-six target
interval, with the widening equal to the zeta interval’s finite rational
width. This turns overlap into a reusable finite target enclosure while the
Basel identity itself remains deferred.

The next strengthening pass accepts three more finite substitutes without
inflating the benchmark count: `rationalNatCode_existsUnique_canonical_decode_index`
gives a unique canonical natural code for each rational; `ExactFunction.secant_of_finite_derivative_bracket`
telescopes cellwise rational derivative brackets to an endpoint secant; and
`LinearODE.ratMatrix_twoByTwo_cayley_hamilton` extends the checked Cayley--Hamilton
identity from explicit entries to arbitrary rational 2-by-2 matrices. The new
`RationalCircle.Trigonometry.toQComplex` bridge identifies rational circle
multiplication and powers with the finite `QComplex` operations, and
`toQComplex_pointPow_mul` records the embedded de Moivre law. The new
`toQComplex_normSq`, `toQComplex_pointPow_normSq`, and
`toQComplex_pointPow_normSq_of_unit` declarations transport the circle
norm-square invariant to the finite complex side. This remains a finite
rational-coordinate theorem; the represented complex exponential and angle
semantics are still separate bridges. The new `pointPowRaw` and
`pointPowRaw_equiv_natPow` declarations lift that finite power into a valid
represented complex raw and identify it stagewise with the corresponding
finite rational-complex power. The new `pointPowRaw_mul_equiv` supplies the
general product form: the power of a rational circle product is equivalent,
at the represented-complex level, to the product of the two finite complex
powers. The companion `pointPowRaw_conj_equiv` still transports conjugation
through the represented finite power as well.

The next bridge pass adds four more finite certificates: a geometric block-sum
identity, a reflection/signed-orientation coordinate certificate,
conjugation closure for finite roots of unity, and a concatenable finite FTC
partition fold. These strengthen items 17, 27/65, 66, and 15 without adding
completed angles, limits, or completeness principles.

The following pass adds four more finite strengthening certificates:
`Polynomial.factorizedEval_root_witness` identifies the roots of any supplied
finite rational factor list; `DirichletSeries.zetaTwoPartial_later_in_target_of_budget`
propagates later Basel partial sums through a rational target;
`secantSlope_product_transport` is the finite rational product-rule analogue;
and `RationalCircle.pointPow_conj` records conjugation symmetry for natural
circle powers. These deepen items 2, 14, 35/75, and 17 without introducing
completed limits or angle-valued semantics.

The complex-circle bridge now transports that symmetry as well:
`QComplex.conj_add`, `QComplex.conj_neg`, `QComplex.conj_scaleRat`,
`QComplex.conj_mul`, and `QComplex.conj_natPow` prove conjugation laws for
finite rational-complex affine operations, rational scaling, multiplication,
and powers, while
`RationalCircle.Trigonometry.toQComplex_pointConj` and
`toQComplex_pointPow_conj` connect them to circle coordinates. This is a
finite reflection/de Moivre certificate, not a complex-analytic theorem.

The current pass adds a finite remainder-certificate interface for arbitrary
coefficient lists, a stage/error-budget package for constructive square-root
bisection, conjugate-pair closure for finite root witnesses, and a chart-based
cross-orientation identity. These strengthen items 2, 17, 27, 79, and 89 while
remaining entirely rational and algorithmic.

The transport pass adds `QComplex.natPow_add`, an exact affine-composition
difference-quotient law, finite alternating-series block transport, and a
chart-based Jacobian/partition substitution certificate. These advance the
finite interfaces behind items 15, 17, 26, and 35 without asserting the
completed exponential, convergence, or substitution theorems.

The bounded endpoint pass adds quartic one-variation/root uniqueness data,
nested-stage certificates for the constructive square-root search, affine
transport of finite secant brackets, and a finite candidate-evaluation package
for the quintic boundary. The last item is deliberately only a checked finite
obstruction example; it is not Abel–Ruffini and does not claim absence of all
rational roots. `RootsOfUnity.quinticBoundary_rationalRootSearch_none` now
connects that obstruction to the executable finite rational-root search and
certifies the `none` branch for the supplied candidate list.

The latest exact-arithmetic pass adds a mod-9 decimal invariant, a generic
block decomposition for finite power sums, and the Cayley--Hamilton
second-order recurrence for arbitrary rational 2-by-2 matrix powers. These
strengthen items 49, 77, and 85 without adding general Faulhaber, prime, or
continuous-matrix claims.

The FTA generalization pass adds a finite-list complex factorization layer:
`factorizedPolynomial` builds a polynomial from supplied rational-complex
roots, `factorizedPolynomial_eval_eq_product` exposes its finite product form,
and list membership yields exact and computable root witnesses. The companion
`Polynomial.factorizedEval_append` transports rational factor lists across
concatenation. This advances items 2 and 46 without claiming unrestricted FTA
or a general quartic formula.
The direct package `factorizedPolynomial_has_algebraic_root_of_nonempty` also
returns an algebraic-complex witness from any nonempty supplied factor list.
Its uniform companion `factorizedPolynomial_algebraic_root_of_mem` certifies
every supplied factor as an algebraic root, preserving the exact finite root
set rather than selecting an arbitrary witness.

The generic FTA layer is now root-set complete at the supplied-factor level:
`QComplex.mul_eq_zero` supplies the finite coordinate zero-product law, and
`factorizedPolynomial_eval_eq_zero_iff_mem` identifies exactly the roots in a
finite supplied list. This remains a finite factorization theorem, not an
existence or root-counting theorem for arbitrary polynomials.
The bridge `AlgebraicFTA_of_factorizedWitness` now packages the exact project
boundary: a supplied nonempty finite factorization witness for every
positive-degree input is enough to extract an algebraic/computable root. The
global factorization-existence algorithm remains a separate deferred target.
The packaged theorem `factorizedPolynomial_hasExactRoot_iff_mem` exposes the
same root-set result directly through `CPoly.hasExactRoot`, so downstream
finite certificates do not need to unfold polynomial evaluation.
The factorized quadratic package now reuses that generic boundary through
`factorizedQuadraticPolynomial_hasExactRoot_iff`, giving the direct two-root
exact predicate for the named degree-two certificate.

The finite FTA search interface now also supplies `exactRootSearch` and its
soundness/completeness certificates, together with the factorized-polynomial
specialization and computable-root result. Search completeness is conditional
on a supplied finite candidate list; it does not assert that arbitrary
polynomials have roots or that a global root-search procedure exists.
The companion negative certificates `exactRootSearch_none_iff` and
`factorizedPolynomialRootSearch_none_iff` now characterize a `none` result as
finite candidate exclusion (or candidate/factor-list disjointness).  This
completes the finite search interface on both success and failure branches.
The success-side corollary
`factorizedPolynomialRootSearch_returns_supplied_root` makes the factor-list
boundary explicit: every returned root is one of the supplied factors.
The companion `factorizedPolynomialRootSearch_self_some` makes the positive
finite case executable: every nonempty supplied factor list returns a
certified root when searched against itself.

The quintic boundary is now explicit as well: `factorizedQuinticPolynomial`
packages five supplied complex roots, with finite product evaluation and exact
and computable root witnesses. The direct package
`factorizedQuinticPolynomial_has_computable_root` exposes the first supplied
factor as an existential computable-root witness without requiring a separate
membership argument. This is the project’s certificate-level edge
for items 16 and 46; Abel–Ruffini and a general quintic formula remain outside
the current computable scope.
The matching root-set theorem
`factorizedQuinticPolynomial_eval_eq_zero_iff` now excludes every candidate
outside those five supplied roots, completing the finite success/exclusion
interface at the quintic boundary.
Its list-level form
`factorizedQuinticPolynomial_eval_eq_zero_iff_mem` packages the same result in
the project’s finite factor-list interface.
The companion
`factorizedQuinticPolynomial_hasExactRoot_iff_mem` lifts that membership test
to the public exact-root predicate used by the computable-root certificates.
The worked `FiniteQuinticBoundaryExample` instantiates the package with the
five supplied roots `-2,-1,0,1,2`, checking all five exact rational-complex
root witnesses while keeping the general radicals problem deferred.

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
- The interval-defined order now has explicit arithmetic compatibility:
  `RealRaw.le_add_le_add` for addition, `RealRaw.le_neg_le_neg` for order
  reversal under negation, and `RealRaw.le_sub_le_sub` for subtraction, and
  `RealRaw.le_antisymm` for the two-sided order/equivalence bridge, and
  `RealRaw.le_scaleRat_le_scaleRat` for nonnegative rational scaling, together
  with `RealRaw.le_scaleRat_le_scaleRat_of_nonpos` for the order-reversing
  nonpositive case. These are endpoint-level finite inequalities;
  validity/equivalence transport is still handled separately.
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

**Benchmark item 35 — finite Taylor core checked.** The public
The potential-infinity remainder layer now adds an explicit factorial-tail
schedule: every later finite exponential Taylor prefix stays within a
requested rational tolerance of the selected prefix on a bounded rational
box. This strengthens item 35 without introducing an infinite sum or a
completeness principle.
`FinitePolynomial.taylorPrefix_hasDerivativeOnInterval` and centered variant
formalize the finite polynomial/Taylor--Lagrange certificate, while
`Taylor.ArctanKernel.finiteRemainderRoute` supplies an explicit finite
remainder factorization. The completed Taylor theorem with integral remainder
and its full analytic hypotheses remain a later effective-calculus milestone.
The factorial exponential specialization now also exposes
`FinitePolynomial.expTaylorPrefix_endpointDifference_succ`: appending one
finite Taylor term changes an endpoint difference by the exact rational
monomial contribution, before any tail or completeness argument is used.
The worked `FiniteExponentialTaylorExample` now checks the literal values
`P_5(1)=163/60` and `P_6(1)=1957/720`, then specializes the schedule to
`C=1`, error `1/100`, and seven additional finite terms.  Its enclosure is a
finite rational comparison, not an assertion that an infinite sum has been
attained.
The same worked object now checks the tighter stage-8 prefix
`P_8(1)=109601/40320`, extending the exact finite Taylor checkpoints.
It now also records stage 10 exactly as `P_10(1)=9864101/3628800`, providing a
further finite prefix checkpoint under the same potential-infinity
interpretation.
The exponential Taylor prefix now reaches stage 12 as well:
`P_12(1)=260412269/95800320`, extending the exact rational precision ladder.
The same finite checkpoint now reaches stages 14 and 16:
`P_14(1)=47395032961/17435658240` and
`P_16(1)=56874039553217/20922789888000`.  These extend the exact prefix
ladder while retaining the potential-infinity interpretation.

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
  `precisionAtStage n`. The exact constant evaluator now has the concrete
  witness `exactRat_constant_intervalRegularOn`, establishing the simplest
  pointwise-to-interval-regular bridge used by the later Riemann construction.
  The companion `exactRat_constant_effectiveModulusFor` packages the same
  exact evaluator with the explicit modulus interface.
  The same bridge is now checked for exact rational affine functions with slope
  in `[0,1]`: `exactRat_affine_intervalRegularOn_of_unit_slope` uses the endpoint
  image interval and the explicit input schedule `n+1`, while
  `exactRat_affine_unitSlope` packages the affine monotone integral certificate
  and its exact raw value.  This remains a certificate-level FTC slice; no
  unrestricted interval-regular-to-integral closure is claimed.
  The signed affine extension `exactRat_affine_intervalRegularOn_of_signed_unit_slope`
  now handles both endpoint orientations for slopes in `[-1,1]`; its packaged
  certificate `exactRat_affine_signed_unitSlope` computes the same affine
  endpoint formula using the nondecreasing or nonincreasing construction as
  appropriate.
  The non-affine base case `exactRat_square_intervalRegularOn_unit` is now
  checked as well, using the endpoint-square interval and the explicit schedule
  `2*(n+1)` on `[0,1]`.  This adds a genuine finite polynomial interval
  certificate without invoking completed-real limits.
  `exactSquare_lipschitz_on_unit` supplies the rational Lipschitz bound needed
  by `IntegralIdentities.LipschitzDyadic`; the packaged
  `exactRat_square_integral_certificate` and
  `exactRat_square_integral_raw_valid` now provide a valid finite raw integral.
  Its identification with the closed form `1/3` remains a separate endpoint
  equivalence target.
  The public finite identity `exactSquare_uniformLeftSum_eq` now reduces the
  uniform left square sum to `Series.squareSum n / n^3`, providing the exact
  algebraic half of that endpoint-equivalence proof.
  The matching public right-sum identity
  `exactSquare_uniformRightSum_eq` is now also checked, reducing the right
  endpoint sum to `Series.squareSum (n+1) / n^3`.  Together these two finite
  formulas give the exact endpoint-sum data needed for the enclosure proof.
  The public inequalities `exactSquare_uniformLeftSum_le_one_third` and
  `exactSquare_uniformRightSum_ge_one_third` put the two endpoint sums on
  opposite sides of `1/3`; consequently
  `exactSquare_compute_contains_one_third` proves singleton containment at
  every dyadic stage, and
  `exactRat_square_integral_raw_equiv_one_third` identifies the finite raw
  integral with the exact rational value `1/3`.
  The next polynomial case is now complete as well:
  `exactRat_cube_intervalRegularOn_unit` and `exactCube_lipschitz_on_unit`
  give executable finite certificates for `x^3` on `[0,1]`; the endpoint
  sums reduce to `Series.cubeSum`, and
  `exactCube_compute_contains_one_fourth` together with
  `exactRat_cube_integral_raw_equiv_one_fourth` identifies the resulting raw
  integral with `1/4`.  This is a second concrete FTC example, still entirely
rational and stagewise.
The quartic FTC pass is now complete: `exactRat_quartic_integral_certificate`
and its validity theorem provide the finite raw integral for `x^4` on
`[0,1]`; the left/right endpoint sums reduce to
`Series.fourthPowerSum`, and `exactQuartic_compute_contains_one_fifth` plus
`exactRat_quartic_integral_raw_equiv_one_fifth` identify the result with the
exact rational value `1/5`.
The quintic finite pass is now checked as well: `FiniteFTCQuintic` supplies
interval regularity, a rational Lipschitz bound, both finite endpoint-sum
identities, and a concrete stage-10 enclosure containing `1/6`. The
all-stage exact-value equivalence remains open, so this is a finite
certificate-level FTC result, not a general regularity-to-integrability
theorem.
The same quintic computation now has a direct stage-20 containment certificate
`exactQuintic_compute_contains_one_sixth_stage20`, strengthening the finite
precision evidence while leaving the all-stage symbolic inequality open.
The FTC endpoint layer now also records the stage-eight left sum for the
derivative `6*x^5`: `5439/8192 <= 6/7`.  This extends the finite polynomial
checkpoint pattern to the sextic case without adding a completed-limit claim.
The same sextic endpoint-sum witness now reaches stage 32 exactly,
`1905663/2097152 <= 1`, extending the finite item-15 precision schedule.
The cubic FTC endpoint layer now also exports
`cubeDerivativeLeftSum_le_one_le_rightSum`: at every positive stage, the
left and right sums enclose the exact endpoint difference `1`. The companion
`cubeDerivativeLeftSum_rightSum_gap_le_three_div` bounds their enclosure width
by `3/n`, making the finite FTC bridge an explicit shrinking rational schedule.

The concrete FTA pass now also checks `z^2 + 1` directly at the two supplied
rational-complex roots `0 + i` and `0 - i`, including distinctness and point
Horner evaluation, and its executable candidate search returns the upper root.
This is an explicit finite item-2 witness layered on the
existing box soundness and subdivision interfaces; the accompanying singleton
box exclusion certificate discards the non-root candidate at zero. Global root existence and
arbitrary-degree isolation remain deferred.
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
  `Integral.nondecreasingDarbouxRange`, `...Stage`, and
`...DyadicStage` now expose the literal increasing-function endpoint-box
calculation from the blueprint.  Weak monotonicity proves each cell range
ordered; interval regularity, stage compatibility, and a function-specific
shrinking-width estimate remain deliberately separate requirements before
a `ConstructionFor` can be claimed.  The reusable
`Integral.nondecreasingDarbouxRange_width_le_of_intervalRegular` now proves
the local width estimate: when a cell is within the evaluator's input budget,
one common image interval bounds both endpoint values and bounds the Darboux
range by `1/(n+1)`.  The global partition schedule and construction proof
remain separate requirements.
The aggregate
`Integral.nondecreasingDarbouxStage_width_le_of_uniform_input_budget` now
propagates that bound through a uniform finite partition, giving the explicit
global stage budget `(F.upper - F.lower)/(n+1)`.
The companion
`Integral.nondecreasingDarbouxStage_width_le_of_uniform_input_budget_and_tolerance`
hands that explicit budget directly to an arbitrary requested rational
tolerance. It is the finite precision handoff needed by an eventual
`ConstructionFor` proof; it introduces no limit or completed integral.
The dyadic specialization
`Integral.nondecreasingDarbouxDyadicStage_width_le_of_input_budget` now exposes
the corresponding `2^n`-cell bound, while retaining the input-budget premise
needed before a shrinking-width construction can be claimed.
Its companion
`Integral.nondecreasingDarbouxDyadicStage_width_le_of_input_budget_and_tolerance`
provides the same direct requested-tolerance handoff for the textbook's
stage-indexed dyadic algorithm.
`Integral.MonotoneDarbouxSchedule` now packages the remaining finite schedule
certificates—input budget, nesting, and a potential-infinity shrinking
witness—while deriving nonnegative widths from the finite endpoint-range
lemma—and
`Integral.monotoneDarbouxScheduleRaw_valid` turns them into a valid
`RealRaw` integral algorithm.  This closes the schedule-to-raw bridge while
leaving the construction of those certificates and primitive identification
explicit.
The companion `Integral.monotoneDarbouxScheduleRaw_width_le_of_tolerance`
hands a supplied rational tolerance directly to any scheduled stage, making
the finite width budget available to downstream FTC and MVT certificates.
The independent `FinitePiecewiseRectangles` module now records the local
equal-cell rule needed for a finite piecewise-monotone stage:
`PieceCellKind.increasing` and `.decreasing` select endpoint order, while
`.turning` encloses both endpoint values and a supplied turn bracket.  Its
width formulas and a two-cell quadratic turn witness are checked entirely over
`Rat`.  This is the finite local mechanism behind the sinc animation; it does
not claim a universal monotonicity classifier or a completed integral.
The same module now turns those value intervals into literal rectangle areas:
`pieceCellLowerArea_le_upper` proves the lower area is below the upper
area for every nonnegative cell width, and the quadratic two-cell witness
exports the coarse enclosure `[0,2]`.  Refinement and function-specific
classification remain the separate steps needed to obtain a shrinking integral
construction.
For a turn cell, `pieceCellBounds_turning_width_le` now proves that a
common certified value range controls the entire unresolved rectangle width.
The area version `pieceCellTurningAreaGap_le` multiplies that bound by
the nonnegative cell width, making explicit the two budgets that must shrink:
value-range uncertainty and geometric mesh width.
The aggregate lemmas `piecewiseRectangleAreaSum_gap_eq_width_sum` and
`piecewiseRectangleAreaSum_gap_nonneg` now lift this cellwise estimate to an
entire finite mesh: the global upper-minus-lower rectangle gap is exactly the
sum of domain widths times value-range widths, and is nonnegative for ordered
cells.  This is a finite rational bridge toward the constructive FTC, not an
appeal to an attained integral or completeness.
The companion `piecewiseRectangleAreaSum_gap_le_common_range_budget` theorem
packages the common-range form: a uniform value-width certificate bounds the
whole mesh gap by the sum of the domain widths times that range budget.  This
separates the two refinement obligations cleanly—geometric mesh width and
function-value uncertainty—before any potential-infinity schedule is added.
The new `piecewiseRectangleAreaSum_constant` evaluates that constant per-cell
budget exactly as `(cells.length : Rat) * value`.  Its companion
`piecewiseRectangleAreaSum_gap_le_common_range` therefore gives the closed
form global bound by the number of cells, the cell width, and the common value
range.  This is the finite equal-mesh bridge needed by the constructive FTC
story and does not introduce an infinite sum.
The mesh identity `natCast_mul_mesh_eq_sub` now closes the geometric part for
an equal rational partition: a positive `n`-cell mesh has total width exactly
`b - a`.  Thus a common value-range budget can be normalized to the interval
width without invoking a completed real or a limiting sum.
  turning-bracket helper in `TurningPointIntegral` supplies one component of
  a finite monotone decomposition: every possibly non-rational turn is
  represented by a shrinking rational bracket, while stagewise monotone
  pieces and fixed range boxes cover the complement and the unresolved gaps.
  Lean proves the one-gap component's width shrinks, and
  `FinitePiecewiseStageAssembly` now proves the finite rational aggregation
  has shrinking width; its common-rate estimate is the literal number of
  boxes times the supplied per-box width bound. Supplying the individual boxes
  and proving that their combined stage encloses the intended integral remain
  function-by-function work. This is consciously not a universal existence definition for
  integrals. The reusable
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
  power-series coefficient shifts and finite-difference examples are checked.
  The series-layer API now makes this staging explicit:
  `FormalPowerSeries.coefficientShift` and `HasCoefficientShift` are the
  primary names; legacy formal-derivative names are compatibility aliases,
  not an assertion about evaluated raw functions.
  `FinitePolynomial.taylorPrefix_hasDerivativeOnInterval` now turns every
  finite coefficient prefix into a two-sided rational-interval derivative
  certificate for its coefficient-shift polynomial. This is the precise
  finite Taylor--Lagrange hand-off; at zero,
  `FinitePolynomial.taylorPrefixShift_at_zero` identifies that derivative
  polynomial with the original linear coefficient.  The centered forms
  `taylorPrefixAt_hasDerivativeOnInterval` and
  `taylorPrefixShiftAt_at_basepoint` make the same statement at every
  rational expansion point, using local `x-a` bounds. They still do not
  differentiate an infinite tail.
  The quantitative certificate algebra is now closed under finite addition,
  rational scaling, and products via `SecantDerivativeBound.mul`; the product
  rule retains the explicitly bounded secant-corner term needed by later FTC,
  integration-by-parts, and ODE arguments.
  The executable factorial loop is also now identified, term by term and at
  every finite prefix, with its rational Taylor coefficients
  (`ExpProofs.powerSeriesTermAtTerms_eq_expCoeff_monomial` and
  `ExpProofs.powerSeriesCenterAtTerms_eq_expTaylorPrefix`). This is finite
  algebra only. `FinitePolynomial.expTaylorPrefix_succ` records the literal
  one-term extension, while
  `FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm` supplies the
  common bounded-box factorial majorant for a uniform tail
  certificate. `ExpProofs.uniformExpRaw` realizes that certificate on
  `|x| <= 2`: its fixed-stage boxes are valid and geometrically shrinking,
  and `uniformExpRaw_equiv_expPowerSeries` proves stagewise agreement with the
  selected adaptive exponential evaluator. `ExpProofs.uniformExpOnUnit`
  exposes this schedule as an
  interval function, pointwise equivalent to the selected exponential. The
  derivative of the next finite prefix is exactly its common center, and
  `uniformExpTaylorPrefix_secant_error` bounds the residual finite secant
  error. `FinitePolynomial.expTaylorPrefix_secant_error_le_thirty_four` now
  proves the uniform coefficient `34` for every factorial prefix on
  `|x| <= 2`, and the uniform schedule inherits it. The step-aware
  tail transport has an executable stage selection:
  `uniformExpQuotientPrecision h hh n` makes the shared factorial magnitude
  no more than `precisionAtStage n * |h| / 24`, while
  `uniformExpSelfDerivativeStepPrecision` reserves half the requested output
  precision for the `34 |h|` finite secant error.
  `uniformExpCenter_secant_error_le` and
  `uniformExpOnUnit_hasDerivativeOnInterval` complete the interval-endpoint
  algebra: the common-prefix evaluator proves the full two-sided
  `E' = E` certificate on `[0,1]`. Its exact zero value is separately
  certified, so `uniformExpOnUnit_solvesSelfDerivative` is the first
  constructive initial-value solution record. The same construction is now
  checked on the centered chart `[-1,1]`:
  `uniformExpOnSymmetricUnit_hasDerivativeOnInterval` uses the explicit
  endpoint consequence `|h| <= 2`, and
  `uniformExpOnSymmetricUnit_solvesSelfDerivative` supplies the corresponding
  initial-value record. This does not silently
  transfer the derivative to the pointwise-equivalent adaptive evaluator;
  that representation-closure theorem, uniqueness, and the logarithm
  relation are the next gates. The literal rational-input
  evaluator `ExpProofs.expPowerSeries x` is now already a valid raw real for
  every `x : Rat`: its finite rational series boxes are nested and have the
  public geometric rate `ExpProofs.expPowerSeriesRate x`, with ratio `1/2`.
  The same evaluator is now the total `PartialRealFunRaw`
  `ExpProofs.expPowerSeriesFunction`, and
  `ExpProofs.expPowerSeriesOnInterval a b` gives its valid rational-interval
  restriction. When zero is in that interval,
  `ExpProofs.expPowerSeriesOnInterval_zero_initial_value` supplies the exact
  function-level initial equivalence required by the ODE interface. This is a
  certified representation layer, not yet a derivative-transport bridge to
  the other definitions. Its finite-difference bridge is now explicit:
  `expTaylorQuadratic x = 1 + x + x*x/2`, and
  `FinitePolynomial.expTaylorQuadratic_hasDerivativeOnInterval` certifies its
  full two-sided interval derivative `1 + x` on every rational subinterval of
  a supplied bounded symmetric box, using the reusable quantitative
  finite-secant linear interface. `ExpProofs.expTaylorQuadratic_forwardDerivativeAtZero`
  remains the specialized forward derivative `1` at zero by the exact quotient
  `1 + h/2`. More importantly,
  `ExpProofs.expPowerSeriesOnUnit_forwardDerivativeAtZero` now certifies the
  tail-enclosed power-series evaluator itself has forward derivative `1` at
  zero. Its finite stage-zero loop has a positive-tail-plus-radius budget of
  `O(h^2)` on `0 < h <= 1/2`, so quotienting gives an explicit first-order
  enclosure. This remains a local boundary theorem for the adaptive
  representative. The
  constant-level compound-interest representative is now additionally packaged as the
  positive base `ExpProofs.ePositive`: its lower interval endpoint is always
  at least `2`, and `ExpProofs.eNaturalPower` gives valid literal natural
  powers between `2^n` and `4^n`. Rational roots, rational-exponent
  continuity, and the self-derivative theorem remain separate open bridges.
- **Linear ODEs — finite Peano--Baker core and direct scalar uniqueness closure checked; analytic layer open.**
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
  `RotationSeries.rotationExpRaw_valid` now encloses those prefixes in nested
  rational complex boxes, with both coordinate widths bounded by
  `8 * rotationTailMagnitude T 0 * (1/2)^n`. Its
  `rotationCosRaw` and `rotationSinRaw` coordinate projections are valid raw
  reals with the same rate. The common bounded-input evaluator is now also
  exposed as `RotationCalculus.uniformRotationCosOnTwo` and
  `uniformRotationSinOnTwo`: both satisfy the project's literal rational
  epsilon--delta continuity definition on `[-2,2]`, with the checked modulus
  `delta = eps / 16` and one uniform factorial stage supplied by
  `uniformRotationBoxes_widths_shrink_uniform`. `RotationTaylorBridge` now
  identifies those literal centers with the corresponding finite formal
  sine/cosine Taylor prefixes and checks the fixed-stage sine secant estimate
  `uniformRotationSinCenter_secant_error`. Its odd-prefix recurrence is now
  bounded by the exponential factorial budget, giving the uniform finite
  theorem `uniformRotationSinCenter_secant_error_le_thirty_four`.
  `RotationDerivative.uniformRotationSinOnTwo_hasDerivativeOnInterval` now
  combines that finite `34 * |h|` error with a step-aware factorial stage
  selected from `precisionAtStage n * |h| / 48`, proving the full two-sided
  raw interval certificate `sin' = cos` on `[-2,2]`. The derivative belongs
  to this common-prefix evaluator. Its companion
  `RotationDerivative.uniformRotationCosOnTwo_hasDerivativeOnInterval`
  now proves `cos' = -sin` against the explicit
  `uniformRotationNegSinOnTwo` evaluator. The finite cosine prefix has one
  dropped sine term, which is assigned a separate factorial shift and joined
  to the divided-tail shift by `max`. `RotationInitialValues` now checks the
  matching finite initial boxes `C(0)=1` and `S(0)=0`, then packages both
  derivatives and those values as
  `uniformRotationOnTwo_rotationInitialCertificate`. Derivative transport to
  equivalent representations remains open. The continuous-simplex
  interpretation, vector uniqueness, and the rotation/geometric
  identification remain open.
  The scientific-calculus gate is the continuous
  interval-matrix Peano--Baker series with simplex integral boxes, that
  scalar tail certificate lifted to componentwise boxes, and variation of
  constants.
  This is the intended constructive **linear Picard--Lindelöf** theorem for
  vector systems:
  Peano--Baker supplies the homogeneous resolvent, variation of constants
  supplies the affine solution, and a bounded zero-initial difference is
  driven to the zero raw vector by an explicit factorial schedule.  Scalar
  `f' = f` uniqueness is deliberately separate: the checked direct
  finite-mesh closure reduces an error envelope by a factor of two per
  refinement sweep.  Constructing that sweep from derivative certificates
  remains open. General nonlinear Picard--Lindelöf remains a later
  interval-Lipschitz/contraction layer.
- **Scalar exponential uniqueness — direct mesh closure checked; analytic
  bridge open.** `ScalarODEUniqueness.lean` does not use Peano--Baker or
  Picard iteration.  A `DirectMeshHalvingCertificate` records rational error
  envelopes from finite mesh sweeps, and its theorem `error_eq_zero` chooses
  a computable dyadic sweep count to force the error to zero.  The
  `SelfDerivativeDirectMeshComparison` wrapper then yields
  `SelfDerivativeInitialValueUnique`; the exact comparison theorem for
  power-series and inverse-logarithm exponentials is available as
  `powerSeries_equiv_logIntegralInverse_on_interval_of_directMesh`.
  `ShortBlockMeshSweep.next_le_half` now checks the exact one-block algebra:
  a telescoped bound `next <= length * previous + residual` with
  `length <= 1/4` and `residual <= previous/4` halves the envelope.
  The cell/telescoping part is now formalized as well:
  `FiniteMesh.sumUpTo_increments` proves the finite endpoint identity and
  `FiniteMeshDifferenceBound.toShortBlockMeshSweep` converts cellwise
  rational increment bounds into that one-block sweep. What remains is only
  to derive those finite increment estimates from two supplied interval
  derivative certificates.

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

**Benchmark item 15 — constructive FTC core checked.** The
`EffectiveFTC`/`StaticDyadicEffectiveFTC` packages and their endpoint-
agreement bridges formalize the finite schedule-to-endpoint identity in the
effective-calculus chapter. This is the project’s certificate-level core;
unrestricted classical hypotheses are not being smuggled into the interface.
The finite selector `FTC.requestedPrecision` now has public certificates
`FTC.requestedPrecision_positive` and `FTC.requestedPrecision_le_one`, making
the normalization and boundedness of every requested schedule precision
explicit. The companion `FTC.requestedPrecision_antitone` proves the selector
is nonincreasing across finite stages, supplying the schedule-order invariant
needed by later endpoint-transport arguments.
The finite polynomial integration-by-parts module now exposes both endpoint
orientations of the product-rule telescope on rational grids. Its
quadratic/cubic specialization proves both sums equal one at every positive
finite stage. This strengthens the item-15 integration-by-parts boundary
without introducing a completed integral or a classical limit.
The newly integrated `FiniteFTCQuartic` module adds a concrete quartic FTC
checkpoint: dyadic left and right sums for `x^4` on `[0,1]` enclose the exact
rational value `1/5` at every finite stage, and the resulting raw integral is
proved equivalent to `RealRaw.ofRat (1/5)`.
The sextic-derivative endpoint-sum witness now also reaches stage 16 exactly:
`FiniteFTC.sexticDerivativeLeftSum_stage16` evaluates the finite sum to
`107775/131072`, and its companion upper-bound theorem keeps the result below
`6/7`. This tightens the item-15 finite schedule without treating the
integral as an attained infinite limit.
The same sextic derivative schedule now reaches stage 64 exactly:
`FiniteFTC.sexticDerivativeLeftSum_stage64` evaluates to
`32002047/33554432`, with the corresponding finite upper-bound check.
It now also reaches stage 128 exactly:
`FiniteFTC.sexticDerivativeLeftSum_stage128` evaluates to
`524369919/536870912`, again with the finite upper-bound check below `1`.
The same schedule now reaches stage 256 exactly:
`FiniteFTC.sexticDerivativeLeftSum_stage256` evaluates to
`8489598975/8589934592`, with its explicit finite upper-bound check below `1`.

- Public integral target: construct an `Integral.ConstructionFor F` from a
  `ContinuousFunctionOnInterval`.
  See `Integral.ConstructionFor` and `Integral.ExistsConstructionFor` in
  `ComputableAnalysis/Calculus.lean`.
- Proved bridge: once the construction exists, the integral is a computable
  real.
  See `integral_construction_proves_well_defined_for`.
- Concrete existence case: `Integral.constantMonotoneConstructionFor` gives a
  valid point-valued integral algorithm for every constant exact-rational
  function, and `Integral.exists_constantMonotoneConstructionFor` packages
  the corresponding monotone construction witness.
  `Integral.constantMonotoneIntegralFor_eq_ofRat` exposes the resulting raw
  integral as exactly `RealRaw.ofRat ((b - a) * c)`.
- Affine extension: `Integral.affineMonotoneConstructionFor` and
  `Integral.exists_affineMonotoneConstructionFor` do the same for
  `x ↦ r * x + c` when `0 ≤ r`, using the exact rational endpoint formula
  `(b - a) * (r * (a + b) / 2 + c)`.
- The opposite orientation is now covered by
  `Integral.exactRat_affine_nonincreasing`,
  `Integral.affineMonotoneConstructionFor_of_nonpos`, and
  `Integral.exists_affineMonotoneConstructionFor_of_nonpos` for `r ≤ 0`,
  with the same exact formula. Together these give the complete affine
  monotone family while retaining finite rational certificates.
  The matching identities
  `Integral.affineMonotoneIntegralFor_eq_ofRat` and
  `Integral.affineMonotoneIntegralFor_of_nonpos_eq_ofRat` expose the affine
  raw integrals by their exact endpoint formula.
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
  The companion identity
  `rightStieltjesSum_eq_left_swap_add_quadraticVariation` identifies the
  right-endpoint sum with the swapped left-endpoint sum plus exactly that
  finite quadratic variation.
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
  `Integral.IntegrationByPartsCertificate` now packages the next general
  handoff: after a particular paired mesh has certified that its two
  integral raws add to the product-endpoint raw,
  `left_integral_equiv_endpoint_sub_right` and its symmetric companion
  derive the usual endpoint-minus-other-integral formula by valid raw
  interval cancellation.  Constructing that paired mesh from arbitrary
  derivative data remains separate.
  The checked
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
  `RealRaw.le_mul_le_mul_of_nonneg` proves order monotonicity of products on
  nonnegative valid representatives, while
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
  logarithmic integral with the inverse of canonical exponential, use direct
  scalar finite-mesh uniqueness to equate the power-series, Euler, and
  inverse-integral exponentials, then transport the resulting `log 2`
  through the integration-by-parts identity.  A later
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
  `52/2^n`.  It instantiates the certificate-level integration-by-parts
  rebalancing theorem, but does not yet construct such certificates from a
  general effective FTC or identify the canonical exp/log transport; those
  are the stronger remaining refinements of this row.
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

The scheduled arctangent branch now provides a cofinal stage schedule
`arctanScheduledStageSchedule`. `arctanScheduledRectangleRaw` is definitionally
the corresponding rescheduling of the finite geometric rectangle raw, and
`arctanScheduledRectangleRaw_equiv_arctanGeom` proves that it represents the
same abstract arctangent. Its explicit rectangle width budget is
`1/(16*(n+1))`. The remaining inverse-function obligation is the interval
image/containment certificate for endpoint boxes, not a hidden appeal to a
completed real-valued arctangent.

**Benchmark item 79 — branch-local bisection core checked.**
`HasBisectionSearch` and `inverse_function_from_bisection_search` formalize
the effective intermediate-value search for an interval-regular monotone
branch with explicit range and separation certificates. A general classical
IVT remains outside the representation boundary. The finite step interface
`monotoneBisectionStep` now gives the corresponding local rational algorithm:
it preserves endpoint signs and interval containment for a nondecreasing
function and halves the width exactly. It is a reusable certificate for
constructive IVT traces, not an assertion that a zero is attained.
The recursive `monotoneBisectionIterate` now lifts this to every finite stage:
ordering, subinterval containment, and endpoint signs are preserved, while
`monotoneBisectionIterate_width` gives the exact (2^{-n}) width schedule.
The companion `monotoneBisectionIterate_width_pos` proves that the ordinary
finite bracket iterator also retains positive width whenever its initial
interval does.
The companion `monotoneBisectionIterate_width_le_of_power_budget` turns a
supplied rational budget `I.width <= eps * 2^n` into the final guarantee that
the iterated bracket has width at most `eps`.  This exposes the bisection
iteration as an executable precision scheduler for the constructive IVT
boundary.  The target-parametrized companion
`monotoneTargetBisectionStep` and its iterated form
`monotoneTargetBisectionIterate` preserve a supplied rational target bracket
at every finite stage.  This is the inverse-search form of the certificate:
the algorithm narrows an interval whose endpoint evaluations enclose the
target, without asserting that a completed-real preimage has been attained.
The target-aware step and iteration now also expose source containment and
the exact width law `I.width / 2^n`.  These are the finite invariants needed to
turn a separation oracle into a data-valued inverse search.  The companion
`monotoneTargetBisectionIterate_certificate` packages orderedness, target
enclosure, source containment, and this exact width in one reusable finite
record.  The companion
`monotoneTargetBisectionIterate_width_le_of_power_budget` converts a supplied
rational initial-width budget into an explicit requested-tolerance guarantee.
The companion `monotoneTargetBisectionIterate_width_pos` proves that every
finite iterate still has positive width whenever the initial bracket does,
making the potential-infinity interpretation explicit.
The companion
`monotoneTargetBisectionIterate_reaches_of_positive_tolerance` now removes the
supplied power budget for initial intervals of width at most one: stage
`eps.den` is certified to reach every positive rational tolerance. This is an
executable inverse-search schedule for the finite bisection core, not an IVT
or completeness principle. The new
`monotoneTargetBisectionIterate_tolerance_certificate` packages that schedule
together with target enclosure and source containment, giving an inverse
client one finite certificate rather than separate bookkeeping lemmas.
The composition lemma `monotoneTargetBisectionIterate_add` identifies a later
finite stage with the same iterator started from an earlier stage's interval.
Consequently `monotoneTargetBisectionIterate_later_subinterval` proves that
every later target bracket is nested inside every earlier one.  This makes
refinement explicit in the certificate API while keeping the IVT replacement
a finite rational statement rather than a hidden appeal to a limit point.
The worked `FiniteSquareRootBisectionExample` now applies the target search to
`x^2 = 1/2` on `[0,1]`: stage 4 returns `[11/16,3/4]`, preserves the target
bracket, and has width `1/16`. This is a non-affine finite witness for item 79.
The companion `FiniteCubeRootBisectionExample` applies the same target search
to `x^3 = 2` on `[1,2]`: stage 4 returns `[5/4,21/16]`, preserves the target
bracket, and has width `1/16`. This gives item 79 a second nonlinear inverse
trace while retaining the project's finite, potential-infinity semantics.
The new `FiniteFourthRootBisectionExample` applies the same search to
`x^4 = 2` on `[1,2]`: stage 8 returns `[19/16,305/256]` with width `1/256`,
and stage 16 returns `[77935/65536,4871/4096]` with width `1/65536`.
This extends item 79's nonlinear finite inverse-search ladder while retaining
the potential-infinity interpretation.
The cube-root and fourth-root traces now also reach stage 24, each with exact
width `1/16777216` and certified endpoint comparisons, extending the same
potential-infinity precision schedule.

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
  For an anchored represented target, the new
  `sqrtOnUnitRepresentedTargetSearch_stage_certificate` packages the same
  subinterval, endpoint-square, width-budget, and target-overlap guarantees
  at one finite stage.  The anchor is explicit data; no represented-target
  existence or choice principle is inferred.
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
  proposition.  The monotonicity and separation certificates are now
  formalized in `ArctanGeomInverseData`: they transport the rectangle
  evaluator's finite order bounds through the certified containment of each
  positive-loop box.  This keeps the inverse route entirely interval-valued
  and executable.  The matching box-valued continuity theorem is
  `arctanGeomOnUnit_near_of_qabs_le`, with the explicit modulus packaged as
  `arctanGeomOnUnit_effectiveModulus`; interval regularity and the data-valued
  bisection search are the remaining pieces of this branch.  The native
  positive-loop evaluator is now also exposed through the cofinal finite
  schedule `arctanGeomScheduledStage`; `arctanGeomScheduledOnUnit` retains
  the same geometric boxes while satisfying the literal width estimate
  `arctanGeomScheduledOnUnit_width_le`.  This is the intended evaluator for
  the interval-image certificate, rather than silently changing the native
  algorithm's precision convention.
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
  There is now one checked local derivative instance for the literal series
  evaluator: `ExpProofs.expPowerSeriesOnUnit_forwardSelfDerivativeAtZero`
  certifies `D⁺ exp(0) = exp(0)`, with the derivative represented by the
  full raw `expPowerSeries 0`; the stagewise normalization above yields its
  value `1`.  Its finite proof uses positive steps at the endpoint only, so it
  is not the required two-sided interval theorem `exp' = exp`.
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
  The interval certificate now generalizes to
  `Logarithm.oneOverXOnOneTo_intervalRegular` for every rational `b` with
  `1 <= b`; this isolates the upper-endpoint-independent part of the positive
  reciprocal transport.
  The stronger `oneOverXOnInterval_lower_ge_one_intervalRegular` form now
  handles arbitrary `[a,b]` with `1 <= a <= b`, making the lower-bound
  dependence explicit before the final rational scaling argument.
  The fully positive version
  `oneOverXOnPositiveInterval_intervalRegular_of_budget` now accepts any
  `0 < a <= b` together with a natural budget `L` satisfying `1/a^2 <= L`;
  its input schedule is explicitly `(n+1)*L`.
  The companion `reciprocal_scale_kernel_eq_logTwoKernel` and
  `reciprocal_scale_point_positive` lemmas check the exact multiplicative
  normalization on `[a,2a]`, including positivity of the transformed points.
  The new `logTwoKernel_shift_eq_oneOverX` and
  `logTwo_rightRiemann_term_as_oneOverX` lemmas make the affine transport
  explicit at the finite rational level, before any general positive-interval
  endpoint theorem is attempted.
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
- The first proved power-series brick is formal: coefficient shift fixes the
  stream `1/n!`. See
  `FormalPowerSeries.expCoeff_derivative` in
  `ComputableAnalysis/PowerSeries.lean`.
- The same formal layer now covers the coefficient-shift identities for trig
  and hyperbolic streams:
  `sin -> cos`, `cos -> -sin`, `sinh -> cosh`, and
  `cosh -> sinh`.
  See `FormalPowerSeries.sinCoeff_derivative`,
  `FormalPowerSeries.cosCoeff_derivative`,
  `FormalPowerSeries.sinhCoeff_derivative`, and
  `FormalPowerSeries.coshCoeff_derivative`.
- The finite rational bridge below the formal table is now checked too:
  `FinitePolynomial.powerSecant_eq_differenceQuotient` identifies the exact
  quotient of every monomial, and
  `FinitePolynomial.qabs_normalized_power_differenceQuotient_sub_monomial_le`
  bounds the quotient of `x^(n+1)/(n+1)` against `x^n` by an explicit
  `|h|` coefficient on a supplied bounded box.  This avoids any mean-value
  theorem and is the direct finite algebra needed for the exponential tail.
  `FinitePolynomial.normalizedMonomial_hasDerivativeOnInterval` now packages
  that bound as a two-sided rational interval derivative certificate, with a
  computed dyadic step schedule, on every interval contained in `[-C,C]` for
  `C >= 1`. `FinitePolynomial.integratedTaylorPrefix_hasDerivativeOnInterval`
  closes the same explicit remainder calculation under every finite rational
  Taylor prefix. The exact finite FTC endpoint recurrence
  `FinitePolynomial.integratedTaylorPrefix_endpointDifference_succ` records
  how adjoining one integrated monomial changes the endpoint difference; it
  is a rational telescoping identity, not an appeal to a completed integral.
  The blueprint keeps these finite-difference derivative
  certificates in the later calculus chapter; the series chapter records only
  coefficient-shift data.
- Next theorem for `exp.ps`: turn the formal coefficient identity plus
  rational tail bounds and a translated-series/addition estimate into an
  effective derivative certificate for the boxed algorithm on an interval,
  hence a witness for
  `exp.ExponentialFunction.SolvesSelfDerivativeOn`.  This can be specialized
  to exponential first; a general term-by-term differentiation theorem can
  come later.
- To prove equality of the three exponential representations by calculus
  rather than by ad hoc estimates, use the scalar equation `f' = f` with
  `f(0) = 1` and the direct finite-mesh route in
  `ComputableAnalysis/ScalarODEUniqueness.lean`. Its checked closure turns a
  rational envelope with `B_(r+1) <= B_r/2` into zero error by an executable
  dyadic stage; `SelfDerivativeDirectMeshComparison` then gives function
  agreement. The remaining analytic theorem derives that envelope by
  subtracting two derivative certificates on short rational blocks and
  chaining finitely many blocks. This is intentionally independent of
  Peano--Baker/Picard iteration. The vector linear theorem and a future
  nonlinear interval-Lipschitz theory remain separate constructive
  existence-and-uniqueness data.

## Linear Differential Equations

**Benchmark item 97 — finite Cramer core checked.**
`cramer_two_by_two` proves the rational (2\times2) Cramer rule under a
nonzero determinant. It is placed here as the finite linear-algebra
prerequisite, and `cramer_two_by_two_unique` proves that every rational
solution agrees with the determinant quotients; general matrix dimensions and
continuous ODE identification are separate milestones.
The worked `FiniteThreeByThreeCramerExample` adds the diagonal system
`diag(2,3,4)u=(4,9,16)`: determinant `24`, inverse witness `1/24`, and exact
solution `(2,3,4)` are all checked.
The non-diagonal 3-by-3 instance with matrix `[[2,1,0],[0,3,1],[1,0,2]]`
and right-hand side `(4,9,7)` has determinant `13`; Lean checks the inverse
witness `1/13`, recovers `(1,2,3)`, and verifies the system through the
generic Cramer solver.
The additional two-by-two witness uses
`[[3,2],[1,2]](2,3)=(12,8)`: its determinant is `4`, and the Cramer
quotients recover `(2,3)` exactly.
The signed two-by-two witness `[[1,-2],[3,4]](16/5,-9/10)=(5,6)` has
determinant `10`; Lean checks both nonintegral Cramer quotients and direct
substitution.  This extends item 97's finite rational coverage beyond
positive-integral examples.

**Benchmark item 49 — finite Cayley--Hamilton core checked.**
The 3x3 matrix-power recurrence is now also checked for every natural stage
and every explicitly supplied rational matrix. It is obtained by multiplying
the finite 3x3 Cayley--Hamilton identity by a finite matrix power; arbitrary
dimensions remain deferred.
`LinearODE.twoByTwo_cayley_hamilton` proves the Cayley--Hamilton identity for
an explicit rational (2\times2) matrix by finite entrywise calculation.
The finite `HarmonicOscillator.threeByThree_cayley_hamilton` certificate now
checks the corresponding explicit (3\times3) identity using the trace, second
characteristic coefficient, and determinant.  The companion
`ThreeByThreeLinearAlgebra.threeByThree_cramer_solves` now packages the
explicit (3\times3) Cramer solve from those determinant numerators whenever an
inverse-determinant witness is supplied; its
`threeByThree_cramer_solves_of_determinant_ne_zero` corollary constructs that
witness canonically from a nonzero determinant.
`LinearODE.ratMatrix_twoByTwo_matrixPow_recurrence_unique` now adds the finite
uniqueness certificate: any rational matrix sequence with the same first two
terms and the induced trace/determinant recurrence agrees stage by stage with
the matrix-power sequence. Arbitrary dimensions and an abstract
characteristic-polynomial interface remain deferred.
The new `concreteFourCayleyCertificate` supplies a checked 4x4 diagonal
annihilator for `diag(1,2,3,4)` with polynomial
`x^4 - 10*x^3 + 35*x^2 - 50*x + 24`. This extends the finite-dimensional
exercise without introducing a determinant construction.

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
- The blueprint now fixes the vector chapter's proof direction: start from the
  forced second-order oscillator, turn it into the general affine vector
  equation `x' = A(t)x + b(t)`, construct Peano--Baker plus Duhamel boxes for
  that general problem, and prove uniqueness by iterating the zero-initial
  Volterra identity until the factorial estimate is below an arbitrary
  rational tolerance. This recovers sine/cosine and the vector rotation
  route. Scalar `E' = E`, `E(0) = 1` uses direct mesh contraction instead;
  after its presentation-agreement theorem, the positive inverse is the
  canonical logarithm used by the long arctangent integration-by-parts Pi
  route. These are named dependency chains, not extra Pi-scoreboard rows.
- Next analytic target: build interval matrices for ordered-simplex
  Peano--Baker terms, prove a factorial tail enclosure from a rational
  coefficient bound, and obtain state-transition and variation-of-constants
  formulas for `x' = A(t)x + b(t)`. Together these are the effective linear
  Picard--Lindelöf theorem: the zero-initial homogeneous case gives
  uniqueness, and the factorial tail is the explicit solution modulus. The
  next specializations are the analytic commuting-exponential identification,
  scalar and piecewise-constant systems, and higher-order
  nilpotent/triangular systems. The scalar `f'=f` exponential route is
  already specified separately by direct mesh contraction. Chapter `Linear
  Differential Equations` gives the vector certificate plan.

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
  stages `10`, `100`, and `1000`.  The new
  `ComplexPathIntegral.PolygonalIntegralCertificate` and
  `ComplexPathIntegral.polygonalIntegralRawEntire_valid` make the validity
  boundary explicit: ordered boxes, stage nesting, and potential-infinity
  width shrinkage must be supplied as finite certificates before the raw
  algorithm is promoted to a valid represented complex number.
  The finite displacement identities
  `ComplexPathIntegral.polygonalDisplacementTo_append_endpoint` and
  `ComplexPathIntegral.polygonalDisplacementTo_closed` now provide the exact
  endpoint-cancellation seed for closed polygonal paths, still entirely in
  rational complex arithmetic.
  The constant-differential lift
  `ComplexPathIntegral.polygonalConstantDifferentialDisplacement_append_endpoint`
  identifies the finite primitive value `c * (z_end - z_start)`, and
  `polygonalConstantDifferentialDisplacement_closed` proves its closed-path
  cancellation exactly.
  The quadratic primitive layer
  `ComplexPathIntegral.polygonalQuadraticPrimitiveTo_append_endpoint` and
  `polygonalQuadraticPrimitiveTo_closed` extends this to the polynomial
  differential `z dz`, whose primitive is `z^2 / 2`, using only finite
  rational-complex identities.
  The general finite monomial extension
  `ComplexPathIntegral.polygonalMonomialPrimitiveTo_append_endpoint` and
  `polygonalMonomialPrimitiveTo_closed` covers `z^n dz` with the executable
  natural power and primitive `z^(n+1)/(n+1)`. This is an algebraic finite
  schema, not a claim about an infinite analytic power function.
  The coefficient-list evaluator
  `ComplexPathIntegral.polynomialPrimitiveEval` and its path fold
  `polygonalPolynomialPrimitiveTo` now package the same endpoint cancellation
  for every finite rational-complex polynomial primitive.

## Algebraic Numbers and FTA

**Benchmark item 89 — linear factor/remainder base case checked.**
The worked `FiniteRemainderExample` evaluates `x^2-3x+2` at the supplied root
`1` and sample point `4`, checking the exact value `6` through the quadratic
factor identity.
Its signed companion evaluates `x^2+3x+2` at root `-1` and sample point `-4`,
again obtaining `6` by the exact factor identity. This extends item 89's
worked rational coverage across negative inputs.
`Polynomial.linear_remainder`, `Polynomial.linear_factor_of_root`,
and `Polynomial.linear_root_iff_constant_eq_neg_mul`
`Polynomial.quadratic_remainder`, and
`Polynomial.quadratic_factor_of_root` provide exact rational degree-one and
degree-two base cases. The cubic remainder/factor pair
`Polynomial.cubic_remainder`/`Polynomial.cubic_factor_of_root` supplies the
rational-root reduction step for benchmark item 37. The worked identity
`Polynomial.cubic_example_factorization` and its checked roots
`Polynomial.cubic_example_roots` provide an explicit rational cubic solution
example within that boundary, while `Polynomial.cubic_example_root_iff`
checks that these are all of its rational roots. More generally,
`rationalCubicPolynomial` and `rationalCubic_has_computable_roots` now package
the three-root factorized cubic interface in the FTA layer as well.
The named complex factorization now also has the exact root-set theorem
`factorizedCubicPolynomial_eval_eq_zero_iff`: a zero is precisely one of the
three supplied rational-complex roots.  This is a finite exclusion certificate
for the cubic core of item 37, not a general cubic formula.
The public exact-root form `factorizedCubicPolynomial_hasExactRoot_iff` exposes
the same three-way characterization without requiring clients to unfold
evaluation.
The new `Polynomial.quadratic_eval_root_of_discriminant` and
`Polynomial.cubic_completion_roots_of_discriminant` theorems complete the
finite supplied-root cubic boundary: a rational discriminant square witness
produces both remaining rational roots. The construction of the initial root
or square witness remains separate algorithmic work.
The worked `FiniteCubicCompletionExample` now instantiates that boundary for
`x^3 - 6x^2 + 11x - 6`: with supplied root `1` and discriminant square
witness `1`, Lean computes and checks the remaining roots `2` and `3`.
The new `FiniteCubicSqrtTwoExample` connects the same cubic boundary to a
non-rational residual branch: `x^3-x^2-2x+2=(x-1)(x^2-2)`, with the exact
root `1` and a finite sign bracket for the `sqrt 2` branch on
`[11/8,23/16]`.
The same cubic branch now consumes the stage-24 square-root enclosure
`[11863283/8388608,23726567/16777216]`, preserving the exact sign bracket
with a much finer rational width.
The parallel `rationalQuarticPolynomial` interface packages four exact
rational roots and their computable witnesses, strengthening the checked
factorized core of benchmark item 46 without claiming a general quartic
formula.
The new `FiniteQuarticSqrtTwoExample` adds the irrational branch: it checks
`x^4-3*x^2+2=(x^2-1)(x^2-2)`, exact roots `-1,1`, and both signed endpoint
brackets for the finite `sqrt 2` enclosure.
The same quartic now consumes the stage-24 `sqrt 2` enclosure and checks both
positive and negative signed endpoint brackets at that finer precision.
The supplied complex-factor quartic now also has the exact root-set theorem
`factorizedQuarticPolynomial_eval_eq_zero_iff`, giving finite exclusion for
every candidate outside the four supplied roots.
The matching exact-root interface
`factorizedQuarticPolynomial_hasExactRoot_iff` packages that four-way result
for computable-root consumers.
The checked worked examples `Polynomial.quartic_example_factorization` and
`Polynomial.quartic_example_roots` supply four rational roots for a quartic,
while `Polynomial.quartic_example_root_iff` checks that these are all of its
rational roots. Together they cover the project's rational worked-example core
of benchmark item 46; the general quartic formula remains outside the current
boundary.
The worked `FiniteQuarticSplitExample` now instantiates the two-quadratic
interface with factors `z^2 - 1` and `z^2 - 4`, checking all four rational
roots `-2`, `-1`, `1`, and `2` in the finite rational-complex model. The
general Ferrari resolvent remains outside the boundary.
The new `FiniteMixedCubicExample` supplies the conjugate pair `i,-i` together
with the real root `1` for `(z-1)(z-i)(z+i)=z^3-z^2+z-1`. Lean checks both the
coefficient expansion and all three exact root evaluations, extending the
finite cubic/FTA boundary to a mixed real/complex example.
The scaled companion example checks
`(z-2)(z-2i)(z+2i)=z^3-2z^2+4z-8`, including the real root `2`, conjugate
roots `2i,-2i`, coefficient expansion, and all three exact evaluations.
The companion `FiniteQuarticMixedSplitExample` uses `z^2 + 1` and `z^2 - 4`,
checking the nonreal rational-coordinate roots `i` and `-i` alongside `2` and
`-2`. This extends the finite quartic boundary to a mixed real/complex split
without adding a general quartic formula or algebraic-closure claim.
The scaled mixed quartic companion uses `z^2 + 4` and `z^2 - 9`, checking the
four supplied roots `2i,-2i,3,-3` and exact evaluations through the same
two-quadratic split interface.
The optional Descartes route now has a finite `Polynomial.signChangeCount`
counter, a zero-filtered variant, the general zero-variation lemma
`signChangeCountIgnoringZeros_zero_of_nonneg_coeffs`, a general quadratic sign-pattern theorem,
the nonnegative/nonpositive-coefficient evaluation lemmas, and checked
examples.  The strict positive-input theorem
`eval_pos_of_nonneg_coeffs_of_pos` supplies a direct positive-ray root
exclusion; the root-counting rule itself is not yet claimed.
The packaged `eval_ne_zero_of_nonneg_coeffs_of_pos` form is available for
direct root-search use; `no_positive_root_of_nonneg_coeffs_of_pos` packages
the same fact as an existential root-exclusion certificate; and
`eval_neg_of_nonpos_coeffs_of_neg` supplies the strict negative dual.
`no_positive_root_of_nonpos_coeffs_of_neg` packages that dual as an
existential root-exclusion certificate as well. The sign-symmetric zero-variation lemma
`signChangeCountIgnoringZeros_zero_of_nonpos_coeffs` is also checked.
The degree-independent finite extension now adds
`eval_nonincreasing_of_nonpos_coeffs` and
`eval_strictly_decreasing_of_nonpos_tail`. Consequently,
`at_most_one_positive_rational_root_of_nonpos_tail` proves uniqueness of a
positive rational root for any finite coefficient list with a positive
constant term and a nonpositive, nonzero tail. The accompanying
`signChangeCountIgnoringZeros_one_of_pos_cons_nonpos_tail` identifies the
single sign variation after zero filtering. This is a finite one-variation
Descartes certificate, now packaged directly as
`Polynomial.one_positive_variation_certificate`; it is not the unrestricted
classical root-counting theorem.
The exact two-variation example now records that \(x^2-3x+2\) has sign count
two and positive rational root set exactly \(\{1,2\}\). This is a finite
Descartes example for item 100, not a claim of the general real-root-counting
theorem.
The new one-variation example `1 - 2x - x^2` has sign count one, a finite
positive-root bracket `[3/8,1/2]`, and a certificate that any two positive
rational roots must coincide. This adds a non-rational-root-shaped test of the
finite Descartes boundary without claiming classical real root existence.
The companion `Polynomial.zero_variation_root_exclusion_certificate` now
packages the zero-variation count with the corresponding positive-root
exclusion whenever the finite list has nonnegative coefficients and a
strictly positive supplied coefficient.
The arbitrary finite-list combinatorial bound
`Polynomial.signChangeCountIgnoringZeros_add_one_le_filter_length` now records
that the zero-filtered sign-change count is at most the coefficient-list
length minus one. This is the finite combinatorial component of item 100;
general root counting remains deferred.
`Polynomial.syntheticDivide_spec` and
`Polynomial.syntheticDivide_factor_of_root` provide linear factor/remainder
certificates for arbitrary finite rational coefficient lists, and
`Polynomial.syntheticDivide_remainder_eq_eval` identifies the remainder with
evaluation at the chosen point, while
`Polynomial.syntheticDivide_remainder_eq_zero_iff` exposes the equivalent
zero-remainder root test. The new finite
`RationalRootSearch.rationalRootSearch` scans supplied rational candidates,
with soundness, candidate-list completeness, and a
`RemainderCertificate`-packaged result. This gives items 37 and 89 an
executable rational-root interface without asserting that an arbitrary
polynomial has a rational root. Division by higher-degree factors and
closed-form cubic solving remain future algebra infrastructure.
The general finite identity `Polynomial.syntheticDivide_secant_quotient`
identifies the nonzero-step secant quotient of any finite rational polynomial
with its synthetic quotient evaluated at the right endpoint. This supplies a
reusable finite secant/Taylor bridge without asserting a limiting theorem.
The finite coefficient derivative identities
`Polynomial.derivativeEval` and
`Polynomial.pow_mul_eval_zipIdx_eq_derivativeEvalAux` expose the exact
power-weighted indexed coefficient identity, while
`Polynomial.eval_derivative_eq_derivativeEval` now provide the generic
recursive coefficient-level derivative evaluator; the named identities
`Polynomial.eval_derivative_linear`,
`Polynomial.eval_derivative_quadratic`, and
`Polynomial.eval_derivative_cubic`,
and the new `Polynomial.quadratic_secant_quotient` and
`Polynomial.quadratic_secant_minus_derivative` expose the exact finite
quadratic difference quotient and its rational step error.  This is the
computable MVT content used before any claim about an attained intermediate
point.
`Polynomial.eval_derivative_quartic`, and
`Polynomial.eval_derivative_quintic`,
`Polynomial.eval_derivative_sextic`, and
`Polynomial.eval_derivative_septic` now connect the coefficient-level
derivative list back to pointwise evaluation through degree seven.
They support the finite Taylor boundary without asserting a general analytic
derivative theorem.
The rational-function wrapper is now also closed for polynomial numerators:
`RatFun.polynomial_defined_all` certifies its denominator everywhere, and
`RatFun.polynomial_evalOnDomain_eq` identifies the domain evaluation with
`Polynomial.eval`. The packaged interval evaluator
`RatFun.polynomialOnInterval` and its exact computation theorem
`RatFun.polynomialOnInterval_compute_eq` make this a reusable
interval-function certificate.

- The algebraic-number layer is now proof-honest: exact rational-complex
  algebraic numbers and exact roots of unity are formalized, while arithmetic
  closure and algebraic closure are explicit targets rather than theorem
  placeholders.  See `AlgebraicComplex.MulRawValid`,
  `AlgebraicComplex.add_annihilator_exists`,
  `AlgebraicComplex.neg_annihilator_exists`,
  `AlgebraicComplex.mul_annihilator_exists`,
  `AlgebraicComplex.inv_exists`, and `AlgPoly.exists_root`.
- The four-corner product is now a certified raw operation.  The finite
  containment/order/refinement facts are `QBox.mulRealInterval_contains`,
  `mulRealInterval_ordered`, `mulRealInterval_nested`, `QBox.mul_contains`,
  `mul_ordered`, and `mul_nested`.  The checked width bound
  `QBox.mulRealInterval_width_le_of_abs_bounded`, lifted by
  `mul_width_height_le_of_coordinateBounded`, uses the explicit stage-zero
  coordinate radii to prove `ComplexRaw.mul_valid`.  The finite-intersection
  proof `QBox.mul_overlaps_of_overlaps` gives `ComplexRaw.mul_equiv`, so this
  product is representation-safe.  Consequently
  `AlgebraicComplex.mulRaw_valid` has discharged the former raw-validity
  premise; resultant-style rational polynomial transformations remain the
  actual addition, negation, and multiplication-annihilator targets.
- The important Euler-route exact-scalar implementation is also checked:
  `ComplexRaw.qcomplexLeftMul` gives every rational complex
  scalar a validity- and equivalence-preserving affine action on a certified
  complex raw.  Its `i` specialization is the direct coordinate rotation
  `ComplexRaw.mulI`, and `ComplexRaw.imaginaryAxis` embeds any certified real
  as the certified complex handle \(ix\).  Thus the selected raw \(\pi\)
  `ComplexRaw.qcomplexLeftMul_ofQComplex` now agrees with ordinary finite
  `QComplex` multiplication on exact rational inputs.  The stagewise and
  represented `imaginaryUnit` certificates likewise identify affine
  multiplication by (i) with the direct coordinate rotation.  This is the
  finite rational-coordinate bridge for item 17; it does not identify a
  represented exponential with a completed complex exponential.
  already yields the valid bounded real input `PiProofs.pi.halfPi`, whose
  boxes stay in \([1,2]\), and a valid raw \(i\pi/2\) both by rational
  scaling and as the literal exact \(i/2\)-scalar action.  The return scalar identity
  \((-2i)(i\pi/2)=\pi\) is now available both as an exact stagewise affine
  theorem and as the general-product theorem
  `PiProofs.pi.negativeTwoImaginaryRaw_mul_imaginaryHalf_equiv_piCircleArea`.
  `PiProofs.pi.LogAtICertificate` isolates the remaining
  branch-specific input: any valid complex logarithm raw agreeing with
  \(i\pi/2\) now immediately yields the certified complex formula
  \(-2i\log(i)=\pi\), both through the affine action and as the literal
  `negativeTwoImaginaryRaw * logI.raw` product.  This does not yet extend the factorial-series
  exponential to represented complex inputs or establish Euler's identity.
  The generic last assembly step is now present as
  `ComplexRaw.cauchyStabilize_valid`: finite intersections of widened direct
  complex candidates become a valid raw box computation when every later
  candidate is contained in every earlier widened box.  Those factorial-tail
  and input-modulus obligations are now discharged for `halfPi`:
  `PiProofs.pi.halfPiRotation` is valid, using the common bounded-input
  rotation schedule, its finite Lipschitz bound, and a radius at most
  `32 / (n + 1)`.  The input is also bridged to
  `2 * arctan.geom(1)` and the geometric normalized quarter-turn raw.
  `halfPi_equiv_geometricHalfPi` and
  `imaginaryHalf_equiv_geometricImaginaryHalf` now carry this agreement to
  the geometry-only represented half angle and its imaginary-axis input.
  `RotationLift.HalfPiInput.rotation_equiv_of_input_equiv` now transports
  equivalent half-angle raws through the separately stabilized factorial
  rotations using a cross radius at most `64 / (n + 1)`, and
  `halfPiRotation_equiv_geometricRotation` specializes that result to the
  registry and geometry-only constructions.  The remaining Euler work is the
  sector-area reparametrization and vector-uniqueness identification of that
  rotation with the geometric endpoint, followed by the relevant logarithm
  branch certificate.
  The geometry-only implementation is now indexed separately as
  `GeometricPiRotation`: its cofinal rational half-pi schedule has certified
  bounds and width modulus, is equivalent to the normalized quarter-turn, and
  feeds a valid finite-prefix-stabilized factorial rotation with ordered
  candidates.  This is an algorithmic strengthening of the Euler/rotation
  target, not a completed-real theorem; endpoint identification and the
  logarithm branch remain open.
  The rational chart side is now a checked variable-coefficient
  rotation-system candidate:
  `GeometricRotationODE.pointOnUnit_geometricRotationSystemCertificate` gives
  `P' = (2 i / (1+t*t)) P`, `P(0)=1`, and `P(1)=i` on `[0,1]`.
  The scalar sector-time component is now checked as well:
  `SectorAreaReparametrization.angleOnUnit_hasDerivative` gives
  `Theta' = 2/(1+t*t)`, and
  `angleAt_equiv_two_arctanGeom` identifies every rational chart value with
  `2 * arctan.geom(t)`.  The finite lower-tail comparison now also gives
  `angleOnUnit_effectiveInverseSeparation`: an input gap `1/(n+1)` produces
  strictly separated output boxes at stage `64*(n+1)`.
  The same finite certificate is now exposed directly on the unscaled
  rectangle function as
  `IntegralIdentities.arctanIntegralRectangleOnUnit_effectiveInverseSeparation`,
  keeping the separation modulus attached to the evaluator that produced the
  boxes.  This is an inverse-search prerequisite, not an inverse theorem.
  `angleOnUnitRegular_intervalRegular` now gives the matching finite
  interval-image certificate through the cofinal `64*(n+1)` schedule, and
  `angleOnUnitRegular_invertible` packages it with monotonicity and effective
  separation as the prerequisites for a constructive inverse branch.  The remaining
  reparametrization work is the data-valued bisection search, then curve
  composition and the vector uniqueness theorem, not the derivative,
  interval regularity, or strict monotone separation of the sector-area
  clock.
  The corresponding endpoint has now been transported as well:
  `PiProofs.pi.sectorAreaAngleOne_equiv_halfPi` proves
  `Theta(1) ≡ pi/2` by the checked geometric arctangent bridge.
  Independently of the pi registry,
  `SectorAreaRotation.halfPi` packages the accelerated endpoint as a bounded
  factorial-rotation input: every rectangle box is checked in `[1,2]` from
  the kernel bounds, its width modulus is explicit, and
  `SectorAreaRotation.rotation_equiv_geometricRotation` transports the
  resulting stabilized rotation to the geometry-only rotation.  The remaining
  Euler endpoint gap is therefore the stated reparametrized rotation-system
  uniqueness theorem, rather than a disagreement between angle inputs.
  `PiProofs.pi.halfPiRotation_equiv_sectorAreaRotation` also records the
  transitive connection back to the project-level pi handle.
  Its imaginary-axis input has the matching transport
  `PiProofs.pi.imaginaryHalf_equiv_sectorAreaRotationImaginaryHalf`.
  `PiProofs.pi.sectorAreaPiRaw_equiv_piCircleArea` doubles that endpoint to a
  direct pi raw and transports it to the preferred circle-area representation;
  it is intentionally a named alternate computation rather than a new
  coverage score.

## First-Year Calculus Course

The course layer should avoid broad classical theorem dependencies such as IVT
and MVT.  Instead, it should grow a concrete table of functions, domains,
derivatives, and definite integration algorithms that covers the examples
students actually compute.

- New course module: `ComputableAnalysis/FirstYearCalculus.lean`.
- Checked formal coefficient-shift table:
  monomials `x^(n+1)/(n+1)`, `exp`, `sin`, `-cos`, `sinh`, and `cosh`.
  See `FirstYearCalculus.PowerSeriesDerivativeEntry` and
  `FirstYearCalculus.checked_power_series_table`.
- The monomial row also has an executable finite-secant estimate, independent
  of the formal stream: see
  `FinitePolynomial.normalizedMonomial_hasDerivativeOnInterval`.
- Linear closure for the table is now available at the formal coefficient
  level.  The primary declarations are
  `FormalPowerSeries.coefficientShift_add`,
  `FormalPowerSeries.coefficientShift_scaleRat`,
  `FormalPowerSeries.hasCoefficientShift_add`, and
  `FormalPowerSeries.hasCoefficientShift_scaleRat`; their older
  formal-derivative counterparts remain compatibility API.
- Real-axis wrappers for concrete functions are named:
  `FirstYearCalculus.RealElementary.expPS`, `sinPS`, `cosPS`,
  `sinhFromExp`, `coshFromExp`, `sqrtRat`, `invX`, and
  `invOnePlusSquare`.
- Rational-function kernels ready for calculus:
  `RatFun.oneOverOnePlusSquare_denominator_apart_on_interval` proves that
  `1/(1+x^2)` has denominator-apartness bound `1` on every rational interval,
  and `RatFun.oneOverX_denominator_apart_on_pos_interval` proves that `1/x`
  is denominator-apart on every interval `[a,b]` with `0 < a`.  The symmetric
  `RatFun.oneOverX_denominator_apart_on_neg_interval` now covers intervals
  with `b < 0`; `oneOverXOnPositiveInterval` and
  `oneOverXOnNegativeInterval` expose both branches as certified interval
  functions with exact computation theorems, while
  `RatFun.oneOverX_defined_of_ne_zero` gives the general pointwise domain
  criterion, while `RatFun.eval?_eq_some_of_defined` and
  `RatFun.eval?_eq_none_of_undefined` expose the executable evaluator's
  success/failure behavior. The pole at zero remains explicitly excluded.
- Next concrete integral targets, beyond the checked unit-branch arctangent
  rectangle/Lipschitz comparison and without a general integrability theorem:
  `integral 1/x = log x` on positive intervals,
  `integral 1/(1+x^2) = arctan x` on general certified branch intervals,
  the half-period sine endpoint `π * integral_0^(1/2) sin(π t) dt = 1`,
  using interval-valued alternating-series sine evaluations rather than exact
  samples,
  `integral 1/sqrt(1-x^2) = asin x` on certified subintervals of `[-1,1]`,
  tangent/secant formulas on intervals whose cosine denominator is apart from
  zero, and polynomial/rational examples via domain-specific interval
  certificates.

  The new `FiniteSineIntegral` module begins the half-period route with the
  finite primitive `halfAnglePrefix`: after substituting `u = pi*x`, it is
  the rational Taylor-prefix value at `u = piApprox/2`. The endpoint
  recurrence and stage-four/stage-six certificates are exact finite rational
  identities; the stage-six value is within `1/1000` of `1`. This is a
  computable prefix toward the normalized formula, not yet a completed
  integral or a claim that the rational approximation is exact pi.
  The same finite evaluator now reaches stages eight and ten, with explicit
  rational values within `1/10000` and `1/1000000` of `1`. These are sharper
  potential-infinity checkpoints, still not the completed sine integral.
- A later noncompact benchmark is the Dirichlet sinc integral
  `∫ sin(π t)/t dt = π`, using the project's rational-angle convention.  The
  first local illustration is its decreasing-then-increasing branch around
  the irrational solution of `tan(π t) = π t`.  This does not justify a
  special one-turn integral: the intended algorithm is a finite list of
  monotone pieces and shrinking rational turn brackets, followed by a
  separately certified oscillatory tail cancellation.  No sine/tangent
  sign-bisection certificate or full-line sinc integral is checked yet.
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
The specialized
`Taylor.ArctanKernel.finite_remainder_half_interval_budget` now supplies an
executable schedule on `0 <= x <= 1/2`: stage `n` has remainder at most
`1/(n+2)`, obtained by a rational half-power comparison. This is the first
explicit stage selector for the Taylor remainder route and remains entirely
finite.
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
  Peano--Baker uniqueness theorem.  Its rational imaginary-axis factorial
  tail is now a valid complex raw (`RotationSeries.rotationExpRaw_valid`),
  while rotation/geometric and branch bridges remain. The primary gates remain
  the
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
- The reusable finite-Riemann bridge now covers every rational input on the
  series chart `|x| <= 1`:
  `arctanEqualsGeom_finiteRiemannBridge_on_unit`, with presentation-level
  certificate `arctanPowerSeriesGeomAgreement_finiteRiemannBridge`.  Its
  nonnegative core remains `arctanEqualsGeom_finiteRiemannBridge`; the
  negative half follows from the literal raw-interval negation implemented by
  both evaluators.  The canonical scoreboard deliberately uses this one
  capability only for the Leibniz endpoint and the two power-series inputs in
  the single Machin formula; this extension is not an additional pi
  computation.
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
- The finite Leibniz evaluator now has an explicit stage-80 checkpoint:
  `piLeibniz_stage80_enclosure` keeps the rational interval inside `[3,16/5]`,
  while `piLeibniz_stage80_width` certifies width at most `1/80`.  This is a
  stronger finite error budget for the project’s computable series route.
The same evaluator now also exports stage 160, keeping the interval inside
`[3,16/5]` with width at most `1/160`.
It now also exports stage 320, keeping the same rational enclosure with width
at most `1/320`, extending the finite item-26 precision ladder.
It now also exports stage 640, keeping the same rational enclosure with width
at most `1/640`, extending the finite item-26 precision ladder.
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
- `BaselFiniteComparison.baselCommonInterval_certificate` strengthens the
  finite cross-check at stages 10,000 and 8: it constructs an explicit
  nonempty rational intersection contained in both independent enclosures.
  This is a reusable finite comparison certificate, still deliberately short
  of the completed Basel identity.
- `BaselFiniteComparison.baselCommonInterval_width_le` records the precision
  consequence: the common interval is no wider than either source enclosure,
  so both finite error budgets transfer to the shared comparison object.
- `BaselFiniteComparison.baselCommonInterval_midpoint_certificate` extracts
  an explicit rational midpoint lying in both source enclosures, providing a
  concrete finite witness for the cross-evaluator comparison.
- `BaselFiniteComparison.baselRefinedCommonInterval_certificate` repeats the
  comparison at the tighter stages 100,000 and 10, with an explicit common
  rational interval.  `baselRefinedCommonInterval_width_le` transfers both
source precision budgets to that refined object.  This strengthens the
finite benchmark evidence without claiming the infinite Basel identity.
  `baselRefinedCommonInterval_midpoint_certificate` additionally exports a
  concrete rational witness lying in both refined enclosures.
The new `baselHighCommonInterval` repeats the independent comparison at zeta
stage `200000` and geometric stage `12`, with a certified nonempty
intersection and inherited width bounds. This deepens the finite Basel
cross-check while keeping Euler's identity itself deferred. The new
`baselHighCommonInterval_midpoint_certificate` exports an explicit rational
midpoint in both highest-stage enclosures.
The named `FiniteBaselComparisonExample` packages the earlier stage-10000/
stage-8 midpoint as a reusable rational witness and carries forward both
source width bounds.
The worked `FiniteBaselExample` now also supplies a refined executable
certificate with `epsilon = 1/10000` at stage `10001`, retaining containment
of stage `100000` and tightening the finite width budget by a factor of ten.
It now also contains stage `200000` under the same `1/10000` width budget,
extending the finite potential-infinity schedule while leaving the Basel
identity deferred.
The named stage-16 checkpoint additionally records the exact partial sum
`822968714749/519437318400` and its explicit `1/16` tail interval.

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
  The exact identity `Differential.square_midpoint_mean_value` additionally
  gives the rational square-function secant slope at the midpoint, a finite
 Mean Value Theorem core for benchmark item 75.  The new
 `Differential.quadratic_midpoint_mean_value` generalizes this exact witness
 to every rational quadratic `c₀+c₁x+c₂x²`, with the same midpoint witness.
The worked `FiniteCubicMVTExample` adds the exact cubic interval witness:
the secant slope of `x^3` on `[0,1]` is `1`, decomposed as midpoint derivative
value `3/4` plus finite remainder `1/4`.
  The companion `ExactFunction.affine_differenceQuotient` proves the exact
  constant slope of every rational affine secant, supplying the corresponding
  finite base case.
  `ExactFunction.affine_root_of_nonzero_slope` also gives the exact rational
  zero of every nonconstant affine function, a finite root-search base case
  for benchmark item 79.
  Its positive-slope companion
  `ExactFunction.affine_root_between_of_sign_change` proves that this zero
  lies inside a certified endpoint sign-change bracket.
  The corresponding negative-slope orientation is checked by
  `ExactFunction.affine_root_between_of_negative_sign_change`.
`ExactFunction.cube_differenceQuotient` adds the exact rational cubic secant
expansion used by the finite Taylor/polynomial layer.
`Differential.cube_midpoint_secant` rewrites that cubic secant around the
interval midpoint, adding an explicit quadratic remainder certificate for the
finite Mean Value/Taylor route.
The companion `Differential.quartic_midpoint_secant` extends the same exact
midpoint expansion to degree four.
`Differential.quintic_midpoint_secant` completes the corresponding degree-five
finite midpoint expansion.
`Differential.sextic_midpoint_secant` extends the same centered finite
secant decomposition through degree six, with the explicit fourth-power
remainder term.
  `ExactFunction.quartic_differenceQuotient` checks the analogous quartic
  expansion as the next finite monomial case.
  `ExactFunction.quintic_differenceQuotient` extends the same exact secant
  family through degree five. The new
  `ExactFunction.sextic_differenceQuotient` carries the exact finite secant
  expansion through degree six, matching the sextic polynomial bracket layer.
  `ExactFunction.square_quotient_by_id` and
  `ExactFunction.cube_quotient_by_id` add finite quotient-cancellation support
  for the optional L'Hôpital layer (benchmark item 64), without claiming a
  limit theorem.  The reusable
  `ExactFunction.power_succ_quotient_by_id` generalizes this cancellation to
  every natural power, and `ExactFunction.power_succ_quotient_by_power`
  cancels the full nonzero power denominator `x^n` in
  `x^(n+1)/x^n = x`; the reusable
  `ExactFunction.power_add_quotient_by_power` proves
  `x^(m+n)/x^m = x^n`. No limiting theorem is claimed.
  `Differential.cubic_linear_factored_quotient_derivative_ratio` adds the
  cubic common-factor identity
  `(x^3-a^3)/(x-a)=3*a^2+3*a*(x-a)+(x-a)^2`, extending the finite algebraic
  L'Hôpital boundary without introducing a limit theorem.
The quartic worked certificate now records the residual
`6*step + 4*step^2 + step^3` after cancelling the common linear factor from
`x^4 - 1`, together with its reciprocal-stage form. This extends item 64's
finite cancellation ladder without introducing an attained limit.
The quintic worked certificate now records the residual
`10*step + 10*step^2 + 5*step^3 + step^4` after cancelling the common factor
from `x^5 - 1`, together with its reciprocal-stage form.
The sextic worked certificate now records the residual
`15*step + 20*step^2 + 15*step^3 + 6*step^4 + step^5` after cancelling the
common factor from `x^6 - 1`, together with its reciprocal-stage form.
The septic worked certificate now records the residual
`21*step + 35*step^2 + 35*step^3 + 21*step^4 + 7*step^5 + step^6` after
cancelling the common factor from `x^7 - 1`, extending item 64's finite
cancellation ladder without introducing a limit theorem.
  The scalar-weighted companion
  `ExactFunction.mul_power_add_quotient_by_power` cancels the same nonzero
  power inside `y*x^(m+n)/x^m = y*x^n`, making the certificate compositional
  for endpoint and affine factors.
  The scaled-denominator extension
  `ExactFunction.mul_power_add_quotient_by_scaled_power` also cancels a
  nonzero scalar factor in the denominator, yielding
  `(y*x^(m+n))/(z*x^m) = (y/z)*x^n` under explicit nonzero hypotheses.
  The new `Polynomial.finiteDerivativeEval` together with its public Horner
  recurrence `Polynomial.finiteDerivativeEval_cons` and exact linear and
  quadratic base cases `Polynomial.finiteDerivativeEval_linear` and
  `Polynomial.finiteDerivativeEval_quadratic` and
  `Polynomial.finiteDerivativeEval_cubic`,
  `Polynomial.finiteDerivativeEval_quartic`, and
  `Polynomial.finiteDerivativeEval_quintic`, and
  `Polynomial.finiteDerivativeEval_sextic`, and
  `Polynomial.finitePolynomial_secant_derivative_bracket` and its direct cubic
  specialization `Polynomial.finiteCubic_secant_derivative_bracket` and its
  quartic-through-sextic specializations
  `Polynomial.finiteQuartic_secant_derivative_bracket` and
  `Polynomial.finiteQuintic_secant_derivative_bracket`, together with the new
  `Polynomial.finiteSextic_secant_derivative_bracket`, assemble a finite
  endpoint secant bracket for any Horner polynomial with nonnegative rational
  coefficients on a nonnegative rational interval. The companion
  `Polynomial.finitePolynomial_secant_derivative_gap` turns that bracket into
  an explicit rational width budget for the secant error. This strengthens the
  finite core of benchmark item 75 without selecting an intermediate point or
  invoking a completed-real Mean Value Theorem.
  The named specialization `Polynomial.finiteCubic_secant_derivative_gap`
  now exposes the same budget directly in the cubic derivative formula used by
  the low-degree calculus examples.
  The new `Polynomial.finiteCubic_secant_derivative_gap_le` makes that budget
  explicit as `(2*c₂ + 6*c₃*b)*(b-a)`, so a requested rational tolerance can
  be converted directly into a mesh-width condition.
  The new `Polynomial.finiteQuintic_secant_derivative_gap_le` extends this
  explicit scheduler through degree five with budget
  `(2*c₂ + 6*c₃*b + 12*c₄*b^2 + 20*c₅*b^3)*(b-a)`.
  The new `Polynomial.finiteQuintic_secant_derivative_gap_le` extends this
  explicit scheduler through degree five with budget
  `(2*c₂ + 6*c₃*b + 12*c₄*b^2 + 20*c₅*b^3)*(b-a)`.
  The matching `Polynomial.finiteQuartic_secant_derivative_gap` and
  `Polynomial.finiteQuintic_secant_derivative_gap` declarations now carry the
  explicit budget through the quartic and quintic formulas as well. The new
  `Polynomial.finiteQuartic_secant_derivative_gap_le` makes the quartic budget
  explicit as `(2*c₂ + 6*c₃*b + 12*c₄*b^2)*(b-a)`.
  The new
  `Polynomial.finiteSextic_secant_derivative_bracket` and
  `Polynomial.finiteSextic_secant_derivative_gap` extend the same finite
  certificate one degree further, without changing the nonnegative-coefficient
  or rational-interval hypotheses.
  The new `Polynomial.finiteSextic_secant_derivative_gap_le` makes the degree-
  six mesh budget explicit as
  `(2*c₂ + 6*c₃*b + 12*c₄*b^2 + 20*c₅*b^3 + 30*c₆*b^4)*(b-a)`.
  The matching `Polynomial.finiteDerivativeEval_septic`,
  `Polynomial.finiteSeptic_secant_derivative_bracket`, and
  `Polynomial.finiteSeptic_secant_derivative_gap` extend the public finite
  endpoint certificate to degree seven, still using only rational coefficients
  and a finite endpoint comparison.
  The same finite interface now extends one step further to degree eight via
  `Polynomial.finiteDerivativeEval_octic` and
  `Polynomial.finiteOctic_secant_derivative_bracket`; this remains a rational
  endpoint enclosure rather than a completed-real Mean Value Theorem.
  It now also reaches degree nine, matching the worked `FiniteNonicMVTExample`,
  through `Polynomial.finiteDerivativeEval_nonic` and
  `Polynomial.finiteNonic_secant_derivative_bracket`.
  The new `Polynomial.monomialCoeffs`, `eval_monomialCoeffs`, and
  `finiteDerivativeEval_monomialCoeffs_succ` give the arbitrary-degree
  monomial version directly: the generated finite coefficient list evaluates
  to `x^n`, and its Horner derivative evaluates to `(n+1) * x^n`.
  `Polynomial.finiteSeptic_derivative_mono` additionally proves that the
  septic derivative evaluator is monotone on nonnegative rational intervals
  under the same coefficient certificate.
  The worked septic witness now also evaluates `x^7` on the shifted interval
  `[1,2]`: the finite secant is `127`, and the endpoint derivative bracket is
  `[7,448]`. This supplies a translated finite item-75 checkpoint without
  selecting an intermediate point.
  `QInterval.around_differenceQuotient_near_around_of_pos` and its signed-step
  wrapper `QInterval.around_differenceQuotient_near_around` now package the
  interval-level hand-off: a finite center-secant error plus explicit box,
  quotient, and derivative budgets yields a literal `NearAt` certificate.
  This closes another reusable algorithmic layer for item 75 while retaining
  the project's rational-box semantics.
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
- The cubic finite FTC package in `FiniteFTCPolynomial.lean` adds the explicit
  accumulator `FiniteFTC.cubeDerivativeLeftSum` for (3x^2) on `[0,1]`.
  Its exact form is certified by `cubeDerivativeLeftSum_eq`, and the error
  identities `cubeDerivativeLeftSum_error_eq` and
  `cubeDerivativeLeftSum_error_le_three_halves_div` give the potential-infinity
  schedule (0\le 1-S_n\le 3/(2n)) for every positive finite stage.  This is
  a cubic endpoint certificate, not an unrestricted classical FTC theorem.
  The matching `FiniteFTC.cubeDerivativeRightSum` has the exact form
  `((n+1)(2n+1))/(2n^2)` and exposes its positive error over the endpoint,
  giving the corresponding right-hand finite enclosure.
- Constructive FTA: a rational-complex polynomial of positive degree has a
  computable complex root.
  See `ComputableAnalysis/FTA.lean`.
- First checked FTA base cases:
  exact rational-complex roots lift to computable roots
  (`exactRoot_is_computable`), monic linear polynomials `X - r` have the
  computable root `r` (`monicLinear_has_computable_root`), and `z^2 + 1`
  has the computable root `i` (`zSqPlusOne_has_computable_root`).  The
  rational-coefficient extension
  (`rationalLinear_positiveDegree`, `rationalLinear_exact_root`, and
  `rationalLinear_has_computable_root`) now checks every `a*z+b` with
  `a != 0`, whose root is `-b/a`.
  The next FTA boundary is now checked as well: `qcomplexLinearPolynomial`
  accepts arbitrary rational-complex coefficients, and a supplied finite
  inverse witness for the leading coefficient yields an exact computable root
  through `qcomplexLinear_has_computable_root_of_inverse`.  This is the
  constant-first `[-b,a]` convention, so the root is `a⁻¹*b`; general division remains a
  separate representation task.
  The reusable finite rearrangement laws
  `QComplex.mul_assoc_cert`, `QComplex.mul_add_cert`,
  `QComplex.add_mul_cert`, `QComplex.mul_one_cert`,
  `QComplex.mul_neg_cert`, and `QComplex.neg_mul_cert` expose the coordinate
  algebra used by this certificate without importing a completed complex field.
  The finite evaluator `QComplex.exists_mul_inverse_of_normSq_ne_zero` now
  constructs the needed inverse witness from the nonzero rational norm-square,
  and `qcomplexLinear_has_computable_root_of_normSq` packages the resulting
  executable root.  Thus this linear case is no longer merely conditional on
  an abstractly supplied inverse.
  The coordinate identity `QComplex.normSq_eq_zero_iff` identifies nonzero
  norm-square with a nonzero complex coefficient, and
  `qcomplexLinear_has_computable_root_of_ne_zero` packages the resulting
  theorem under the natural leading-coefficient hypothesis.
The factorized monic quadratic package
(`rationalQuadratic_left_exact_root`,
`rationalQuadratic_right_exact_root`, and
`rationalQuadratic_has_computable_roots`) likewise certifies both roots of
`(z-r)*(z-s)` for rational `r` and `s`.
  The theorem `rationalQuadratic_positiveDegree` certifies the matching
  positive-degree premise.  The theorem `rationalQuadratic_root_of_discriminant`
  checks the usual quadratic-formula root for arbitrary rational `a`, `b`, and `c` whenever a
  rational witness `d^2 = b^2 - 4*a*c` is supplied; constructing such a
  witness remains the separate square-root task.  Its companion
  `rationalQuadratic_has_computable_root_of_discriminant` packages that exact
  root as a `ComplexCert`; the paired theorem
  `rationalQuadratic_has_computable_roots_of_discriminant` packages both
  quadratic-formula roots, and
  `rationalQuadratic_has_algebraic_roots_of_discriminant` gives the parallel
  `AlgebraicComplex` witnesses.
  The complex-coefficient quadratic boundary is now checked as well:
  `qcomplexQuadratic_root_of_discriminant` accepts a rational-complex
  discriminant square-root witness and an inverse witness for `2*a`, and
  `qcomplexQuadratic_has_computable_root_of_discriminant` packages the exact
  root.  The witness-producing square-root algorithm remains separate.
  Its norm-square specialization
  `qcomplexQuadratic_has_computable_root_of_discriminant_and_normSq` now
  constructs the inverse of `2*a` automatically from nonzero `normSq a`, so
  only the discriminant square-root witness remains explicit.
  The companion `qcomplexQuadratic_other_root_of_discriminant` and paired
  `qcomplexQuadratic_has_computable_roots_of_discriminant` now certify both
  quadratic-formula branches in the same finite witness model.
  The norm-square specialization now packages both branches automatically as
  `qcomplexQuadratic_has_computable_roots_of_discriminant_and_normSq`.
  The new `FiniteQuadraticRootInterval` bridge transports any finite
  square-root interval through both signed quadratic-formula branches using
  `affineQInterval_mem`; it is now root-imported and linked in the Algebra/FTA
  chapter.  It remains a finite interval transport theorem, not an arbitrary
  discriminant square-root existence theorem.
- The latest Wiedijk-list pass adds `FiniteFTABoundary.syntheticDivide` and
  `DeflationCertificate`: arbitrary finite rational-complex coefficient lists
  can be deflated at a supplied exact root, with a checked Horner remainder
  identity and factorization theorem.  This advances item 2 without claiming
  root existence or algebraic closure.
- The arbitrary-dimension Cayley--Hamilton consumer is now isolated in
  `FiniteCayleyHamiltonCertificate`: supplied monic annihilating-polynomial
  data for any finite `RatMatrix dimension` yields shifted annihilation and a
  finite matrix-power recurrence.  The characteristic-polynomial construction
  remains deferred.
- The quartic boundary now also has `finiteQuarticQuadraticSplit`: two
  supplied quadratic factors are multiplied in constant-first QComplex form,
  their Horner evaluations multiply exactly, and supplied roots of either
  factor become roots of the quartic.  This is a Ferrari-shaped finite
  interface; the general resolvent and witness-producing quartic formula remain
  deferred.
- `FiniteDeflationChain` now iterates supplied-root synthetic deflation and
  proves a single Horner factorization identity for the complete finite chain.
  This strengthens the finite root-peeling boundary behind items 2 and 16;
  root existence, radical extensions, and general solvability remain deferred.
- The chain API now also proves `exactRoot_of_exactRoot_of_ne`: a supplied
  root distinct from the deflated root remains an exact root of the quotient.
  This is the reusable algebraic step needed to turn a list of distinct
  supplied roots into a certified deflation chain.
- `FiniteQuinticDeflationExample` now instantiates that preservation lemma on
  the supplied roots `-2,-1,0,1,2`, proving a complete five-step finite
  deflation chain.  This strengthens the item-16/item-46 certificate boundary
  without claiming a quintic formula or root-finding algorithm.
- The quintic example now also checks its final padded quotient and exports
  the complete generic Horner factorization identity, making the supplied
  five-root certificate compositional rather than a list of isolated root
  equalities.
- `quintic_boundary_exact_factorization` specializes that final padded quotient
  to the constant polynomial `1`, exposing the complete product of the five
  supplied linear factors as an executable finite factorization. This is the
  finite endpoint of the item-2/item-16 root-peeling boundary; radicals and
  general quintic solvability remain deferred.
- The worked quintic now exposes its expanded constant-first coefficient list
  `0 + 4x - 5x^3 + x^5` and checks the direct evaluation at the supplied root
  `2`. This makes the item-16 boundary concrete both before and after the
  deflation chain, while keeping root construction and general solvability
  deferred.
- The worked cubic chain now also exposes its final padded quotient and the
  complete `horner_factorization` identity.  Thus the finite computation not
  only verifies each supplied root, but records the entire factor-peeling
  certificate in the generic chain interface.
- `FiniteFTAIsolationExample` now checks a nontrivial rational square around
  the origin for (z^2+1): interval Horner evaluation proves that its image
  misses zero, yielding a finite root-exclusion certificate.  This advances
  the FTA subdivision boundary from supplied roots toward executable
  isolation while keeping root existence and completeness deferred.
- The same worked example now instantiates the recursive dyadic subdivision:
  the supplied root (i) survives two stages inside a rational child box of
  width and height (1/2).  This records an explicit finite enclosure budget
  without passing to an attained limiting box.
- The symmetric supplied root (-i) now has the matching depth-two survivor
certificate, so both exact roots of (z^2+1) are covered by the finite
subdivision trace.
The same subdivision trace now has depth-three survivors for both `i` and
`-i`, with rational child width and height `1/4`. This sharpens the finite FTA
isolation budget while retaining the supplied-root, no-completeness boundary.
It now also checks depth four for both supplied roots, with child width and
height `1/8`, extending the explicit dyadic precision schedule without
claiming unique or globally constructed roots.
- `FiniteDeflationExample` makes that boundary concrete on the cubic
  (z^3-6z^2+11z-6): finite computation checks the quotient at the supplied
  root (1), its zero remainder, and the complete supplied-root chain
  (1,2,3).  This is a worked certificate, not an automatic root solver.
- `FiniteFTABoundary.syntheticDivide_quotient_length` now exposes the exact
  finite coefficient-count invariant of one supplied-root deflation.  The
  quotient remains padded in the constant-first representation, while the
  deflation chain supplies the corresponding factorization invariant.
The stronger `syntheticDivide_quotient_padded` theorem identifies that
padding explicitly and proves that trimming it lowers the coefficient count
by one for every nonempty input.
  `FiniteDeflationChain.deflatedCoeffs_length` lifts the padded coefficient
  count through an arbitrary finite chain, making the shape invariant
  explicit without claiming that padding removal or radical solvability is
  already formalized.
- `QBox.evalPoly_contains` now proves soundness of finite Horner evaluation on
  rational complex boxes: every enclosed rational point has its polynomial
  value enclosed by the output box.  This supplies the interval-arithmetic
  kernel needed for finite FTA root-exclusion/subdivision certificates,
  without asserting global root existence.  Its companion
  `QBox.evalPoly_no_root_of_not_overlaps_zero` packages the corresponding
  finite box-discard step.  `FiniteRootExclusionCertificate` now packages a
  finite rational cover of a supplied domain and proves `no_root_in_domain`
  when every covered box misses zero.
  `OneSurvivorCertificate.root_mem_survivor` adds the complementary finite
  search step: after excluding all other children, any root in the parent is
  forced into the retained child.
- `FiniteFTASubdivision.dyadicChildren` now supplies the geometric four-way
  split used by that search: ordered children are nested in the parent and
  cover it coordinatewise, all over rational endpoints.
  `dyadicChildren_width_height` proves the exact half-width/half-height
  shrinkage for every child.
  `survivingChildren` and `root_mem_survivingChildren` connect this geometry
  to polynomial-image overlap, proving that the finite filter cannot discard
  a root; `survivingChildren_ordered` preserves the box invariant after
  filtering.
  `survivingSubdivide` applies the filter recursively at every finite depth,
  while `root_mem_survivingSubdivide` proves that a supplied root remains in
  at least one retained box throughout that finite schedule.
  `survivingSubdivide_nonempty_of_root` makes the corresponding list
  nonemptiness explicit, and `survivingSubdivide_nestedIn_parent` together
  with `survivingSubdivide_ordered` preserves nesting and orderedness at every
  finite depth.
  `survivingSubdivide_width_height_exact` transfers the exact (2^{-n})
  width/height precision law to every retained box, so polynomial-image
  pruning preserves the finite mesh budget.
  `dyadicSubdivide` now iterates the four-way split to any finite depth;
  `dyadicSubdivide_nonempty` and `dyadicSubdivide_nestedIn_parent` provide the
  finite potential-infinity scaffold for repeated root search.
  `dyadicSubdivide_ordered` and `dyadicSubdivide_width_height_le_parent`
  additionally preserve orderedness and give an explicit non-expansion bound
  on both dimensions at every finite depth.
  `dyadicSubdivide_width_height_exact` sharpens this to the exact finite mesh
  law: every depth-(n) box has both dimensions divided by (2^n).  This is
  the explicit precision scheduler for the potential-infinity root-search
  route.
- `FiniteStirlingCertificate` adds a bounded item-90 exercise: finite rational
  enclosures for (e) and π, an explicit square-root bracket, and a certified
  Stirling-shaped ratio at (n=10).  The asymptotic Stirling limit remains
  outside the current theorem boundary.
- `FiniteStirlingStageSixtyFour` extends the same bounded item-90 schedule to
  (n=64), using the rational anchor `2005/100` for the square-root bracket of
  `128π` and retaining the explicit ratio enclosure `[1/2,2]`.
- `FiniteStirlingStageOneTwentyEight` extends the same bounded item-90 schedule
  to (n=128), using the rational anchor `2836/100` for the square-root bracket
  of `256π` and retaining the explicit ratio enclosure `[1/2,2]`; the
  asymptotic limit remains deferred.
- `FiniteStirlingStageTwoFiftySix` continues the same bounded item-90 schedule
  to (n=256), using the rational anchor `401/10` for the square-root bracket
  of `512π` and retaining the explicit ratio enclosure `[1/2,2]`; the
  asymptotic limit remains deferred.
- `FiniteStirlingStageFiveTwelve` extends the same bounded item-90 schedule to
  (n=512), using the rational anchor `567/10` for the square-root bracket of
  `1024π`.  Its sharper finite transport places the ratio in `[99/100,102/100]`
  and exports the explicit error budget `2/100`; the asymptotic limit remains
  deferred.
- `FiniteComplexPathCertificate` packages the first closed-polygon exactness
  certificate for a constant differential: a finite rational-complex path is
  closed by construction, and its exact displacement is proved to be zero.
  This is a finite primitive/cancellation layer, not a general Cauchy theorem
  or a limit of polygonal integrals.
  The same certificate interface now covers arbitrary finite polynomial
  differentials through `finitePolynomialDifferentialExactness_closed` and
  `FiniteClosedPolynomialPathCertificate.exactDisplacement_eq_zero`.
  The planned left-sum layer is now explicit as
  `polygonalLeftSumRawEntire`; `PolygonalLeftSumCertificate` and
  `polygonalLeftSumRawEntire_valid` promote it to a valid `ComplexRaw` only
  when orderedness, nesting, and shrinking widths are supplied as finite
  certificates.
- Next FTC extensions: exact polynomial derivative facts, then interval-valued
  Riemann-sum convergence under `IntervalRegularOn`.
  `Integral.IntervalRegularIntegralCertificate` now names the honest bridge
  boundary: it stores both interval regularity and a separate valid integral
  construction.  Its exact constant instance is checked, while the general
  regularity-to-integrability construction remains an explicit future theorem.
- Next FTA extensions: complex-coefficient linear polynomials using certified
  complex division away from zero, arbitrary quadratics via a computable
  discriminant square root, then
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
