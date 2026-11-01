# Chapter 3. Integration, derivatives, and the fundamental theorem

## A mathematical relation, not a universal recipe

An integral claim identifies the role of a supplied computation for a supplied
function on a supplied interval. It is useful to state general comparison,
uniqueness, linearity, and fundamental-theorem laws with the evidence they
need. Those laws do not select a class of integrands or give one algorithm
that must construct every integral.

For each particular function, propose an appropriate construction, prove its
validity, and prove that it has the claimed integral role. Rational quadrature,
finite geometric dissection, an independently justified endpoint formula,
series, substitution, and domain-specific methods may provide different
routes. No route's numerical validity alone establishes that role.

Markdown records the mathematical contract, available laws, and reference
constructions. The accompanying skills help agents choose a method. Lean
checks the finite estimates and the bridge from the actual computation to
the stated integral relation. There is no obligation to formalize a universal
method-selection algorithm or a general existence theorem before doing this
work for a particular function.

## Constant and simple functions, interval addition, and bounds

The basic integral contract starts with constants and finite piecewise
constant functions. Here a **simple function** means a step function on a
finite interval partition. It does not refer to an unspecified measurable-set
theory. Initially take rational partition points; its constant values can be
arbitrary valid represented reals. Fix the endpoint convention when defining
the sampler, and prove that isolated endpoint choices do not affect the
integral rather than assuming that fact silently.

For a constant value, the normalization is

$$
\int_a^b c\,dt\simeq(b-a)c.
$$

Finite interval addition gives the value for a supplied simple function:

$$
\int_a^b s(t)\,dt\simeq
\sum_{j=0}^{N-1}(t_{j+1}-t_j)c_j,
\qquad a=t_0<\cdots<t_N=b.
$$

Prove that refining its presentation does not change this value. For any
supplied function and justified integral witnesses on adjacent intervals,
the interval-addition law is

$$
\int_a^c f(t)\,dt\simeq
\int_a^b f(t)\,dt+\int_b^c f(t)\,dt,
\qquad a\le b\le c.
$$

This is a conditional comparison of supplied witnesses, not an assumption
that every interval already has a chosen integral.

Finally, simple functions supply the required order tests. If they bound the
supplied integrand on the entire interval, every justified integral value
must obey

$$
s_-(t)\le f(t)\le s_+(t)\quad\Longrightarrow\quad
\int_a^b s_-(t)\,dt\le\int_a^b f(t)\,dt
\le\int_a^b s_+(t)\,dt.
$$

These are the proposed common laws. Constants already have a construction
theorem in the current interface; a general simple-function constructor,
refinement comparison, and adjacent-interval law must be checked at their
actual implementation scope before being marked proved. No new integral
record is introduced here that assumes the desired identification or
uniqueness conclusion.

The laws do not assert existence or determine a unique integral for every
function. If all available simple bounds leave a positive gap, they can
permit several values. For functions with arbitrarily tight simple bounds,
the bounds do identify at most one value; that is a proved sufficient route.
Other particular constructions may be justified by additional mathematical
evidence and comparison laws. Do not turn tight simple approximation into
a compulsory hypothesis for every method.

## The monotone quadrature construction

Let the endpoints be rational and ordered, and let a nondecreasing sampler
have valid represented values throughout the interval. Use the fixed mesh

$$
t_j=a+\frac{j(b-a)}{2^n},\qquad j=0,\ldots,2^n.
$$

At a separate evaluation stage, define rational lower and upper sums

$$
L_{n,m}=\sum_{j=0}^{2^n-1}(t_{j+1}-t_j)
\operatorname{lo}(f(t_j),m),
$$

$$
U_{n,m}=\sum_{j=0}^{2^n-1}(t_{j+1}-t_j)
\operatorname{hi}(f(t_{j+1}),m).
$$

For a nonincreasing sampler exchange the endpoint roles. Monotonicity
provides range containment on every cell. A supplied bound on total endpoint
variation controls the spatial rectangle gap. The evaluation contribution
is controlled by the finite sampled widths, for example by

$$
(b-a)\max_{0\le j\le2^n}
\operatorname{width}(f(t_j),m).
$$

Prove the actual combined error estimate; do not infer it from the names of
the two indices. For each fixed spatial mesh there are finitely many sample
values. Their validity allows a sufficiently large evaluation stage to be
found so that all required widths satisfy the chosen rational error budget.
An evaluation schedule may tend cofinally to infinity, or directly certify
the shrinking width budget for each sample. Exact rational values need no
further evaluator refinement. The new signed monotone construction uses a
terminating rational width search for each sampled value.

Thus a function-specific diagonal schedule can be chosen to satisfy

$$
n(k)\longrightarrow\infty,\qquad m(k)\longrightarrow\infty,
\qquad U_{n(k),m(k)}-L_{n(k),m(k)}\longrightarrow0.
$$

The last conclusion requires the proved error control; the first two
conditions alone are not a substitute. In particular, using the same stage
for subdivision and all evaluator calls is not justified automatically.
If a two-index bound is uniform beyond independent thresholds, any cofinal
diagonal satisfying those thresholds can be compared directly.

Before declaring the diagonal a real name, prove orderedness and compatibility
between its finite bounds. If literal nesting needs repair, use finite prefix
intersections after proving that those intersections are nonempty and retain
the shrinking estimate. Do not assume an already-existing integral merely
to supply their common point. Prove agreement for other justified schedules
so callers need not choose the internal precision policy.

## The arctangent comparison

For the rational kernel of Chapter 2, endpoint evaluation is exact. Only
spatial subdivision contributes uncertainty, and decreasing-kernel rectangle
bounds can be compared cell by cell with the geometric sector bounds.
The intended identity is

$$
\int_0^x\frac{dt}{1+t^2}\simeq A(x).
$$

On the checked unit branch, the raw quadrature value is valid and equivalent
to the geometric arctangent by the existing `ArctanGeometry` results. These
are substantial construction and comparison results. To advertise the
display as a theorem of a semantic integral interface, also certify that
the actual quadrature satisfies that interface for the entire segment.
The word “integral” in a constructor name does not discharge that obligation.
Extensions beyond the checked branch need their own construction or transport
proofs; negative endpoints use justified orientation.

## The current semantic interface and its boundary

`Integral.HasIntegral` presently uses arbitrarily tight finite rectangle
tests. It proves uniqueness and representation invariance at that scope.
`Integral.HasIntegral.ftc` applies to an independently supplied witness and
`Integral.CellDerivativeBounds`, which gives local inequalities about the
actual endpoint function. Finite telescoping yields

$$
\int_a^b f(t)\,dt\simeq P(b)-P(a).
$$

This is a proved conditional law; it is not a universal constructor. The
rectangle criterion is a useful sufficient route, not the mandatory meaning
for every new function-specific integral construction. Separating the
intended method-independent laws from this route remains open design and
proof work. Broader uniqueness needs justified comparisons or common laws,
not an assumed uniqueness field.

## Nonmonotone functions

For a particular nonmonotone function, supply whatever finite range bounds,
local pieces, substitutions, or other evidence the actual construction uses.
Keep domain, pole, branch, and tail restrictions explicit. Resolve internal
partitions and turning-point brackets inside the construction and compare
choices before hiding them from callers. Do not require every function to
fit the monotone quadrature recipe.

**Construction skill: use the particular function's geometry.** For the
normalized geometric sine and cosine of Chapter 2, the base rational domain
is $[-1,1]\cap\mathbb Q$, extended with period $2$. Sine is increasing on
$[-\tfrac12,\tfrac12]$ and decreasing on the two remaining base pieces;
cosine is increasing on $[-1,0]$ and decreasing on $[0,1]$. Use proved order,
periodicity, and join laws to split an integration interval at these exact
rational transitions. No approximate search for these breaks is needed.
Refine endpoint evaluations and rectangle meshes together; exact transition
locations do not remove the need to control evaluation error.

For another function, unresolved transitions may instead be enclosed in
rational brackets $[\ell_j,r_j]$ with proved bounds $L_j\le f\le U_j$
throughout each bracket. Their contribution boxes are

$$
[L_j(r_j-\ell_j),\;U_j(r_j-\ell_j)].
$$

Choose the brackets and outer-piece computations so that the total uncertainty

$$
\sum_j (U_j-L_j)(r_j-\ell_j)
  +\text{outer-piece errors}
$$

is below the requested tolerance. The bounds may vary with refinement; the
products must shrink with a justified schedule. These are case-by-case
construction strategies, not a universal partition algorithm or new checked
existence theorem. See the integral construction skill at
`skills/computable-analysis-formalization/references/integral-computation-strategies.md`.

## Derivatives as continuous extension of the quotient

Once the necessary function evaluations are justified, fix an input point
and form the punctured difference quotient

$$
Q_{F,x}(h)=\frac{F(x+h)-F(x)}{h},\qquad h\ne0.
$$

The derivative is the value at zero of a continuous extension of this
quotient, when such an extension is constructed:

$$
DF(x)\simeq\widetilde Q_{F,x}(0).
$$

The extension must cover sufficiently nearby punctured quotient values.
Filling in an arbitrary valid value at zero is insufficient: it must agree with all
the punctured quotient observations and make the output brackets shrink
there. At a boundary retain the intended one-sided domain. For represented
base points, justify the derived function evaluations used in the quotient;
do not silently replace the rational-input primary function by an assumed
extension.

Each function supplies the quotient enclosures or secant bounds appropriate
to it. For arctangent, reuse the fixed dyadic geometry and local kernel
bounds. No universal differentiation procedure is required. The existing
`BracketDerivative.HasDerivativeAt` instead states a common limit of all
admissible rational endpoint secants. Its checked uniqueness and congruence
laws remain available. Agreement between that interface and the quotient
extension formulation needs an explicit bridge under the relevant continuity
and domain evidence; it is not asserted merely because both use the word
derivative.

**Another construction route: Cauchy's formula.** For a complex function with
a justified Cauchy representation, a positively oriented simple contour
$\gamma$ enclosing a neighborhood of $z$ gives a candidate computation

$$
D_\gamma f(z)=\frac{1}{2\pi i}
  \int_\gamma\frac{f(\zeta)}{(\zeta-z)^2}\,d\zeta.
$$

Certify that the contour and its interior lie in the function's domain,
prove separation from the evaluation neighborhood, and justify the contour
integral with its error bounds. Subtracting the Cauchy representations at
$z+h$ and $z$ yields a difference quotient whose kernel converges uniformly
to this squared kernel. That argument identifies the computation with the
derivative and permits comparison of different valid contours. It does not
change the derivative specification. If Cauchy's theorem was proved from
holomorphicity using a derivative witness, this is a new computation of that
derivative; it does not supply a prior definition of holomorphicity. The
geometric real sine/cosine FTC development remains independent of this
complex route. See `skills/holomorphic-functions/SKILL.md`.

## Constructed convex and concave derivatives: a checked FTC

The first calculus goal after the integral specification is the recovery law

$$
\int_a^b DF(t)\,dt\simeq F(b)-F(a).
$$

For a convex function, left secants bound the derivative from below and right
secants bound it from above. Concavity reverses these bounds. Convexity alone
does not make their gap vanish: the function

$$
F(x)=|x|
$$

has a corner at zero. A function-specific construction must prove that its
actual outer-secant intervals are ordered, nested, and shrink. No generic
ordinary derivative is asserted at corners.

`ConvexFTC.OuterSecants` packages the executable rational sampling schedule
and these validity proofs. The secants surround the full input interval, not
only a chosen rational approximation. `OuterSecants.hasDerivative` identifies
their value with `RealSecantDerivative.HasDerivativeAt`, which controls all
sufficiently nearby rational secants. The input may be any valid represented
real. `OuterSecants.equiv` proves agreement for different valid schedules and
equivalent input names. The quotient-extension bridge discussed above remains
a separate target.

From ordered secants the module derives supporting-slope inequalities:

$$
DF(u)\le\frac{F(v)-F(u)}{v-u}\le DF(v),\qquad u<v
$$

in the convex case, with the endpoint derivatives reversed in the concave
case. Thus the constructed derivative is nondecreasing or nonincreasing.
Multiplying these inequalities by each cell length and telescoping gives
rectangle bounds for the endpoint difference. This argument needs no attained
mean-value witness.

The signed monotone quadrature in `ConvexFTC` works with represented values
of either sign. For a uniform partition into a positive number of cells, the
finite gap estimate separates spatial and evaluator error:

$$
U-L\le\frac{b-a}{N}B+(b-a)\tau.
$$

Here the nonnegative rational bound is computed from endpoint boxes, and
each sampled evaluator width is at most the supplied positive tolerance.
`boundsAtTolerance_gap` proves that the internal cell count and width searches
meet any requested positive rational error. These partitions need not be
dyadic; the geometric arctangent retains its fixed dyadic construction.

`ConvexFTC.integral` evaluates these rectangles independently and intersects
finite prefixes to repair nesting. The previously derived endpoint bounds
justify nonempty intersections; an integral identity is not an input field.
`integral_hasIntegral` certifies this computation in the current rectangle
relation, and `integral_ftc` proves the displayed exact recovery law.
`integral_equiv` compares the integral computations from different supplied
valid secant schedules.
The proper integral bounds are rational. The older outer-secant route needs
its supplied neighborhood to remain inside the proved curvature domain.
`ConvexFTCClosed` now supplies a second route using actual relative derivatives
on the closed interval itself. It derives supporting slopes from all-pair
secant limits and the weighted identity for adjacent secants; at an included
endpoint, one-sided evidence suffices. No curvature outside the interval is
requested. `closedIntegral_hasIntegral` and `closedIntegral_ftc` certify an
independently executed signed quadrature. `closed_ftc` applies to any supplied
actual integral, and `oriented_ftc` also covers reversed or coincident bounds.

The companion `ConvexFTCExamples` instantiates the full construction for
the square and its concave negative, including an interval crossing the
derivative's zero. It also proves the supporting-slope integral law for an
affine function with any valid represented coefficient, including irrational
coefficients. These are checked reference cases, not extra core imports.

## Differentiating accumulated monotone integrals

`MonotoneFTC.accumulated` independently computes the primary rational sampler

$$
P(q)=\int_a^q f(t)\,dt,\qquad q\in\mathbb Q\cap[a,b].
$$

When the supplied integrand is increasing, this accumulation is convex; when
it is decreasing, the accumulation is concave. The `curved` theorem derives
this from integral increments and monotone endpoint bounds, without a sign
restriction on the integrand.

Under the chapter-one endpoint continuity criterion, the covered derivative
of this rational sampler at any valid represented source point is the
integrand's justified extension value:

$$
DP(x)\simeq f(x).
$$

`MonotoneFTC.hasDerivativeAt` applies to any independently justified accumulated
integral samples. Its proof derives the integral role of increments by interval
additivity, then squeezes every nearby secant between actual integrand endpoint
boxes. Validity of those boxes makes the gap shrink. `accumulated_hasDerivativeAt`
instantiates the law with the executed quadrature. No general product, chain,
or inverse derivative law is needed.

`closed_hasDerivativeAt` and `exists_closed_derivative` cover the entire closed
represented source interval, including relative endpoint derivatives. Clipping
is internal, so a valid input name may straddle an included boundary.
`closed_value_congr` proves agreement for equivalent names and different valid
endpoint computations. `EndpointContinuity.HasValueAt` records only an actual
valid integrand endpoint computation and its value; it assumes no derivative
or integral identity.

These are the two checked elementary FTC directions at the current proper-
integral and covered-secant interfaces. A proper integral still has rational
bounds; an integral at particular represented or improper endpoints requires
its own justified extension or exhaustion. `ConvexFTC.limit_hasIntegral` and
`limit_ftc` now provide the recovery law for a supplied compact exhaustion
whose endpoint-value sequences converge. They permit arbitrary represented
limiting values and use actual compact integrals, not validity-only candidates.
The punctured-quotient comparison remains the separate interface obligation
described above. Further derivative algebra can be formalized for applications
when needed.

## Finite changes of curvature

The checked `PiecewiseFTC.Pieces` extension permits finitely many supplied
convex and concave pieces. Their derivative need not be globally monotone.
It concatenates local finite rectangle bounds, proves global increment bounds
across joins, and certifies the sum of independent local quadratures on the
whole interval. Intermediate endpoint values cancel in `Pieces.ftc`.
`Pieces.integral_equiv` proves agreement for different justified decompositions.

All pieces use the same endpoint function and derivative sampler at a join.
Curvature proofs still need actual derivative validity and supporting slopes;
curvature alone cannot supply them. `Pieces.ofOuter` derives a leaf from the
existing outer-secant route when its neighborhood hypotheses hold. At an
inflection point on a piece boundary, that two-sided route may leave the
curvature domain. `Pieces.ofClosed` now constructs a leaf from actual relative
closed-domain derivatives and curvature on that piece, deriving its supporting
slopes internally. Shared endpoint values and the necessary derivative evidence
must still be justified. See Chapter 6
for the trigonometric application and the precise remaining obligations.

## Logarithm from monotone dyadic quadrature

The checked elementary construction starts from the definite integral

$$
L(x)=\int_1^x\frac{dt}{t},\qquad x>0.
$$

For positive rational endpoints \(a\le b\), subdivide into \(2^n\) equal
cells, with width \(h_n=(b-a)/2^n\) and points \(t_k=a+kh_n\).
Since the reciprocal is decreasing, the rational endpoint sums bound the
integral:

$$
\ell_n=h_n\sum_{k=1}^{2^n}\frac1{t_k},\qquad
u_n=h_n\sum_{k=0}^{2^n-1}\frac1{t_k}.
$$

Their difference telescopes exactly:

$$
u_n-\ell_n
=h_n\left(\frac1a-\frac1b\right)
=\frac{(b-a)^2}{ab\,2^n}.
$$

Refinement increases the lower sum and decreases the upper sum. These
properties and the explicit shrinking gap justify the raw construction.
`BoundsQuadrature` takes finite prefix intersections of the actual dyadic
bounds to certify nesting, using independently proved overlap of integral
bounds.
For \(x\ge1\), use \([a,b]=[1,x]\); for \(0<x<1\), use
\([a,b]=[x,1]\) and negate the resulting interval. The value at one is zero.
All samples in this primary rational-input construction are exact rationals.

The resulting logarithm is increasing, although its integrand is decreasing.
On a positive interval \([a,b]\), its integral increments give

$$
\frac{v-u}{b}\le L(v)-L(u)\le\frac{v-u}{a},
\qquad a\le u<v\le b.
$$

These give strict increase and the quantitative continuity needed to extend
the rational sampler to valid represented positive inputs. Require the input
name to be eventually contained in the positive domain, and prove validity
of the actual endpoint-evaluation precision schedule.

`MonotoneLogarithmRange` proves full real range using only the preceding
increment inequalities. Each dyadic segment contributes at least
\(1/2\), so

$$
L(2^m)\ge\frac m2,\qquad
L(2^{-m})\le-\frac m2.
$$

A natural number computed from the target's first rational interval gives
an initial positive bracket. Strict rational inversion then constructs a
preimage for every valid represented real target, using finite separation
rather than deciding equality of real numbers. Both inverse laws are
proved, as are the ordinary quotient definitions `value` and `inverseValue`.
This range proof does not assume the logarithmic product law.

The derivative follows from the same integral increments. Every rational
secant satisfies

$$
\frac1v\le\frac{L(v)-L(u)}{v-u}\le\frac1u,
\qquad 0<u<v.
$$

For a shrinking positive neighborhood of a represented input, the reciprocal
endpoint computation is valid and the bounds squeeze every secant.
`MonotoneLogarithm.derivative` states the full covered derivative
\(L'(x)=1/x\), independently of the chosen valid rational-sample presentation.

**Remaining comparison.** Identifying this inverse with the Euler-method
exponential is still a separate proof obligation. The already checked
Euler/series comparison would then also identify it with the factorial
series. The companion's `ExponentialComputations.integralLog` and its inverse
laws remain checked at their own scope; they are not silently used as the
missing comparison for this independent foundation route.
