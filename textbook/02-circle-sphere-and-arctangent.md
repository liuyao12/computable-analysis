# Chapter 2. Circle, sphere, and arctangent

## Finite geometric computations

This chapter uses Archimedean inner and outer approximations. Every stage
is a finite rational geometric calculation; the proof establishes containment,
refinement compatibility, and a shrinking gap. The geometric interpretation
must be justified by the relevant finite dissection and comparison laws.
Naming a convergent numerical stream an area or volume is insufficient.

The two spatial objects here are the unit circle and the solid sphere in
three dimensions. Higher-dimensional volumes are deferred to a later
proposition. They are not prerequisites for these opening constructions.

## Circle area and circumference

The rational circle parametrization is

$$
P(t)=\left(\frac{1-t^2}{1+t^2},\frac{2t}{1+t^2}\right).
$$

Rational parameters give rational points on the unit circle. On the parameter
interval from zero to one, take the fixed dyadic mesh and its midpoint
refinements. Chords and tangent intersections give inner and outer polygonal
sector areas. Extend the quarter-circle construction by symmetry.

**Circle proposition.** The area bounds are ordered, nested under refinement,
and have gap tending to zero. They therefore give a valid represented value,
denoted by the usual constant

$$
\pi.
$$

Chord and circumscribed-polygon lengths similarly give circumference bounds,
using justified square-root computations when the chord lengths are not
rational. The comparison proposition for a circle of radius one is

$$
C\simeq2\pi.
$$

Area and circumference are separate computations until that comparison has
been established. For a general nonnegative represented radius, scaling laws
require their own validity and geometric scaling evidence.

The library's `RationalCircle`, `Pi`, and `ArctanGeometry` modules contain the
rational geometric machinery. Some older circle comparison proofs remain in
the companion and are promotion work; this paragraph does not assert that
every circle law is exported by the foundation entry point.

## Sector area as arctangent

For a nonnegative rational parameter, let the geometric arctangent be the
sector area from the initial point to its circle point. The doubled-angle
normalization of the parametrization means

$$
A(x)=\arctan x,\qquad 4A(1)\simeq\pi.
$$

This geometric construction is made before using the derivative of
arctangent or defining arctangent by an integral. `ArctanGeometry.arctanGeom`
is the existing computation; its checked validity has explicit branch
hypotheses. The core comparison
`ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea` gives the normalization.

The same midpoint-refined parameter cells supply a quadrature computation
for the rational kernel

$$
k(t)=\frac{1}{1+t^2}.
$$

On a nonnegative cell the kernel is decreasing, so lower and upper rectangles
use its right and left values, respectively. For a dyadic partition of the
parameter interval, the basic finite mesh identity is

$$
\sum_j (t_{j+1}-t_j)^2=\frac{x^2}{2^n}.
$$

This is already checked as
`ArctanGeometry.arctanIntegralRectangle_dyadicSquareMesh`. Finite cell
comparisons relate the rectangle and geometric bounds. The checked raw-value
comparison is `ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom`.
Use its validity hypotheses when treating the two outputs as represented
numbers. Chapter 3 states the additional semantic integral obligation.

Keep this fixed dyadic refinement visible. Its finite cell estimates will
also support the later secant proof of the arctangent derivative, instead of
hiding the construction behind an unspecified choice of partitions.

## Inverting arctangent and constructing normalized trigonometry

On the first-quadrant branch, construct the inverse by rational target
brackets, with comparisons performed using finite enclosures of sector area.
Concavity motivates secant and supporting-line updates; their particular
rational containment and shrinking inequalities are what Lean must check.
Retain an overlap-safe update rather than waiting for an exact equality test.

For a rational normalized angle in the first quadrant, specify the inverse
parameter by

$$
0\le r\le\frac12,\qquad
A(u(r))\simeq2rA(1)\simeq\frac{\pi r}{2}.
$$

The primary geometric trigonometric computations are named sine and cosine:

$$
\sin(r)=\frac{2u(r)}{1+u(r)^2},\qquad
\cos(r)=\frac{1-u(r)^2}{1+u(r)^2}.
$$

Throughout this foundation, their input is the normalized angle. Thus these
names compute the values conventionally written as sine and cosine of
$\pi r$. Their period is $2$, and differentiation with respect to this
coordinate introduces the factor $\pi$. The rational samplers are
`GeometricTrig.sin` and `GeometricTrig.cos`.

The underlying `ArctanInverseCircle.sineQuarter` and `cosineQuarter` use a
quarter-turn fraction, so `GeometricTrig.quarter` supplies twice the normalized
argument. The inverse is geometric and overlap-safe, with a proved target;
its evaluation is not defined by a power series.

For any rational argument, use the integer quadrant index

$$
j=\lfloor 2r\rfloor,\qquad t=r-\frac j2,\qquad
0\le t<\frac12.
$$

Evaluate the first-quadrant pair at $t$, then rotate its coordinates using
$j$ modulo $4$. The checked endpoint identities show that adjacent closed
quarter descriptions agree. This handles negative arguments as well as
positive ones. `sample_on_closed_quarter` and `turn_join` expose the comparison
laws; `sin_period` and `cos_period` establish period two for rational inputs.

`GeometricTrig.sinAt` and `cosAt` extend these samplers to every valid
represented real. Whole rational input brackets are covered using proved
coordinate Lipschitz bounds. Finite prefix intersections restore nesting.
This construction does not test which side of a quadrant boundary an unknown
real lies on. Validity, rational agreement, representation invariance, and
period two are proved by `sinAt_valid`, `sinAt_rational`, `sinAt_congr`, and
`sinAt_period`, and the corresponding cosine theorems.

The full-domain geometric derivatives are proved in `GeometricDerivative`,
including secants crossing the quadrant joins. Chapter 6 explains the finite
estimate beneath those identities. Unit-circle, parity, and addition identities
are separate exact laws; addition formulas and comparison with exponential
constructions can be developed later.

## Solid sphere

For the unit solid sphere, horizontal sections have disk-area coefficient
given by the quadratic height profile. Approximate the upper and lower
hemispheres by finite stacks based on dyadic height subdivisions. Inner and
outer disk approximations reduce the finite volume bounds to rational
dissections and the circle-area computation.

**Sphere proposition.** Construct actual compatible geometric volume bounds,
prove their gap shrinks, and identify their represented value by

$$
V\simeq\frac43\pi.
$$

The familiar quadratic finite sums are part of the computation. Proving
their algebra or writing down this multiple of the circle-area value alone
does not prove that it is the geometric volume. Existing
`RationalBall.shells_recurrence_estimate` is reusable finite shell evidence;
its source explicitly leaves the geometric dissection bridge separate.
This sphere proposition remains a target until that bridge for the actual
three-dimensional construction is supplied. Higher dimensions can follow
as a later theorem rather than expanding this chapter's scope.
