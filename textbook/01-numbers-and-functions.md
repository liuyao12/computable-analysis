# Chapter 1. Computable numbers and functions

## Real numbers

A real name is a map from stages to rational intervals,

$$
x:n\longmapsto I_n=[a_n,b_n],\qquad a_n,b_n\in\mathbb Q,
$$

satisfying orderedness, nesting, and shrinking:

$$
a_n\le b_n,\qquad
n\le m\Longrightarrow a_n\le a_m\le b_m\le b_n,
$$

$$
\forall\varepsilon\in\mathbb Q_{>0}\;\exists N\;
\forall n\ge N,\quad b_n-a_n\le\varepsilon.
$$

These are the conditions in `RealRaw.Valid`. The raw data in `RealRaw` do
not include validity as an assumption that every program automatically
satisfies. A construction supplies the data and proves these conditions.
No particular rate of shrinking is imposed by the definition.

Here **computable** is used informally when the stage map is given by a finite
algorithm. The mathematical definition does not itself impose that
restriction on every supplied name. All concrete constructions should strive
to be executable, without requiring optimal efficiency. The type of
`RealRaw.compute` alone is not a computability certificate. A supplied
quantitative schedule is additional usable data, not another kind of number.

## Equality, order, and arithmetic

Two valid names represent the same value when their intervals overlap at
every stage. Write this relation as

$$
x\simeq y.
$$

The Lean relation is `RealRaw.Equiv`. Checked lemmas show that, on valid
names, common-stage overlap also gives overlap between arbitrary pairs of
stages. Equality is reflexive, symmetric, and transitive on valid names.

The real numbers themselves are the equivalence classes

$$
\mathbb R=\{x:\mathrm{RealRaw}\mid x\text{ is valid}\}/{\simeq}.
$$

`Numbers.Real` is this quotient, implemented by `RealRawQuotient.Value`.
Two valid names have equal quotient values exactly when `RealRaw.Equiv`
holds. The quotient does not choose a computation: algorithms still operate
on supplied raw representatives and prove that their outputs are independent
of those choices. The existing `Real` record is a legacy computation bundle
with a preferred implementation, rather than this mathematical quotient.

Forming a quotient does not require marking its arithmetic `noncomputable`
in Lean. Quotient constructors and lifts preserve executable operations on
supplied names when their congruence proofs are available. They do not provide
a canonical executable representative of an arbitrary equivalence class.
Our domain evaluator descends directly through the quotient using its proved
representation invariance, so it needs no `noncomputable` declaration.
Numerical execution uses a supplied valid name. These are distinct issues
from whether a particular example's stage map is given by an algorithm.

We aim for downstream computational applications that need no `noncomputable`
declarations. Constructions should supply executable witness selection where
needed; classical reasoning may remain in proofs. This is a design goal,
independent of improvements in proof size or numerical efficiency, rather
than a claim that every existing interface has already met it. Classical
comparison maps to Mathlib remain in their separate downstream package.

Order is the value-level relation

$$
x\le y\quad\Longleftrightarrow\quad
\forall n,m,\ a_n(x)\le b_m(y),
$$

implemented as `RealRaw.Le`. A finite interval comparison can instead return
overlap; that output is not an exact decision of equality or order.

Rational constants, addition, negation, subtraction, rational scaling, and
multiplication are given by rational interval algorithms. For multiplication
one may always take the minimum and maximum of the four endpoint products:

$$
[a,b][c,d]=
[\min(ac,ad,bc,bd),\ \max(ac,ad,bc,bd)].
$$

This construction allows intervals crossing zero. Sign-separated formulas
can be used when their evidence is available; shifting stages cannot force
the zero value to have a strict sign.

For a reciprocal, by contrast, the divisor must be separated from zero. Once
a stage satisfies either strict separation condition, later nested intervals
retain it, and the reciprocal interval is

$$
[a,b]^{-1}=[1/b,1/a],\qquad 0<a\le b\ \text{or}\ a\le b<0.
$$

The construction must provide or find that stage with a termination proof.
Dividing without nonzero-domain evidence is not justified by the totality of
rational operations in Lean. Complex division uses separation of the squared
magnitude from zero rather than a sign on complex numbers.

**Arithmetic propositions.** Prove validity and congruence for each operation,
then the ordered-field laws at the level of represented values. In particular,
state associativity, commutativity, distributivity, identities, additive
inverses, and multiplicative inverses modulo value equivalence; retain the
nonzero hypothesis for inverses. State reflexivity, antisymmetry modulo value
equivalence, transitivity, totality, and the additive and positive-multiplicative
order laws. This is the full mathematical contract to audit, not a claim that
an `OrderedField` instance or every one of these public laws is already
packaged. Existing selected declarations are listed in the proposition ledger.

## Complex numbers

A complex name is a sequence of rational complex boxes. It can be stored as
two Gaussian rational corners, whose real and imaginary coordinates are
ordered separately. The box is the product of those two coordinate intervals,
not an ordered line segment in the complex plane. The coordinates satisfy
the same nesting and shrinking conditions as real names.

This is equivalent to supplying two real names, so write

$$
z=x+iy.
$$

`ComplexRaw`, `QBox`, and `ComplexRaw.Valid` implement the data and validity;
`ComplexRaw.Equiv` is equality of values. Coordinate projection, arithmetic,
and their representation invariance must be justified. There is no order on
the complex field corresponding to the real ordered-field structure.

Likewise define

$$
\mathbb C=\{z:\mathrm{ComplexRaw}\mid z\text{ is valid}\}/{\simeq}.
$$

`Numbers.Complex` reuses the existing `ComplexRawQuotient.Value`, and
`Numbers.ofReal` gives the injective inclusion of real quotient values.
These quotients identify the numbers represented by the algorithms; they do
not replace the interval constructions or their validity proofs.

The separate downstream file
`subprojects/mathlib-comparison/ComputableAnalysisMathlibComparison.lean`
compares them with Mathlib's number types. `realOrderRingIso` preserves the
real order and arithmetic; `complexRingIso` preserves complex arithmetic,
with proved agreement for the real inclusion and the imaginary unit.
These are bijections on all values, including values without supplied
executable names. The comparison package imports both libraries; the
foundation itself imports no Mathlib modules. Its classical comparison maps
are marked `noncomputable`, independently of the concrete interval algorithms.

## Functions and evaluation at represented inputs

Numbers naturally occur as special values of functions. Primary computations
therefore take rational or Gaussian rational inputs, or rational parameters
in an explicitly specified chart. Their outputs are represented numbers.
Domains are part of the definition. `PartialRealFunRaw` and `FunctionRaw`
provide the basic real and complex sampler data.

A raw function contains one computation on its declared domain. Another
computation, possibly on a larger domain, is a separate raw object whose
agreement must be proved. The derived mathematical function has the usual
form $f:U\to\mathbb C$, with $U$ open when discussing holomorphicity.
Evaluation requires domain membership evidence and gives no placeholder
values outside $U$. More general evaluation domains can retain meaningful
boundary values, with holomorphicity proved on an open restriction.

On the same domain, equality means pointwise equality of values. On different
domains, agreement on the intersection means compatibility, and extension
additionally requires domain inclusion. `FunctionRawDomain` proves validity
of restrictions and composition of extensions; `SameFunction` includes
equality of domains. These checked raw laws concern rational samples; the
agreement of represented-input extensions must also be proved.

Nonempty-overlap agreement is not transitive: two disjoint restrictions of
the same constant function both agree with the larger function, but do not
overlap each other. It can nevertheless generate an equivalence relation:
`FunctionRaw.OverlapEquivalent` allows finite chains, so direct overlap is
sufficient but not necessary for equivalence. For analytic continuation,
restrict the presentations to holomorphic computations on connected local
domains. A chain class can contain different branches and does not by itself
give a single-valued function on the union. The raw chain relation alone
does not prove those analytic conditions.

Later, on the Riemann surface of the continued function, different branches
over the same complex coordinate occupy different surface points. Each raw
computation describes a local branch; evaluation at a specified surface point
is single-valued. The chain equivalence records the continued analytic
function rather than equality of its local sections as partial functions.

Use compatibility for gluing and extension, and germs at a fixed point for
local identity. Gluing must retain an actual computation with justified
local selection and comparison, together with compatibility on all overlaps
needed by the glued function.

`DomainFunctions.Map` is the foundation's represented-input adapter. Its
`valueDomain` and `value` descend the domain and evaluation to quotient
complex values, and `value_ofRaw` proves agreement with execution on any
supplied valid input name. The semantic quotient wrapper is not an algorithm
for choosing a preferred input computation.

For a nondecreasing real sampler, the values at the two endpoints bound
all rational values between them. For a nonincreasing sampler, exchange
the endpoint roles. This order construction is the basis of the following
continuity definition. General function-specific enclosures and complex-box
enclosures remain available as other computational tools.

## Continuity on increasing and decreasing pieces

Let $f$ have valid rational-input evaluations and be increasing on an interval
$I$. An admissible input is a valid name $x_n=[a_n,b_n]$ that is eventually
contained in that interval:

$$
\exists N\;\forall n\ge N,\qquad [a_n,b_n]\subseteq I.
$$

We discard that finite prefix and relabel the remaining intervals. No
additional interior-point condition is imposed. Write $f_{m,-}(q)$ and
$f_{m,+}(q)$ for the lower and upper rational endpoints of the stage-$m$
evaluation at a rational input $q$.

**Definition.** The increasing function is continuous on $I$ if, for every
admissible valid input name, an endpoint precision schedule $\sigma$ makes

$$
\bigl[f_{\sigma(n),-}(a_n),f_{\sigma(n),+}(b_n)\bigr]_n
$$

a valid real name. For a decreasing function the sequence is

$$
\bigl[f_{\sigma(n),-}(b_n),f_{\sigma(n),+}(a_n)\bigr]_n.
$$

The direct schedule is $\sigma(n)=n$. Choosing $\sigma(n)=2n$ or another
function-specific schedule may simplify the validity proof. Prove validity
of the actual output, including nesting and shrinking; a cofinal schedule
alone does not establish it for a sampler whose argument also varies.
Continuity here means exactly that this endpoint construction turns valid
admissible inputs into valid outputs. No finite-observation condition is
added to this definition. Increasing and decreasing include their nonstrict
versions; strictness is needed separately when inverting the function.

**Checked comparison laws.** Monotonicity proves cross inequalities between
any two such endpoint constructions on equivalent input names. If both
outputs are valid, these inequalities prove they represent the same real.
Thus different valid schedules, discarded prefixes, or admissible input
names give the same value. At rational inputs this value agrees with the
primary sampler. `EndpointContinuity.ContinuousOn`, `bounds_equiv`,
`bounds_value_eq`, and `rational_agreement` formalize these statements; see
`docs/ENDPOINT_CONTINUITY.md`. Existence of a valid schedule is a property;
concrete applications supply their executable construction and proof.

## Polynomial and rational-function continuity

**Checked endpoint-continuity bridge.** On supplied strictly increasing or
strictly decreasing intervals, `EndpointContinuityBridge` and
`EndpointContinuityDecreasing` prove the preceding criterion for polynomials
and rational expressions. Coefficients and inputs may be arbitrary valid
represented reals. The rational-function interval must contain no represented
denominator zero, including irrational poles. Locating or bracketing the
turning points is a separate function-specific construction.

The endpoint schedule is executable. `StrictEndpointContinuity.precision`
searches finite rational tests until the next endpoint samples both have
small errors and fit inside the preceding output interval. If a rational
endpoint has moved, strict order supplies finite separation; if it has not,
nesting of that same sample suffices. This proves termination and nesting.
Finite-observation coverage then proves the gaps shrink. No uniform
continuity modulus is requested from the caller.

**Existing sufficient computational route.** Interval arithmetic evaluates
polynomials on the whole real line and rational expressions

$$
R(x)=\frac{P(x)}{Q(x)}
$$

where $Q(x)\ne0$. The older `FunctionContinuity.Continuous` certificate
requires validity, name invariance, and finite observation. Its checked
theorems below remain available for this route; finite observation is not
the chapter's primary continuity definition. The complex counterpart remains
a separate target.

The construction starts with rational-input sampling and extends using the
already proved interval arithmetic. Constants and the identity preserve
validity. Addition and multiplication preserve validity and representation
agreement, so a finite Horner evaluation does too. For a quotient, refine the
denominator until its interval is separated from zero, then use reciprocal
intervals and multiplication. Nonvanishing justifies termination of that
search. On a compact neighborhood away from zero, reciprocal interval widths
are bounded by a fixed rational multiple of denominator widths, so they shrink.
These arguments use no differentiation theorem.

Squaring at zero is the first place where monotone endpoint evaluation needs
care. For $a\le b$, the exact interval range is

$$
\{x^2:a\le x\le b\}=\begin{cases}
 [a^2,b^2],&0\le a,\\
 [b^2,a^2],&b\le0,\\
 [0,\max(a^2,b^2)],&a\le0\le b.
\end{cases}
$$

If $[a_n,b_n]$ shrinks to zero, the third enclosure shrinks to zero as well.
Squaring the two endpoints alone would miss the interior minimum. General
interval multiplication is also sufficient: for $[-h,h]$ it may return the
wider enclosure $[-h^2,h^2]$, which still covers all squared values and shrinks.
Sharp bounds are useful but are not required for continuity. This computational route evaluates a polynomial without a supplied list
of all its turning points. The endpoint criterion is stated separately on
a monotone interval.

A zero of the displayed denominator is excluded from that computation's
domain. Some such singularities are removable after cancellation or another
justified extension; a zero denominator is not automatically a genuine pole.

**Lean status of the sufficient computational route.** The real-variable
theorems under `FunctionContinuity.Continuous` are checked:
`FunctionContinuity.polynomial_continuous` applies to every finite list of
valid real coefficients, and `rationalFunction_continuous` applies to every
numerator and denominator. `rationalFunction_domain` is exactly the condition
that the denominator value is nonzero. The reciprocal searches internally for
separation from zero, and `CertifiedReciprocal.mul_reciprocal` proves its exact
inverse identity. These results quantify over arbitrary valid represented
inputs and coefficients; no monotonicity, turning points, or chosen margins
are supplied by the caller. Coefficient-name changes preserve evaluation and
the rational function's domain, by `polynomial_coefficients_congr`,
`rationalFunction_coefficients_congr`, and `rationalFunction_domain_congr`.
`Realizer.value` descends evaluation to
`Numbers.Real` without `noncomputable`. See `docs/FUNCTION_CONTINUITY.md` and
`scripts/check_function_continuity.lean`. The general complex-box counterpart
remains an explicit formalization target, alongside its existing arithmetic
validity and congruence laws.

## Increasing functions and inverses

Define increasing and decreasing by their value-level order inequalities on
the stated rational domain; distinguish strict from nonstrict versions.
Nonstrict monotonicity does not identify a unique inverse. Even strict
monotonicity alone does not ensure that every intermediate target is attained.

**Constructive strict intermediate value theorem (checked).** Let the primary
rational sampler on $[a,b]$ be strictly increasing, and let its justified
interval extension preserve validity. For every valid represented target
$y$ with $f(a)\le y\le f(b)$, a computation constructs a valid source value
$g(y)\in[a,b]$ and proves

$$
f^{\mathrm{ext}}(g(y))\simeq y,
\qquad
f^{\mathrm{ext}}(x)\simeq y\Longrightarrow x\simeq g(y).
$$

The target may be irrational. Neither a supplied continuity modulus nor an
inverse-separation schedule is required. At each positive-width bracket,
inspect its two interior thirds and refine value enclosures until one strict
side comparison is certified. Strict increase guarantees that one succeeds,
including when the target equals one of the sampled values. The retained
bracket has at most two thirds of the previous width. Coverage and continuity
prove the exact target identity. Equivalent target names give equivalent
answers, and the other inverse law holds for arbitrary valid source names;
clipping wide initial names to $[a,b]$ is internal.

`StrictMonotoneInverse.inverse`, `inverse_valid`, `inverse_target`,
`inverse_unique`, `inverse_evalOn`, and `inverse_congr` implement these claims.
`inverseValue` gives the corresponding function on `Numbers.Real` by quotient
lifting without `noncomputable`. The construction and audit are documented in
`docs/STRICT_MONOTONE_INVERSE.md`. `EndpointInverse` now proves the exact
forward value, uniqueness, both inverse laws, and name invariance directly
from valid endpoint schedules. Its `inverseValue` is also an ordinary quotient
definition and does not require the older matching-precision coverage law.
Squaring on $[0,1]$ is a checked instance; it is strictly increasing even
though its derivative at the endpoint zero vanishes. Squaring on the whole
real line is continuous but not an invertible strictly increasing function.

For a particular inverse, specify its source interval, target range, branch,
and the intended equation for the justified extension:

$$
f^{\mathrm{ext}}(g(y))\simeq y.
$$

Construct nested rational preimage brackets and prove the target containment
and shrinking estimates. Bisection, supporting-line/secant updates, or an
explicit algebraic formula may work for different functions. With represented
target values, do not rely on deciding exact equality at a midpoint. The
arctangent inverse in the next chapter is the principal reference case.
