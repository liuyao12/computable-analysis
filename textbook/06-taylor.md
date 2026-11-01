# Chapter 6. Taylor expansions from FTC

## Starting with the geometric functions

The starting objects are the geometric sine and cosine of Chapter 2.
Repeated definite-integral FTC generates their finite polynomial terms and
an iterated-integral remainder. Proving that remainder tends to zero then
gives the infinite series. The development order is integration and FTC,
infinite series, power series, then this derivation of Taylor expansions.

The checked trigonometric result here is the expansion about zero, at every
valid represented real input. Its finite form has $N$ terms:

$$
F(x)\simeq\sum_{j=0}^{N-1}\frac{D^jF(0)}{j!}x^j+R_N(x).
$$

The coefficients come from the actual geometric derivatives. No previously
written trigonometric power series or assumed integral identity supplies the
analytic argument.

## FTC across changes of curvature

`PiecewiseFTC.Pieces` assembles a finite tree of ordered rational intervals.
Each leaf supplies convex or concave supporting-slope evidence, or obtains it
from actual shrinking outer secants through `Pieces.ofOuter`. Different leaves
may use opposite curvature signs. They share the same endpoint function and
the same derivative sampler on their closed intervals, so endpoint values
are compatible at joins.

`Pieces.integral` sums independently computed local quadratures. The proof
concatenates local rectangle partitions, combines their error budgets, and
extends local increment bounds across every join. Thus `Pieces.hasIntegral`
certifies the result on the entire interval in the current rectangle relation.
`Pieces.ftc` proves

$$
\int_a^b DF(t)\,dt\simeq F(b)-F(a).
$$

`Pieces.integral_equiv` proves independence from the supplied decomposition,
including its grouping and rational breakpoints, whenever both decompositions
carry the required evidence for the same functions. The proof does not require
global monotonicity of the derivative. A cubic example changes curvature at
zero and exercises this theorem. Rational breakpoint evidence is the current
scope; irrational turning points need shrinking brackets and a proved vanishing
boundary contribution. Corners still do not acquire ordinary derivatives.

## The geometric trigonometric route

With the normalized sine and cosine names of Chapter 2, the checked cycle is

$$
D\sin(x)\simeq\pi\cos(x),\qquad
D\cos(x)\simeq-\pi\sin(x).
$$

`GeometricTrig.sin_derivative` and `cos_derivative` prove these identities at
every valid represented real input. Their derivative relation covers every
nearby rational secant, including secants crossing a quadrant join. The right
sides use the actual represented values `cosAt` and `sinAt`; callers supply no
quadrant choice or partition. The extension respects equivalent input names.

The proof uses real circle coordinates, sector-area estimates, and the
geometric arctangent inverse. It invokes neither a complex exponential nor a
sine/cosine series. For an ordered rational step $h$ with
$0<h\le\frac14$, `full_firstOrder_small` proves

$$
|F(u+h)-F(u)-h\,d_F(u)|\le1600h^2,
$$

where $d_F$ is the corresponding represented expression in the checked cycle.
The constant is a convenient rational bound, not an optimal one. The
quarter-circle estimate is proved from the actual inverse and evaluation
errors. At a join $c$, the two local remainders leave the additional term

$$
(v-c)\bigl(d_F(c)-d_F(u)\bigr).
$$

The proved derivative-sampler Lipschitz bound controls this term by a
quadratic error. Shared endpoint values justify the algebra at the join.
Division by the secant length gives an error tending to zero; covered
continuity of the derivative sampler identifies the real derivative.

`GeometricTaylorData.jet_derivative` now iterates this cycle: each rational
sampler `jet` has the next `jetAt` as its derivative at every valid represented
input. `jetAt_rational` and `jetAt_congr` preserve rational agreement and
input-name independence throughout the cycle. The initial coefficients are
obtained from geometric initial values by `jet_zero`, rather than asserted
from the formal series. The same file proves the rational uniform bound

$$
|D^nF(x)|\le8^n.
$$

`jetAt_small` certifies this estimate for arbitrary valid represented inputs.
The generous bound follows from the geometric coordinate bound and the
proved bound on the circle constant. It is sufficient input to a factorial
remainder theorem; it does not by itself prove that theorem.

## Repeated FTC produces the terms and remainder

For a rational angle $q$, use the segment parameter $t$ and the actual
geometric function

$$
G(t)=F(qt),\qquad 0\le t\le1.
$$

`GeometricFTCData.family` constructs its successive derivatives, retaining
the factors $q$ and $\pi$. This works for negative as well as positive $q$.
`GeometricFTCData.step` proves the data for FTC from the actual geometric
first-order estimates. `FTCRealOrder` removes the quadratic error by finite
subdivision. `LipschitzIntegralBounds` constructs tight represented rectangle
bounds with internal evaluator-width searches. This is a justified sufficient
integration route, not a required class of integrands.

FTC first gives the value difference as the integral of the geometric
derivative. Applying it to that derivative, and then repeating, integrates
constants into monomials and produces the next coefficient. In the checked
construction, write

$$
P_{N,k}(t)=\sum_{j=0}^{N-1}\frac{G^{(k+j)}(0)t^j}{j!},\qquad
R_{N,k}(t)=G^{(k)}(t)-P_{N,k}(t).
$$

`RepeatedFTC.polynomial_step` certifies the finite monomial integrations.
`remainder_hasIntegral` proves the successive substitutions as genuine
mathematical definite-integral statements:

$$
R_{N+1,k}(t)\simeq\int_0^t R_{N,k+1}(u)\,du,
\qquad R_{0,k}(t)=G^{(k)}(t).
$$

Thus the remaining term is an iterated integral of an actual geometric
derivative. `GeometricTaylorFTC.integral_remainder` instantiates every step.
The integral role is proved from finite derivative evidence and rectangle
bounds; it is not an endpoint agreement assumed in a record.

## Integrating the error bounds produces the factorial

The geometric bounds give

$$
|G^{(k)}(t)|\le B^k,\qquad B=8|q|.
$$

Starting with this bound, the induction in `RepeatedFTC.remainder_bound`
applies FTC and integral order to the positive and negative monomial
majorants. Each integration supplies the next denominator:

$$
|R_{N,k}(t)|\le\frac{B^{k+N}t^N}{N!}.
$$

At the end of the segment this yields the finite trigonometric remainder

$$
|R_N(q)|\le\frac{(8|q|)^N}{N!}.
$$

Only after this geometric FTC argument does
`GeometricTaylorFTC.initial_coefficients` identify the resulting initial-value
cycle with the alternating powers of the represented geometric constant.
`rational_remainder` is the resulting finite polynomial inequality.

## Arbitrary represented real inputs

`TaylorPolynomialValues` proves whole-bracket images of the finite real
polynomials. `GeometricTaylorReal.remainder_bound` combines these with the
geometric rational-to-real extension. It proves the finite remainder inequality
for every valid represented real, with represented powers of both the input
and the geometric circle constant. On an internally chosen bounded input
bracket, the rational budget has the form

$$
|R_N(x)|\le\frac{C^N}{N!}.
$$

The chosen bracket and precision searches are internal. The public identities
require only a valid represented input. Different input names may yield
different error budgets, but the exact values agree.

## The remainder vanishes and the series follows

`factorial_shrinks` proves that the finite FTC error tends to zero. The
resulting exact identities, in our normalized angle convention, are

$$
\sin(x)\simeq
\sum_{k=0}^{\infty}\frac{(-1)^k(\pi x)^{2k+1}}{(2k+1)!},
$$

$$
\cos(x)\simeq
\sum_{k=0}^{\infty}\frac{(-1)^k(\pi x)^{2k}}{(2k)!}.
$$

`GeometricTaylorSeries.sin_taylor_converges` and `cos_taylor_converges`
state convergence of the explicit `sineTerm` and `cosineTerm` streams in
these formulas to the geometric functions. `selected_terms_closed` proves
their agreement with the coefficients obtained from repeated FTC.
`RepresentedSeries.HasSum` specifies convergence independently of the selected
sum algorithm and has a proved uniqueness law.

`sinTaylor` and `cosTaylor` compute rational-input Taylor enclosures;
`sinTaylorAt` and `cosTaylorAt` evaluate them at arbitrary valid represented
inputs. Their boxes contain the finite-polynomial evaluation uncertainty and
the proved FTC remainder. Finite prefix intersections enforce nesting.
`sin_taylor` and `cos_taylor` prove exact value equivalence with `sinAt` and
`cosAt`. Rational agreement and input-name invariance are proved too.
The evaluator uses the current geometric computation of the circle constant;
using a faster proved-equivalent constant is a separate optimization.

## Exponential from its Euler ODE construction

The exponential here is the numerical Euler solution of $E'=E$ with
$E(0)=1$. It is not introduced by a factorial series.
`EulerTaylorFTC` derives finite supporting increments from the already checked
Euler secant bounds. `Step.ofSupportingIncrements` turns those increments and
a proved Lipschitz bound for the derivative into the quadratic first-order
evidence needed by FTC.

On a bounded segment, choose a certified rational value budget $M>0$ and put

$$
G_k(t)=\frac{q^kE(qt)}{M},\qquad 0\le t\le1.
$$

The checked `family_step` proves that the derivative of $G_k$ is $G_{k+1}$,
for either sign of $q$. Normalization gives $|G_k(t)|\le|q|^k$, so the same
`RepeatedFTC` construction used above generates the finite polynomial and
successive genuine integral remainders. Restoring $M$ gives

$$
\left|E(q)-\sum_{k=0}^{N-1}\frac{q^k}{k!}\right|
\le M\frac{|q|^N}{N!}.
$$

`EulerTaylorSeries.remainder_bound` transports this finite result to every
valid represented input, using the actual Euler enclosure and whole-box
polynomial images. The chosen input bound $C$ yields error $MC^N/N!$.
Its proved decay gives the exact identity

$$
E(x)\simeq\sum_{k=0}^{\infty}\frac{x^k}{k!},\qquad x\in\mathbb R.
$$

`hasSum` states convergence of these actual terms; `series_valid` and
`series_exact` certify the executable error-padded sum. `series_congr` proves
name invariance. This is an additional proof: the earlier finite-binomial
comparison in `EulerSeriesIdentity` remains valid and is not a dependency of
the new convergence argument.

## Logarithm by integrating finite reciprocal division

The logarithm remains the fixed-dyadic integral of the reciprocal kernel,
extended to positive represented inputs by monotone endpoint bounds. Its
Maclaurin formula is naturally written for $\log(1+x)$:

$$
\log(1+x)\simeq\sum_{k=0}^{\infty}
\frac{(-1)^k x^{k+1}}{k+1},\qquad -1<x\le1.
$$

`LogTaylorFTC.hasIntegral` first gives the genuine reciprocal-kernel integral
role of the translated quadrature logarithm, using its supporting secants.
For the two signs of a rational displacement, finite geometric division
bounds that kernel by its finite polynomial plus or minus the monomial
$t^N/m$. Here $m>0$ bounds the denominator on the entire segment; the
negative displacement requires staying strictly before the pole.

`TaylorIntegralPolynomial.step` integrates each monomial by checked FTC.
Integral order then proves the finite error, without proposing an infinite
series in advance. With $r=|x|\le1$, its bound is

$$
\frac{r^{N+1}}{m(N+1)}\le\frac{1}{m(N+1)}.
$$

`LogTaylorSeries.remainder_bound` proves the latter bound for arbitrary valid
represented inputs on the stated domain. A positive-domain search finds
$m$ internally; clipping repairs early input boxes while preserving the
represented value. Whole-box polynomial images and `MonotoneLogarithm.eval_covers`
account for input and endpoint evaluation errors. The error vanishes even at
$x=1$. The endpoint $x=-1$ is excluded because its argument vanishes there.
`hasSum`, `series_valid`, `series_exact`, and `series_congr` prove convergence,
valid computation, exact quadrature agreement, and representation invariance.

This proves the logarithm series independently of identifying the inverse
quadrature logarithm with the Euler exponential. That separate comparison
remains an open foundation obligation.

## Arctangent from geometric sector area

`ArctanTaylorFTC.hasIntegral` derives the reciprocal-square kernel integral
from the geometric sector computation and its finite supporting secants, on
each segment $[0,r]$ with $r\le1$. The exact finite identity for
$1/(1+t^2)$ gives a derivative error bounded by $t^{2N}$. Integrating its
monomial majorant gives

$$
\left|\arctan(r)-\sum_{k=0}^{N-1}
\frac{(-1)^kr^{2k+1}}{2k+1}\right|
\le\frac{r^{2N+1}}{2N+1}.
$$

`ArctanTaylorSeries` extends the geometric rational sampler by oddness to
$[-1,1]$. The original rectangle bounds prove strict increase and a
Lipschitz bound of one. Its represented evaluator is constructed from
scheduled monotone endpoint values, including the endpoints; it is not
defined by the series. `rational_geometric` identifies the nonnegative
rational branch with the original geometric arctangent.

The uniform represented-input error is $1/(2N+1)$. Its decay proves

$$
\arctan(x)\simeq\sum_{k=0}^{\infty}
\frac{(-1)^kx^{2k+1}}{2k+1},\qquad -1\le x\le1.
$$

Both endpoints are included. `hasSum`, `series_valid`, `series_exact`, and
`series_congr` certify the actual signed terms and their exact geometric sum.
Using this computation outside the series convergence interval requires a
separately justified argument reduction.

## Reusing the strategy

The [Taylor from FTC construction skill](../skills/taylor-from-ftc/SKILL.md)
records the procedure for contributing agents. Its full instructions also
accompany the combined mission Markdown. For another constructed function,
the same questions guide the development:

1. What are the actual function, its normalization, and its successive derivatives on the entire segment?
2. Which justified FTC steps generate the finite polynomial and express each remainder as the integral of the preceding remainder of the next derivative?
3. What majorants can be integrated to bound that actual remainder?
4. Does the resulting bound tend to zero with an explicit precision schedule?
5. How do whole-bracket enclosures transfer the result to arbitrary valid represented inputs and identify the represented sum?

For an expansion about $a$, put $G(t)=F(a+(x-a)t)$ on $[0,1]$.
This keeps negative displacements in the same argument, with the chain factors
$(x-a)^k$ included. A bound $M_N$ for the actual $N$th derivative of $F$
throughout the segment yields the finite remainder estimate

$$
\left|F(x)-\sum_{j=0}^{N-1}\frac{F^{(j)}(a)(x-a)^j}{j!}\right|
\le\frac{M_N|x-a|^N}{N!}.
$$

One must still prove that this error vanishes. Smoothness alone does not imply
Taylor convergence. The checked generic construction uses geometrically
bounded derivative families; broader growth conditions and centers require
their own proofs.

This is also a way to preserve mathematical exploration. We can begin with
the geometric functions, discover the successive integral corrections, and
only then recognize the infinite series. The text should retain those
motivations and intermediate discoveries, even when the final theorem admits
a shorter proof.

## Checked scope

The geometric sine/cosine expansions, Euler exponential expansion on the
whole represented real domain, logarithm expansion on $-1<x\le1$, and geometric
arctangent expansion on $[-1,1]$ are checked, including finite errors, represented
series computations, exact agreement, and representation invariance. `scripts/check_geometric_taylor.lean` audits the proof dependencies
and requires actual geometric FTC dependencies in each principal result.
The proof uses no complex-number mathematics, Euler identity, ODE uniqueness,
or pre-existing trigonometric series evaluator.

The general piecewise convex/concave FTC results above remain available.
Separate curvature certificates for geometric sine/cosine, general expansion
centers, and broader integration laws are further work. They are not
hypotheses silently added to these global trigonometric identities. The legacy
`Taylor.FTCStepAt` candidate-agreement record is not used in this proof.

`scripts/check_elementary_taylor.lean` additionally audits the exponential,
logarithm, and arctangent proof routes and executes their endpoint, sign,
normalization, and shrinking-error checks. Its ordinary downstream definitions
require no `noncomputable` declaration.
