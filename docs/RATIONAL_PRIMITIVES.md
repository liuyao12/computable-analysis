# Elementary primitives of rational and trigonometric rational functions

The checked analytic theorem now constructs local elementary primitives for
**every rational numerator and every denominator supplied as distinct rational
linear pole blocks, with arbitrary positive multiplicities**. It computes the
partial fractions, a positive pole-free neighborhood, and valid elementary
evaluators, then proves the original quotient is their interval derivative.
The algebraic integration algorithm now also supports arbitrary computable-real
coefficients. Concrete logarithm/arctangent derivatives with computable coefficients are
also checked; full finite assembly and the trigonometric corollary remain open. All proofs use the project's own
rational-interval foundation; no Mathlib real or complex numbers are used.

## Factorization can be assumed as input

Yes: FTA is needed to establish existence of a factorization for an arbitrary
denominator, but it is not needed inside the integration algorithm once a
factorization is supplied. The real form is
\[
q(x)=c\prod_i(x-a_i)^{m_i}
      \prod_j\bigl((x-u_j)^2+v_j\bigr)^{n_j},
\qquad c\ne0,\quad v_j>0.
\]
A quadratic with negative discriminant has this form after completing the
square and extracting its leading coefficient. `generalQuadratic_value`
checks this normalization for every rational quadratic with negative
discriminant, including a negative leading coefficient. Repeated equal factors are
grouped into one block.

`ComputableFactoredAlgebra.FactoredRational` accepts this factored form with
**arbitrary certified computable-real coefficients**, including transcendental
coefficients. Each coefficient is an arithmetic expression whose parameters
are the project's `Real` interval algorithms. The numerator and leading
coefficient use the same representation. No algebraicity restriction is
imposed when factorization is supplied.

`certifyFactors` checks positivity and residual-denominator separation using
rational interval endpoints at a supplied precision. A failed check means the
certificate is insufficient; it does not assert equality or zero. Repeated
identical factors must be grouped into a single block. `primitive` computes
every partial-fraction coefficient and its elementary formula.
`FactoredRational.primitive_correct` proves raw-computation equivalence between
the formula's represented formal derivative and the original factored
rational function, at certified domain points and successful evaluation
precisions. These evaluations return valid shrinking interval computations,
not rational stand-ins for the coefficients.

The proof checks arithmetic identities for all sufficiently fine rational
samples of the coefficient boxes, then transfers them to `RealRaw.Equiv`.
It neither selects completed-real values nor assumes a partial-fraction
identity. `RationalFactoredPrimitives.Factorization` remains the exact rational
specialization with a factorization identity for an existing `RatFun`.

For quadratic division, write \(y=x-a\), \(Q=y^2+b\), and reduce the numerator
and residual denominator to \(u_1y+u_0\) and \(v_1y+v_0\). Their quotient
modulo \(Q\) is \(Ay+B\), where
\[
D=v_0^2+bv_1^2>0,\qquad
A=\frac{u_1v_0-u_0v_1}{D},\qquad
B=\frac{bu_1v_1+u_0v_0}{D}.
\]
The algorithm subtracts this contribution, divides out one copy of \(Q\),
and repeats. The norm positivity and every division identity are proved.
No square-root evaluator is required for this algebraic step.

The irrational regression uses the existing bisection computation of
\(r=\sqrt{2}\), with integrand
\[
\frac{1+rx}{(x-r)\bigl((x-r/2)^2+r\bigr)^2}.
\]
Lean checks factor certificates, successful evaluation of the generated
coefficients and formal derivative at zero, and equivalence with the original
quotient. Zero reciprocals and duplicate irrational pole blocks are rejected.
The strict axiom audit includes these closed examples.

FTA remains relevant to obtaining a factorization from an arbitrary input
polynomial. It is independent of this integration algorithm. What is still
missing is an analytic evaluator and actual `HasDerivativeOnInterval` for the
computed formulas with general computable coefficients. In particular, the
quadratic base atoms below now have concrete certificates, but are not yet
assembled through the full formula compiler.

## Concrete logarithm and arctangent certificates

`ComputableLogarithmChart` builds the local logarithm series with an arbitrary
computable complex slope \(m\). A finite interval bound \(M>0\) determines
\(r=1/(2M)\). On \(|t|\le r\), the candidates are the finite sums
\[
 L_n(mt)=\sum_{k=1}^n\frac{(-1)^{k+1}(mt)^k}{k},
 \qquad K_m(t)=\frac{m}{1+mt}.
\]
Both real coordinates are certified interval computations. The finite secant
estimate bounds the error by
\(2M^2|h|+8M2^{-n}\). A separate coefficient perturbation estimate controls
replacement of the computable slope by rational samples. A common sampling
stage retains the algebraic relationships between derived coefficients.
`widthStage` searches rational interval endpoints; validity proves termination
without supplying a noncomputable runtime precision oracle.

`Coefficient.hasDerivative` constructs `HasDerivativeOnInterval` for both
coordinates, with precision depending on the secant step. `weightedHasDerivative`
does the same for arbitrary computable constant multiples, from explicit
weighted finite sums. No derivative or chain-rule hypothesis is supplied.

For a computable pole \(a\) and rational center \(c\), a successful finite
reciprocal test supplies \(m=(c-a)^{-1}\). `simplePole_derivative_equiv`
identifies the real-coordinate derivative with the independently evaluated
\((x-a)^{-1}\) wherever the chart and target reciprocal certificates apply.
For a purely imaginary slope \(is\), `arctan_valueSample` proves that the
imaginary candidates at even stages are exactly the standard arctangent
Taylor sums. `arctan_derivative_equiv` identifies their derivative with
\(s/(1+s^2(x-c)^2)\).

For quadratics, the concrete interface uses
\[
 Q(x)=(x-a)^2+b^2,\qquad b\ne0,\qquad
 m=\frac{c-a-ib}{Q(c)}.
\]
Twice the real coordinate gives a local logarithm primitive with derivative
\(2(x-a)/Q(x)\); multiplying the imaginary coordinate by \(-1/b\) gives
one with derivative \(1/Q(x)\). The `quadraticLog_derivative_equiv` and
`quadraticArctan_derivative_equiv` theorems compare those derivative computations
to the original coefficient evaluator. They require successful finite inversions
of \(Q(c)\), \(b\), and \(Q(x)\), and chart membership. These are concrete
local log-series charts; global branch identities are not asserted.

`ComputablePrimitiveDerivativeExamples` checks the irrational pole
\(a=\sqrt2\), the arctangent scale \(s=\sqrt2\), and the quadratic
\(Q(x)=(x-\sqrt2)^2+(\sqrt2)^2\). Each has an actual interval derivative
certificate and a reciprocal/kernel identification at \(x=1/16\).

The formal factorization interface instead takes \((x-a)^2+B\) with a
positive computable \(B\). Supplying and verifying a width \(b\) with
\(b^2=B\), then assembling all repeated-factor terms with computable
coefficients, remains work for the complete compiler theorem.

## Precise target

For polynomials \(p,q\) with certified computable-real coefficients, on a rational interval \([a,b]\) equipped
with an explicit certificate \(|q(x)|\geq\delta>0\), construct an elementary
formula \(F\), a valid interval evaluator for it, and a finite-difference
certificate for
\[
F'(x)=\frac{p(x)}{q(x)}.
\]
Elementary formulas may use certified computable-real constants, arithmetic operations,
logarithms of absolute values, and arctangents. Restricting all constants in
the answer to rational numbers would be too strong: already
\(1/(x^2-2)\) naturally requires \(\sqrt{2}\). A denominator may also have
algebraic roots of higher degree; roots need not be expressible by radicals.

Poles are excluded. This is a real interval theorem; a complex logarithm
requires a branch, and a meromorphic rational function need not have a
single-valued primitive on an entire punctured complex domain.

## The finite integration proof

Polynomial division and real algebraic factorization reduce the integrand to
a polynomial and finitely many terms of the forms
\[
\frac{c}{(x-a)^m},\qquad
\frac{A(x-a)+B}{((x-a)^2+b)^m},\qquad b>0,\quad m\geq1.
\]
The polynomial primitive is computed coefficient by coefficient. Linear
poles give
\[
\int\frac{c}{x-a}\,dx=c\log|x-a|,\qquad
\int\frac{c}{(x-a)^m}\,dx=
 -\frac{c}{(m-1)(x-a)^{m-1}}\quad(m>1).
\]
Writing \(u=x-a\), \(Q=u^2+b\), and \(I_m=\int Q^{-m}\,dx\), the
positive-quadratic reduction is
\[
I_1=\frac{1}{\sqrt b}\arctan\frac{u}{\sqrt b},\qquad
I_{m+1}=\frac{u}{2mbQ^m}+\frac{2m-1}{2mb}I_m.
\]
The linear numerator contributes
\[
\int\frac{Au}{Q}\,dx=\frac A2\log Q,\qquad
\int\frac{Au}{Q^{m+1}}\,dx=-\frac{A}{2mQ^m}.
\]
These are terminating recursions on pole multiplicity. The Lean syntax uses
natural indices one less than the displayed pole order.

`RationalPrimitiveFormula.quadraticPrimitive_correct` proves the reduction
for every multiplicity. `NormalForm.primitive_correct` proves the formal
derivative identity for every finite supplied sum, and
`Decomposition.primitive_correct` transfers it to a `RatFun` using a supplied
partial-fraction identity. `primitive_regular` proves the resulting formula
is pointwise defined at every permitted input. These theorems do **not**
produce `HasDerivativeOnInterval` or evaluate logarithms and arctangents.

The implemented normal forms have rational coefficients, centers, and
positive quadratic constants. Thus their existence is **not** a valid
additional assumption for *every* rational function. General input requires
the algebraic-constant extension and a decomposition algorithm.

## Analytic polynomial and logarithm primitives

`RationalPrimitivePolynomial.hasDerivative` realizes the formal polynomial
primitive by exact rational boxes and proves its two-sided interval derivative
on **every rational interval**, for an arbitrary finite coefficient list.
`primitiveSum_zero` identifies the analytic evaluator with the compiler's
literal coefficient primitive.

`RationalPrimitiveLogarithm.hasDerivative` proves
\[
\frac{d}{dx}\log(1+x)=\frac1{1+x},\qquad -\frac12\le x\le\frac12.
\]
The logarithm is the real part of the project's stabilized Taylor series,
with validity and geometric widths. A finite quadratic remainder estimate is
converted to `HasDerivativeOnInterval`; its evaluation stage depends on the
step, paying explicitly for uncertainty after division by that step. The
geometric derivative boxes contain the **exact rational reciprocal**.

`affineHasDerivative` handles every nonzero rational slope, of either sign.
For arbitrary rational \(a,z\) with \(z\ne a\), put \(r=|z-a|/2\).
`poleRadius_pos` and `simplePole_hasDerivative` construct
\[
F_{a,z}(x)=\log\left(\frac{x-a}{z-a}\right),\quad
F'_{a,z}(x)=\frac1{x-a},\quad x\in[z-r,z+r].
\]
The argument of the logarithm is positive on this interval, on either side
of the pole. The only supplied hypothesis is \(z\ne a\), not a derivative,
limit, partial-fraction identity, or branch certificate. This is a local
normalized logarithm; agreement of additive constants on larger overlaps
is not asserted here.

`HasDerivativeOnInterval.add` now combines any two derivative certificates
on a common interval, even when both their original schedules differ.
Nestedness allows refinement to the larger runtime stage; three times the
original tolerance pays for refinement, and finer requested precisions pay
for addition. The product of the two natural step precisions synchronizes
step bounds, including zero-precision edge cases. The checked polynomial
plus logarithm example exercises this automatic synchronization.

These results close the polynomial and simple-logarithm analytic atoms. They
do not yet provide analytic soundness for every constructor of `Formula`.

## Automatic partial fractions and analytic assembly

`RationalPartialFractions.removePole` computes the coefficient at each pole
by evaluation and removes it by synthetic division. Iteration handles all
multiplicities, then processes the remaining distinct pole blocks.
`decomposition` proves the resulting identity and domain regularity for every
numerator. `ofFactorization` accepts a checked rational linear factorization
of a `RatFun`, including a nonunit leading coefficient. It does not assume a
partial-fraction identity.

`RationalPrimitivePowers.hasDerivative` proves the reciprocal-power primitive
on any rational interval with an explicit lower bound for the distance to its
pole. Negative-side intervals and negative coefficients are supported.
Automatic addition and scaling choose the required precision schedules.

For poles \(a_i\) and a permitted rational center \(z\), the assembly chooses
\[
r=\min\bigl(1,|z-a_1|/2,\ldots,|z-a_k|/2\bigr)>0.
\]
`radius_pos` and `denominator_near` prove this is a nondegenerate pole-free
interval. `RationalPrimitiveAssembly.splitPrimitive` constructs a
`PrimitiveOn` containing a valid function, an `Elementary` witness for that
actual evaluator, and a `HasDerivativeOnInterval` whose target is the
original quotient. The witness permits only polynomial and reciprocal-power
atoms, normalized logarithms, scaling, addition, and restriction. It does not
classify arbitrary interval algorithms as elementary.

A regression computes, rather than assumes, the decomposition
\[
\frac{1+2x}{x^2(x-1)^3}
=-\frac1{x^2}-\frac5x+\frac3{(x-1)^3}
 -\frac4{(x-1)^2}+\frac5{x-1}.
\]
`automaticMixed_hasDerivative` assembles its analytic primitive around
\(z=2\), on \([3/2,5/2]\), and `automaticMixed_elementary` certifies the
resulting evaluator. This is a complete local theorem for rationally split
denominators, not a factorization theorem for arbitrary denominators.

## Why the trigonometric corollary follows

On a half-angle chart, set \(t=\tan(\theta/2)\). Then
\[
\sin\theta=\frac{2t}{1+t^2},\qquad
\cos\theta=\frac{1-t^2}{1+t^2},\qquad
d\theta=\frac{2}{1+t^2}\,dt.
\]
Consequently the transformed integrand
\[
R\!\left(\frac{2t}{1+t^2},\frac{1-t^2}{1+t^2}\right)
\frac{2}{1+t^2}
\]
is rational. Its elementary primitive, composed with the half-angle
coordinate, gives the desired local primitive. An antipodal chart, with
\(u=-\cot(\theta/2)\), covers the omitted points; the same rational formulas
have both circle coordinates negated and the same positive Jacobian.
An interval crossing a chart boundary needs overlap constants and gluing.

`TrigonometricRationalization.Expr.pullback_correct` proves the transformed
rational evaluation for **every expression and every rational chart input**.
`pullback_defined_iff` proves exact preservation of its domain, including
identically undefined expressions. `rational_circle_chart_cover` proves
two-chart coverage of the rational circle. Identifying these coordinates
with the chosen represented sine and cosine, and transporting analytic
derivatives through the angle chart, remain separate tasks.

The compiler intentionally does not cancel holes. For inversion it replaces
\(p/q\) by \(q^2/(pq)\), retaining the condition \(q\neq0\).
This ensures that \(1/(1/x)\) remains undefined at zero, as does
\(0\cdot(1/x)\).

## Checked examples and trust

The regression module checks
\[
\int\frac{dx}{x(x-1)}=\log|x-1|-\log|x|+C,
\qquad
\int\frac{dx}{(1+x^2)^2}=
\frac{x}{2(1+x^2)}+\frac12\arctan x+C
\]
at the stated formal-derivative level, as well as the rational pullback of
\(1/(1+\cos\theta)\), which equals one on the first chart. It also checks
undefined reciprocals and preservation of a genuine sine pole.

Run:

```sh
lake build ComputableAnalysis.RationalPrimitiveExamples
lake env lean scripts/check_rational_primitives.lean
lake env lean scripts/check_computable_primitive_runtime.lean
```

The audit accepts only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` dependencies. It rejects unfinished proofs, custom axioms, and
native-decision axioms, and checks the import closure for Mathlib. The
constructors themselves are executable finite rational algorithms.

## Remaining work before the general theorem can be claimed

1. Construct a certified factorization of an arbitrary input polynomial when
   it is not supplied. Partial fractions from supplied computable-real linear
   and positive quadratic factors are already computed and checked.
2. Connect the positive quadratic constant in the factorization interface to
   a certified width for the concrete quadratic base primitives.
3. Assemble the computable-coefficient polynomial, reciprocal-power, and
   quadratic recurrence terms with the new concrete logarithm/arctangent
   certificates. Irrational simple poles and quadratic base terms now have
   actual `HasDerivativeOnInterval` certificates; the full formula does not yet.
4. Identify the two angle charts with the established sine and cosine
   evaluators, then prove the chain rule and overlap gluing.

General `ComputableFTA` in `FTA.lean` is currently a target proposition, not a
theorem available to discharge the first obligation. Defining formal
differentiation rules does not discharge the third obligation.
