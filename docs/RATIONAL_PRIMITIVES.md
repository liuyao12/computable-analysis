# Elementary primitives of rational and trigonometric rational functions

The requested general analytic theorem is **not yet proved**. The checked
addition is the finite integration algorithm for supplied rational partial
fractions, together with a domain-preserving rationalization of every rational
expression in circle coordinates. It imports only the project's polynomial
and rational foundation; no Mathlib real or complex numbers are used.

## Precise target

For rational polynomials \(p,q\), on a rational interval \([a,b]\) equipped
with an explicit certificate \(|q(x)|\geq\delta>0\), construct an elementary
formula \(F\), a valid interval evaluator for it, and a finite-difference
certificate for
\[
F'(x)=\frac{p(x)}{q(x)}.
\]
Elementary formulas may use real algebraic constants, rational operations,
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
```

The audit accepts only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` dependencies. It rejects unfinished proofs, custom axioms, and
native-decision axioms, and checks the import closure for Mathlib. The
constructors themselves are executable finite rational algorithms.

## Remaining work before the general theorem can be claimed

1. Construct real algebraic factorization and partial fractions for arbitrary
   nonzero rational denominators; extend the finite algebra to those constants.
2. Realize each elementary formula by valid `RealRaw` interval computations,
   with explicit width schedules and denominator/branch separation.
3. Prove analytic differentiation soundness of the formula compiler using
   `HasDerivativeOnInterval`, including synchronized sums and compositions.
4. Identify the two angle charts with the established sine and cosine
   evaluators, then prove the chain rule and overlap gluing.

General `ComputableFTA` in `FTA.lean` is currently a target proposition, not a
theorem available to discharge the first obligation. Defining formal
differentiation rules does not discharge the third obligation.
