# Euler's formula as a source of applications

This is a downstream application chapter. Its source and Lean modules belong
in the companion package; the independent foundation supplies the number
values, geometric functions, exponential constructions, and checked calculus.
The route through Euler's formula is part of what this chapter preserves.

## A series-first reading order

One can first meet the factorial exponential series and collect its even and
odd terms. In our normalized coordinate this leads to

$$
Z(x)=\sum_{n=0}^{\infty}\frac{(i\pi x)^n}{n!}
    =\cos(\pi x)+i\sin(\pi x).
$$

The equality uses the actual geometric sine and cosine. It does not introduce
new trigonometric functions by writing down coefficient streams.
`EulerTrigApplications.series_euler_formula` is the checked entry point for
this reading order. The foundation also has an independent Euler ODE route;
its comparison theorems justify moving between the computations.

This reading order does not prescribe a numerical implementation. Practical
exponential, sine, and cosine evaluators may choose different argument
reductions and certified local approximations for different inputs and
precisions. Multiplication, inversion, periodicity, and symmetry then
reconstruct the value. The resulting computation needs its own error bounds,
validity, and exact comparison proof. The geometric, Euler-method, and series
constructions retain their mathematical and explanatory roles regardless of
which evaluator is fastest for a particular calculation.

Write the geometric functions and the imaginary exponential as

$$
C(x)=\cos(\pi x),\qquad S(x)=\sin(\pi x),\qquad Z(x)=C(x)+iS(x).
$$

We now ask what can be learned from that identity. The applications below
actually use the proved Euler formula. Their theorem-dependency audit requires
`EulerImaginary.euler_identity`; importing its module is not sufficient.

## Reflection and the negative-angle identities

Conjugating a finite Euler step reflects its imaginary coefficient. Thus the
whole finite computation at the negative input is the conjugate computation.
Passing to the proved limits gives

$$
Z(-x)=\overline{Z(x)}.
$$

`EulerRotationReflection.conjugation` proves this law without assuming the
trigonometric negative-angle identities. Taking real and imaginary parts of
Euler's formula then gives

$$
C(-x)=C(x),\qquad S(-x)=-S(x).
$$

These are `EulerTrigApplications.cosine_even` and `sine_odd`. They hold for
any valid represented real input, including irrational inputs, independently
of its chosen name. No quadrant or monotonicity partition is supplied by
the caller.

Adding and subtracting the two Euler formulas also gives

$$
Z(x)+Z(-x)=2C(x),\qquad Z(x)-Z(-x)=2iS(x).
$$

`cosine_exponential_form` and `sine_exponential_form` check those exact complex
identities. They explain how a trigonometric expression can be rewritten in
exponential terms; the derivation remains visible in the formal dependency
graph.

## Multiplying the convergent series

For arbitrary represented complex inputs, write

$$
P_N(z)=\sum_{k=0}^{N-1}\frac{z^k}{k!}.
$$

Multiplying two finite prefixes gives a rectangle of pairs of indices. The
complete diagonals inside that rectangle satisfy the finite identity

$$
\sum_{k=0}^{n}\frac{z^k w^{n-k}}{k!(n-k)!}
=\frac{(z+w)^n}{n!}.
$$

This is the binomial theorem with factorial denominators. It is checked by
`ModularForms.ExponentialDiagonal.complete` and its executable-name bridge
`raw_complete`. It does not exchange any infinite sums.

Choose a rational radius \(R>0\) bounding both coordinates of \(z\),
\(w\), and \(z+w\). The factorial coefficients admit geometric bounds with
any positive ratio. The proof uses

$$
K=\frac{1}{32R},\qquad
B=\operatorname{factorialSeriesFiniteBound}(K^{-1}).
$$

Each coordinate of the omitted finite rectangle is bounded in absolute value
by

$$
32B^2(8KR)^N.
$$

`exponential_finite_product_bound` proves that estimate. Its bound tends to
zero, as do the three series-prefix errors. Passing these finite identities
to the actual sums proves

$$
\exp(z)\exp(w)=\exp(z+w).
$$

`ModularForms.exponential_series_addition` is the convergence argument;
`entireExponential_addition` chooses and reconciles the bounds internally.
Its public statement applies to every pair of valid represented complex
inputs. It asks for no radius, truncation choice, or regrouping assumption.
The raw-value construction and these laws are separated from the broader
holomorphic packaging into `EntireExponentialValue`,
`ExponentialSeriesAddition`, and `ExponentialValueAddition`.

## Connecting that product to the geometric circle

The complex series evaluator and our geometric computation initially have
different algorithms. `EulerSeriesMultiplication.imaginary_prefix` proves
that their finite factorial prefixes at \(i\pi x\) agree coordinate by
coordinate. The geometric error is precisely the remainder already derived
by repeated FTC, while the general complex evaluator supplies its own
certified tail. Both errors tend to zero.

Consequently `factorial_circle` proves the actual represented-value
agreement, and `factorial_euler` connects it to the existing Euler formula.
Applying complex exponential addition now gives

$$
Z(x)Z(y)=Z(x+y).
$$

This is `rotation_addition`. Multiplying the coordinates in Euler's formula
then yields

$$
\begin{aligned}
C(x+y)&=C(x)C(y)-S(x)S(y),\\
S(x+y)&=C(x)S(y)+S(x)C(y).
\end{aligned}
$$

`EulerTrigAddition.addition` proves both laws for arbitrary valid represented
real inputs. `difference` combines them with the negative-angle identities:

$$
\begin{aligned}
C(x-y)&=C(x)C(y)+S(x)S(y),\\
S(x-y)&=S(x)C(y)-C(x)S(y).
\end{aligned}
$$

The source of the identities matters: these proofs use the Cauchy product,
the geometric FTC remainder, and Euler's formula. The audit checks those
dependencies explicitly.

## Integer powers and de Moivre's formula

Repeated multiplication gives, first for nonnegative integers,

$$
\bigl(C(x)+iS(x)\bigr)^n=C(nx)+iS(nx).
$$

For negative integers we first need a justified inverse. Exponential addition
and its value at zero prove

$$
\exp(z)\exp(-z)=1,
\qquad Z(x)Z(-x)=1.
$$

`EulerDeMoivre.exponential_inverse` proves the first identity for every valid
represented complex input. `circle_inverse` proves the second for the
geometric circle. `circleUnit` packages the actual circle computation and its
proved reciprocal. Its integer-power algorithm uses that reciprocal for
negative exponents. `CertifiedUnit.reciprocal_unique` proves that another
justified reciprocal gives the same value; this convention does not favor
one reciprocal algorithm.

`EulerDeMoivre.de_moivre` therefore proves

$$
\boxed{\bigl(\cos(\pi x)+i\sin(\pi x)\bigr)^n
=\cos(\pi nx)+i\sin(\pi nx),\qquad n\in\mathbb Z.}
$$

It applies to every valid represented real \(x\). `de_moivre_congr` proves
independence of the input name, and `de_moivre_value` states the same identity
as equality in our mathematical complex quotient. The computation definitions
require no `noncomputable` declaration.

## Double angles and products

`EulerTrigProducts.cosine_double` and `sine_double` specialize addition:

$$
C(2x)=C(x)^2-S(x)^2,\qquad S(2x)=2S(x)C(x).
$$

Its `product_to_sum` theorem derives all four formulas:

$$
\begin{aligned}
C(x)C(y)&=\tfrac12\bigl(C(x+y)+C(x-y)\bigr),\\
S(x)S(y)&=\tfrac12\bigl(C(x-y)-C(x+y)\bigr),\\
S(x)C(y)&=\tfrac12\bigl(S(x+y)+S(x-y)\bigr),\\
C(x)S(y)&=\tfrac12\bigl(S(x+y)-S(x-y)\bigr).
\end{aligned}
$$

These are consequences of the preceding theorem, rather than separately
checked coincidences of formulas. They prepare the reduction of products and
higher powers to elementary definite integrals.

## A first family of definite integrals

Let \(A\) and \(B\) be arbitrary represented real coefficients, and let
\(a\le b\) be rational endpoints. The normalized derivative laws are

$$
S'(t)=\pi C(t),\qquad C'(t)=-\pi S(t).
$$

Consequently the endpoint expression suggested by the exponential coordinates
is

$$
F(t)=\frac{A S(t)-B C(t)}{\pi},\qquad F'(t)=A C(t)+B S(t).
$$

The definite-integral result is

$$
\int_a^b \bigl(A\cos(\pi t)+B\sin(\pi t)\bigr)\,dt
=\frac{A\bigl(S(b)-S(a)\bigr)-B\bigl(C(b)-C(a)\bigr)}{\pi}.
$$

`EulerTrigIntegralApplications` constructs the finite derivative evidence,
including the represented reciprocal of the proved nonzero geometric
\(\pi\). The coordinate comparison used here comes from the Euler formula
through `EulerTrigApplications.euler_components`.

The numerical integral uses finite lower and upper rectangles of the original
geometric integrand, with independently selected evaluation precision. Prefix
intersections repair nesting. It does not evaluate the displayed closed form
to obtain its answer. `FTCStepQuadrature` proves validity, the actual
`Integral.HasIntegral` role, and the endpoint identity from the supplied
first-order and variation evidence.

The worked application proves the integrand and endpoint comparisons,
`hasIntegral`, and `definite_integral`. Its public
`definite_integral_of_hasIntegral` theorem applies to any supplied integral
witness at the stated scope, and `representation_equiv` proves that equivalent
coefficient names give equivalent results. The coefficients may be irrational;
there is no caller-supplied partition, precision schedule, or derivative premise.
The quadrature is a certified construction, not a performance benchmark.

## Continue the route

The multiplication law, integer-power formula, addition, double-angle, and
product-to-sum identities above are checked. Further definite-integral
families for higher trigonometric powers are contribution targets.
Rational trigonometric expressions additionally
need the relevant whole-segment domain and substitution evidence. Consult
`skills/elementary-definite-integrals/SKILL.md`; a rational chart reduction is
not yet an angle-integral theorem.

## Reproduce the checked applications

From `subprojects/special-topics`:

```sh
lake build ComputableAnalysis.EulerTrigApplications ComputableAnalysis.EulerTrigIntegralApplications
lake build ComputableAnalysis.EulerDeMoivre ComputableAnalysis.EulerTrigProducts
lake env lean --run ../../scripts/check_euler_applications.lean
```

The audit checks standard logical axioms, the finite Cauchy-product and
geometric FTC dependencies, the actual Euler-formula dependency, and the
justified integral role. It also checks that the quadrature's executable
dependency graph does not call the closed form. The default runtime cases
exercise certified positive and negative integer powers, finite Euler
reflection, and the shared quadrature on a nonzero affine test.
Add `--trig-runtime` to the Lean command
for end-to-end geometric quadrature/formula cases. The canonical geometric
sampler makes that optional run expensive; the exact theorem audit covers
the full trigonometric family independently of execution time.

From the repository root, the elementary-integral checker also discovers the
companion package automatically:

```sh
python3 skills/elementary-definite-integrals/scripts/check.py \
  --module ComputableAnalysis.EulerTrigIntegralApplications \
  --root ComputableAnalysis.EulerTrigIntegralApplications.integrand_identity \
  --root ComputableAnalysis.EulerTrigIntegralApplications.hasIntegral \
  --root ComputableAnalysis.EulerTrigIntegralApplications.definite_integral \
  --root ComputableAnalysis.EulerTrigIntegralApplications.definite_integral_of_hasIntegral \
  --root ComputableAnalysis.EulerTrigIntegralApplications.representation_equiv
```

Source ownership remains separate even though both Lake packages share the
generated build directory: Lean resolves one directory for the preserved
`ComputableAnalysis` namespace. The foundation import audit still rejects a
foundation source importing any companion module.
