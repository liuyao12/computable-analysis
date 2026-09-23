# Apéry's zeta(3): differential equation and arithmetic approximants

Import `ComputableAnalysis.Apery`. This milestone derives the differential
equation from an independent finite integer construction, then gives the
series actual computable-analysis semantics. It does **not yet prove the
irrationality of zeta(3)**.

## Integer sums force a differential equation

Define

\[
 A_n=\sum_{k=0}^n\binom nk^2\binom{n+k}k^2,\qquad
 P(n)=34n^3+51n^2+27n+5.
\]

`number_integral` identifies the rational computation with an explicit natural
number. Pascal's identity proves the row and column shifts of its summand
`F(n,k)`. The Cohen–Zagier certificate

\[
 C(n,k)=4(2n+1)\bigl(k(2k+1)-(2n+1)^2\bigr)
\]

makes `(n+1)^3 F(n+1,k)-P(n)F(n,k)+n^3 F(n-1,k)` telescope.
The proof checks both finite-support endpoints; it does not divide by a
quantity that vanishes at the top endpoint. Summing yields

\[
 (n+1)^3A_{n+1}-P(n)A_n+n^3A_{n-1}=0\quad(n\ge1),
 \qquad A_0=1,\quad A_1=5.
\]

The Euler operator is independently defined by multiplication by the formal
variable after coefficient differentiation. With `theta=t d/dt`,

\[
 L=\theta^3-t(34\theta^3+51\theta^2+27\theta+5)+t^2(\theta+1)^3.
\]

`number_equation` proves `L A=0`. `operator_ordinary` proves the translation
to the usual third-order derivative expression. Defining `A` by its
binomial sums is essential: the recurrence and the equation are conclusions,
while integrality has a separate finite arithmetic proof.

## Actual computations and derivatives

The checked bound `0<=A_n<=64^n` gives a conservative rational chart
`U(x)=A(x/4096)`, `|x|<=1`. Its coefficients satisfy `|a_n|<=64^-n`.
The first three derivative streams all satisfy `|a_n^(j)|<=8^-n`.
Each evaluator returns a finite prefix plus/minus `2/2^N`; its width is
`4/2^N`. `value_valid` proves validity, and `value_derivative` proves actual
finite-difference semantics for the three successive derivatives, with an
explicit step radius and step-dependent output precision.

For arbitrary samples `u,d1,d2,d3` from the four stage-`N` boxes,
`equation_error` proves that the absolute value of

\[
 x^3(1-34x/4096+x^2/4096^2)d_3
 +x^2(3-153x/4096+6x^2/4096^2)d_2
 +x(1-112x/4096+7x^2/4096^2)d_1
 +(-5x/4096+x^2/4096^2)u
\]

is at most `24/2^N`. `equation` computes a sufficient stage for every
positive rational error request. This uses finite-prefix identities and
valid rational boxes. No completed real or complex number type, Mathlib,
analytic continuation, or geometric period theorem is needed.

## The companion and the number-theoretic target

The rational sequence `B` is computed by the same recurrence with
`B_0=0,B_1=6`. Its generating series satisfies the **inhomogeneous** equation
`L B=6t`; it is not a second homogeneous solution with those initial terms.
The checked discrete Wronskian and positivity of `A_n` imply

\[
 (n+1)^3(A_nB_{n+1}-A_{n+1}B_n)=6,
 \qquad
 \frac{B_{n+1}}{A_{n+1}}-\frac{B_n}{A_n}
 =\frac6{(n+1)^3A_nA_{n+1}}>0.
\]

Thus consecutive approximants are strictly separated. This is not itself
an irrationality proof: increasing rational sequences can converge to
rational numbers.

The remaining arithmetic proof must identify the limit with the independent
`DirichletSeries.zetaNatRaw 3` computation, establish the necessary denominator
control for `B_n`, and prove sufficiently small nonzero integer linear forms.
None of these facts is assumed in the current theorems. The sharper growth
estimates needed for irrationality are also separate from the deliberately
coarse local convergence bound above.

Classically, Apéry's generating function has a K3-period interpretation,
explained by Beukers and Peters after Apéry's proof. This is the geometric
context for the Picard–Fuchs operator; our development has not yet formalized
the K3 family, period integral, or that identification. No claim that this
series is an algebraic function is made.

## Checked declarations and validation

| Result | Declaration in `ComputableAnalysis.Apery` |
|---|---|
| Integer binomial definition | `number_integral` |
| Explicit finite telescoping | `term_telescopes`, `number_recurrence` |
| Conservative coefficient bound | `number_growth` |
| Generating-series equation | `number_equation`, `coefficients_equation` |
| Euler/ordinary derivative translation | `operator_ordinary` |
| Actual valid derivative computations | `value_valid`, `value_derivative` |
| Quantitative differential equation | `equation_error`, `equation` |
| Companion recurrence and forcing | `companion_recurrence`, `companion_equation` |
| Nonzero discrete Wronskian | `casoratian` |
| Positive integer denominators | `number_ge_one` |
| Exact strictly positive increments | `approximant_difference`, `approximant_increasing` |

`Apery.Tests` checks the classical initial values, the fractional companion,
both ends of the rational chart, a non-singleton box width, and an ordinary
third-order test coefficient. The publication audit prints dependencies of
all the declarations listed above. There are no new custom axioms, proof
placeholders, or native-decision proofs; analytic certificates inherit the
foundation's existing native-decision dependencies, disclosed in the audit.

Sources: [Zagier, *The arithmetic and topology of differential equations*](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.4171/176-1/33/HirzebruchLectureECM2016.pdf)
for Apéry's recurrence, arithmetic proof and geometric context;
[Zeilberger, *Sister Celine's technique and its generalizations*, §1.3](https://sites.math.rutgers.edu/~zeilberg/mamarimY/celine1982.pdf)
for the finite telescoping certificate.
