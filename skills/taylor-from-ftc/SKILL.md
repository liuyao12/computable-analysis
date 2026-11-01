---
name: taylor-from-ftc
description: Derive a constructed function's Taylor expansion and exact convergence by repeated definite-integral FTC, with explicit remainder bounds and represented-real input bridges. Use for Taylor developments of geometric sine/cosine or another supplied derivative family; convergence of an independently proposed series alone is a different task.
---

# Taylor convergence from repeated FTC

Start with the actual function and its constructed derivatives. Successive
applications of FTC generate the finite polynomial and its remainder; the
infinite series is the consequence of proving that remainder vanishes.
Record the motivating questions and intermediate discoveries. A derivation
may explore useful constructions before a series formula becomes the goal.

## Establish the function and its derivative chain

Fix the center, the full segment to the input, and the function's normalization.
Supply justified derivative and definite-integral evidence along that segment,
including joins of local pieces. Piecewise convexity or concavity can help
construct derivatives; it does not itself prove differentiability at a corner.
Do not cross poles or silently discard negative inputs.

For a proposed expansion about $a$, pull the segment back to $[0,1]$ by
$G(t)=F(a+(x-a)t)$. Include every chain factor $(x-a)^k$ in $G^{(k)}$.
This also handles $x<a$. In this repository rational-input computations come
first; the bridge to arbitrary valid represented inputs is a later proof.

Construct the finite FTC evidence for the actual derivative family. A record
asserting the desired integral identity or series agreement would assume the
result. `FTCRealCalculus.Step` instead carries quantitative derivative and
variation evidence from which `Step.hasIntegral` proves an integral law.
Use justified integration evidence appropriate to the particular function;
the current rectangle-bound implementation is one sufficient route.

## Generate the finite development by integration

Write $G_k=G^{(k)}$. Integrate initial derivative values and monomials to obtain

$$
P_{N,k}(t)=\sum_{j=0}^{N-1}\frac{G_{k+j}(0)t^j}{j!},
\qquad R_{N,k}(t)=G_k(t)-P_{N,k}(t).
$$

The empty polynomial is zero. Prove, using finite polynomial arithmetic and
FTC for the supplied derivatives, that

$$
R_{0,k}=G_k,\qquad R_{N+1,k}(0)\simeq0,\qquad
R_{N+1,k}(t)\simeq\int_0^t R_{N,k+1}(u)\,du.
$$

This last identity must concern a genuine definite integral. Numerical
candidate validity or an endpoint-agreement field alone does not establish it.
In Lean, retain the integral evidence as well as the resulting equality.

## Bound the actual remainder and make it vanish

Integrate upper and lower majorants for these actual remainders. For example,
if $|G_k(t)|\le B^k$ on $[0,1]$, repeated integration gives

$$
|R_{N,k}(t)|\le\frac{B^{k+N}t^N}{N!}.
$$

More generally, a supplied bound $M_N$ for $|F^{(N)}|$ on the entire segment
gives the finite estimate

$$
\left|F(x)-\sum_{j=0}^{N-1}\frac{F^{(j)}(a)(x-a)^j}{j!}\right|
\le\frac{M_N|x-a|^N}{N!}.
$$

Prove a quantitative schedule making this right side arbitrarily small.
For fixed $C$, $C^N/N!$ tends to zero; arbitrary derivative bounds $M_N$
need not give this conclusion. Smoothness alone is insufficient. If the
remainder has not been proved to vanish, report the finite expansion and its
bound without claiming equality with an infinite Taylor series.

## Extend the estimates and construct the represented sum

For a valid interval name of the input, enclose the finite polynomial on the
whole input bracket and bound the remainder uniformly there. Endpoint values
alone do not enclose a polynomial that turns inside the bracket. Account for
coefficient, input, and truncation errors, and prove the chosen cofinal
precision schedule shrinks them together. Keep these choices internal.

Construct sum intervals from finite-polynomial enclosures enlarged by the
proved remainder. Repair nesting with finite prefix intersections when
needed. Prove containment, validity, and exact agreement with the original
function using `RealRaw.Equiv` on every valid represented input in the domain.
State convergence of the actual term stream separately from validity of one
sum algorithm. Prove representation invariance and any regrouping used to
select nonzero terms. Reuse agreement theorems when optimizing evaluation.

## Checked reference: geometric sine and cosine

Here $\sin(x)$ and $\cos(x)$ denote the geometric functions in the normalized
coordinate, with period $2$. Their already constructed global derivatives are
$D\sin=\pi\cos$ and $D\cos=-\pi\sin$. Apply the preceding steps to those
functions, using their geometric initial values. The generated nonzero terms
are respectively

$$
\frac{(-1)^k(\pi x)^{2k+1}}{(2k+1)!},\qquad
\frac{(-1)^k(\pi x)^{2k}}{(2k)!}.
$$

Their finite FTC errors are bounded first by $(8|q|)^N/N!$ at rational inputs
$q$, then by $C^N/N!$ on a represented-input bracket. Only after this bound
vanishes do we obtain the infinite expansions. Do not replace this derivation
with an independently defined trigonometric series, ODE uniqueness, or Euler's
identity. Complex numbers are unnecessary here.

Repository entry points, resolved from the project root:

- `ComputableAnalysis/GeometricFTCData.lean`: actual geometric derivative family.
- `ComputableAnalysis/FTCMonomials.lean`: justified monomial integration.
- `ComputableAnalysis/RepeatedFTC.lean`: `remainder_hasIntegral` and `remainder_bound`.
- `ComputableAnalysis/GeometricTaylorFTC.lean`: finite geometric development and initial coefficients.
- `ComputableAnalysis/GeometricTaylorReal.lean`: whole-bracket bridge to valid real inputs.
- `ComputableAnalysis/RepresentedSeries.lean`: `HasSum`, uniqueness, and certified sum construction.
- `ComputableAnalysis/GeometricTaylorSeries.lean`: `sin_taylor_converges`, `cos_taylor_converges`, exact evaluator agreement, and input invariance.

The checked generic `RepeatedFTC` route assumes a bound $B^k$ for its supplied
family. The checked geometric expansions are centered at zero. Other centers
or more general derivative growth require their own connecting proofs; the
general finite estimate above does not claim those interfaces already exist.

After changes to these proofs, run:

```sh
lake build ComputableAnalysis.GeometricTaylorSeries
lake env lean scripts/check_geometric_taylor.lean
```

The audit checks the actual geometric and repeated-FTC dependencies. For
another function, add a corresponding audit of its supplied derivative family
and remainder proof; do not merely rename the geometric result.


## Elementary reference cases

For the Euler exponential, consult `EulerTaylorFTC` and `EulerTaylorSeries`.
Normalize the actual derivative family by a certified value budget before
applying `RepeatedFTC`; restore that budget afterward. The pullback proof
handles either sign of the displacement. Keep the successive integral roles,
factorial finite error, represented-input transport, and exact sum theorem.
The earlier binomial comparison is a separate valid proof.

When the actual derivative has a finite geometric-division identity, a useful
specialized route is to integrate that identity and its monomial majorants.
`LogTaylorFTC` and `ArctanTaylorFTC` use this route with genuine integral
witnesses for the already constructed functions. This avoids forcing their
factorially growing derivative families into a geometric derivative bound.
Use `TaylorIntegralPolynomial` for the checked monomial FTC comparisons and
`TaylorPolynomialSeries` for whole-input-box transport.

The exact reference domains are $-1<x\le1$ for $\log(1+x)$ and
$-1\le x\le1$ for geometric $\arctan(x)$. The denominator budget must hold
on the complete logarithm segment. Prove endpoint convergence from the
integrated error; a geometric tail estimate requiring $|x|<1$ alone does not
cover the convergent endpoints. `LogTaylorSeries` and `ArctanTaylorSeries`
include the signed rational arguments, actual endpoint extensions, validity,
convergence, exact identification, and representation invariance.

Run `lake env lean --run scripts/check_elementary_taylor.lean` to audit these
routes and exercise ordinary executable downstream definitions.
