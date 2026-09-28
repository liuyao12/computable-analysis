# Gaussian integrals and a convolution route to the central limit theorem

The useful program is to construct the Gaussian integral, prove its exact
identities, and use convolution on functions to express the central limit
theorem. None of these steps needs Mathlib real numbers, a probability space,
or a completed space of measures. They do need mathematical proofs connecting
finite computations to their asserted integral and limit values.

## Existing Gaussian route and the new checked scope

`FiniteGaussianIntegral` constructs valid bounded-radius integrated Taylor
series. `FiniteGaussianTail` proves reciprocal-square domination and a
two-sided omitted-tail budget \(2/R\). `FiniteGaussianRadiusQuadrature`
compares bounded quadrature with those series and constructs the valid raw
`gaussianGrowingRadiusQuadratureFullLineRaw`, with width at stage \(n\) at
most \(16/(n+1)\). A positive rational lower bound supplies its reciprocal.
These finite comparisons and valid computations are useful existing work.
They do **not** yet prove the geometric normalization
\[
  \left(\int_{-\infty}^{\infty}e^{-x^2}\,dx\right)^2\simeq\pi.
\]
The module also does not yet expose this candidate as a witness of
`Integral.HasIntegralLimit`. Its compact semantic witnesses and exhaustion
comparison must be checked separately; raw validity alone is insufficient.
Those Gaussian modules are pre-existing working-tree work, outside this
publication's source closure. The new audit certifies the finite convolution
module and its dependencies, not a fresh build of that Gaussian development.

The new `FiniteConvolution` module proves actual finite laws over the existing
`FiniteProbabilityKernel`. Its only direct import is
`FiniteApproximateIdentity`, which imports `Basic`; the external foundation
is Lean's rational arithmetic. All computations are finite rational sums.

For samples \((x_i,p_i)\) and \((y_j,q_j)\), convolution constructs
\((x_i+y_j,p_iq_j)\), preserving multiplicities. Writing
\(A_K(h)=\sum_i p_i h(x_i)\), the checked laws include
\[
 A_{K*L}(h)=\sum_i p_i\sum_j q_jh(x_i+y_j),\qquad
 A_{K*L}(h)=A_{L*K}(h),\qquad
 A_{(K*L)*M}(h)=A_{K*(L*M)}(h).
\]
Equality is of actions, since list order is an implementation choice.
Total mass remains one, and
\[
 \mu_{K*L}=\mu_K+\mu_L,\qquad
 v_{K*L}=v_K+v_L,\qquad
 \mu_{K^{*n}}=n\mu_K,\qquad v_{K^{*n}}=nv_K.
\]
The convolution action on functions,
\[
 (T_Kh)(x)=\sum_i p_i h(x-x_i),
\]
satisfies \(T_{K*L}h=T_K(T_Lh)\).

## Checked quantitative replacement theorem

Suppose finite kernels \(K,L\) have equal means and second moments. For any
quadratic polynomial \(P\), the module proves \(A_K(P)=A_L(P)\). If a
function \(h\) satisfies the supplied pointwise bound
\[
 |h(x)-P(x)|\le C|x|^3
\]
on both finite supports, then
\[
 |A_K(h)-A_L(h)|\le C\bigl(\rho_3(K)+\rho_3(L)\bigr),
 \qquad \rho_3(K)=\sum_i p_i|x_i|^3.
\]
This is `cubic_replacement_bound`. Its hypotheses are remainder bounds, not
the desired conclusion. No derivative or Taylor theorem is silently assumed.

`convolutionPower_replacement_bound` proves that a translated one-step error
at most \(\varepsilon\), uniformly in the translation, accumulates to at
most \(n\varepsilon\). The combined theorem
`scaled_convolutionPower_cubic_bound` takes rational \(r\) and quadratics
\(P_z(x)=c(z)+\ell(z)x+q(z)x^2\) satisfying
\[
 |h(z+rx)-P_z(x)|\le C|r|^3|x|^3
\]
for all rational translations \(z\) and both finite supports. It concludes
\[
 \left|A_{K^{*n}}\bigl(h(r\,\cdot)\bigr)
       -A_{L^{*n}}\bigl(h(r\,\cdot)\bigr)\right|
 \le nC|r|^3\bigl(\rho_3(K)+\rho_3(L)\bigr).
\]
In particular, choosing \(n=m^2\) and \(r=1/m\), for positive natural
\(m\), makes the coefficient \(C/m\) using rational arithmetic alone.
The theorem does not supply an irrational scale for arbitrary \(n\).
Extending that input to valid represented reals requires a separate
representation-invariant evaluation and error transport proof.

The regression examples have equal first two moments but different fourth
moments, so equality of moments is not confused with equality of laws.
The two kernels are
\[
 K=\tfrac12\delta_{-1}+\tfrac12\delta_1,\qquad
 L=\tfrac18\delta_{-2}+\tfrac34\delta_0+\tfrac18\delta_2.
\]
Their absolute third moments are \(1\) and \(2\), and their fourth moments
are \(1\) and \(4\). Four convolutions of \(K\) have variance \(4\)
and fourth moment \(40\), checked by the literal evaluator.

## Exact Gaussian targets

The following are targets, **not newly checked identities**. Parameters must
range over arbitrary valid represented reals, with genuine positivity and
domain evidence. Equality in the public results will be `RealRaw.Equiv`
(or the complex counterpart), independent of internal schedules.

1. Establish compact Gaussian integral witnesses and the supplied full-line
   exhaustion, then compare the square of its value with geometric \(\pi\).
   A finite double-sum product followed by a certified radial change of
   variables is one route. The origin and the square-versus-disk boundary
   both need explicit error bounds; writing a polar-coordinate identity is
   not that proof.
2. Prove affine substitution on those justified integrals. Completing the
   square should then give, for \(a>0\),
   \[
     \int_{-\infty}^{\infty}e^{-ax^2+bx+c}\,dx
       \simeq \sqrt{\frac\pi a}\,
               e^{c+b^2/(4a)}.
   \]
   This includes translated and rescaled normal kernels.
3. Prove symmetry and integration by parts with polynomial-weighted tail
   control. The moment targets are
   \[
     \int_{-\infty}^{\infty}x^{2k}e^{-ax^2}\,dx
       \simeq\frac{(2k)!}{4^k k!}\frac{\sqrt\pi}{a^{k+1/2}},
     \qquad
     \int_{-\infty}^{\infty}x^{2k+1}e^{-ax^2}\,dx\simeq0.
   \]
   The unweighted reciprocal-square tail bound alone does not control all
   these weighted tails.
4. Construct the relevant convolution integrals and prove Gaussian stability:
   \[
     G_t(x)=\frac{e^{-x^2/(4t)}}{\sqrt{4\pi t}},\qquad
     G_s*G_t\simeq G_{s+t}\quad(s,t>0).
   \]
   This is also the heat semigroup law. The Fourier target, with phase
   \(e^{-i\xi x}\), is \(\widehat G_t(\xi)\simeq e^{-t\xi^2}\).
   The real shifted Gaussian formula does not by itself justify a complex
   contour shift or the Fourier identity.

Gaussian normalization need not block every subsequent calculation: one can
first use the reciprocal of the independently computed positive mass. Any
claim of mass one or Gaussian convolution stability still needs its integral
comparison proof. Renaming a raw value does not establish either law.

## The central limit theorem as a statement about functions

For a nonnegative density \(f\) with supplied justified integrals
\[
 \int f=1,\qquad \int xf(x)\,dx=0,\qquad \int x^2f(x)\,dx=1,
\]
the intended normalized convolution density is
\[
 f_n(x)=\sqrt n\,f^{*n}(\sqrt n\,x).
\]
The first target is convergence of its action on smooth bounded test
functions:
\[
 \int h(x)f_n(x)\,dx\longrightarrow
 \int h(x)\varphi(x)\,dx,
 \qquad \varphi(x)=\frac{e^{-x^2/2}}{\sqrt{2\pi}}.
\]
This is not a claim of pointwise convergence of densities. A local limit
theorem requires additional hypotheses and a separate proof. The iterated
test action can also be constructed directly by finite multiple sums;
universal pointwise existence of convolution for every integrable function
is not a prerequisite.

For a supplied third absolute moment \(\rho_3\), the quantitative target is
\[
 \left|\int h f_n-\int h\varphi\right|
 \le\frac{M}{6\sqrt n}
       \left(\rho_3+2\sqrt{\frac2\pi}\right),
 \qquad |h'''|\le M.
\]
The finite cancellation and telescoping underlying this estimate are now
checked. Remaining proofs must turn the derivative evidence into a cubic
remainder, transport the finite sums to represented integral actions, prove
the Gaussian moments and stability, and handle represented normalization.
Quadrature errors must be scheduled for the whole replacement sum: an error
per factor cannot be silently treated as a total error.

For finite variance without a third moment, use truncation with a supplied
effective second-moment tail bound
\[
 \int_{|x|>R}x^2f(x)\,dx\le\eta(R),\qquad \eta(R)\longrightarrow0.
\]
This exposes the data needed for a computable convergence schedule. Merely
asserting that the variance is finite does not provide such an algorithm.
Passing from smooth tests to distribution functions needs a further smoothing
estimate; it is not part of the new finite theorem.

The analytic strategy is the classical Lindeberg replacement argument; see
[Amir Dembo's probability notes, Section 3.1](https://web.stanford.edu/class/stats310c/NOTES/lnotes.pdf)
and [Chatterjee's generalization of the Lindeberg principle](https://arxiv.org/abs/math/0508519).
These are mathematical references, not imported foundations or proofs of the
Lean targets.

## Verification

```bash
lake build ComputableAnalysis.FiniteConvolution
lake env lean scripts/check_finite_convolution.lean
```

The check file exercises exact distributions, function-action commutativity
and associativity, moment cancellation, and the cubic replacement interface.
It prints the axioms of the general theorems. Concrete runtime regressions
use `native_decide`; the general convolution and replacement proofs do not.
