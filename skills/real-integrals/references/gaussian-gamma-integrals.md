# Gaussian and Gamma integrals

These are construction routes with unfinished analytic bridges. Read the
[Gaussian progress report](../../../docs/GAUSSIAN_CONVOLUTION.md) and
[Gamma and ball-volume report](../../../docs/N_BALL_GAMMA.md) before reporting
checked scope. Follow the
[shared formalization policy](../../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems).

## Gaussian: separate the finite interval from the tail

For \(g(x)=e^{-x^2}\), choose a rational radius \(R\ge1\). Compute the
finite integral on \([-R,R]\) using independently justified exponential
enclosures or a finite Taylor polynomial with a proved uniform remainder.
If the uniform approximation error is at most \(\delta\), the integral
error is at most \(2R\delta\), once the finite-integral comparison is proved.

The positive exponential series gives \(e^{x^2}\ge x^2\), hence
\(e^{-x^2}\le x^{-2}\) for \(x\ge1\). A justified comparison with the
[power integral](improper-power-integrals.md) yields a two-sided
omitted-tail allowance \(2/R\). Allocate the total budget explicitly:

\[
\text{finite evaluation error}+2R\delta+\frac2R\le\varepsilon.
\]

Prove the actual finite witnesses and the exhaustion-limit statement. Existing
valid Gaussian candidates and finite tail computations do not supply those
semantic bridges merely through their validity.

## Gaussian normalization is a further theorem

Keep the Gaussian computation independent of the circle constant. To prove
\(G^2\simeq\pi\), compare finite two-dimensional constructions and control
the omitted regions and diagonal. Justify any change of variables and the
product-integral comparison. Do not define \(G\) to be \(\sqrt\pi\) and
then call the normalization proved.

The existing square-to-triangle finite identities retain and bound the
diagonal. They are useful components, not yet a normalization theorem.

## Gamma: budget both endpoints

For a positive represented parameter \(s\), the intended construction is

\[
\Gamma(s)=\int_0^\infty t^{s-1}e^{-t}\,dt.
\]

Find rational bounds \(0<\sigma\le s\le M\) from the parameter's boxes.
On \((0,1]\), prove domination by \(t^{\sigma-1}\); the omitted interval
\((0,a)\) then contributes at most \(a^\sigma/\sigma\).
For an integer \(m\ge\max(M-1,0)\) and \(t\ge1\), prove

\[
t^{s-1}e^{-t}\le t^me^{-t}\le\frac{(m+2)!}{t^2}.
\]

This gives the explicit far-tail budget \((m+2)!/R\). It is a conservative
starting estimate; improve it when useful. Construct the power/exponential
product, its order comparisons, and its finite integrals independently before
using these budgets. Parameter-uniform estimates support irrational inputs.

## Recurrences and geometric comparisons

Prove integration by parts on finite truncations and show the boundary terms
vanish before asserting \(\Gamma(s+1)\simeq s\Gamma(s)\). Prove the
substitution identifying \(\Gamma(1/2)\) with the independently normalized
Gaussian. A finite coefficient recurrence is not this integral identity.

Likewise, the formula
\(\pi^{n/2}R^n/\Gamma(n/2+1)\) needs a separate comparison with a
construction of geometric ball volume. Distinguish the ball's ambient
dimension from its boundary sphere's dimension.

## Proof sources and checks

Inspect [NBallGaussian](../../../ComputableAnalysis/NBallGaussian.lean) for the
checked finite coefficient and diagonal lemmas, and the reports above for
their limitations. Check the actual source before reusing any older Gaussian
candidate. Do not treat a recurrence audit or numerical regression as a proof
of the Gaussian or Gamma integral.

For a newly completed bridge, run the focused Lean build and axiom audit from
the [formalization skill](../../computable-analysis-formalization/SKILL.md), then
update the reader's proof status to match exactly what was proved.
