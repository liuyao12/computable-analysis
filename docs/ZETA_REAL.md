# Zeta on the represented-real half-line s > 1

`ComputableAnalysis.ZetaReal.zeta` accepts a `Real` and a finite strict-domain
certificate `AboveOne`: some input box has lower endpoint greater than 1.
It returns a valid `Real`. The construction uses rational arithmetic, finite
sums, terminating searches, and the existing interval-function application.
It introduces neither a completed-real type nor a new axiom.

## The construction

For rational s in a chart `[1+1/(q+1), m+2]`, q > 0, put

- c₀(s) = 1, cₖ₊₁(s) = cₖ(s)(k+2−s)/(k+1);
- zₙ = 1−1/(n+1);
- Dₖ(N) = Σ(n<N) (n+1)⁻² zₙᵏ;
- R(s,K,N) = Σ(k<K) cₖ(s) Dₖ(N).

These are literal finite rational computations. `rectangle_dirichlet` proves
that R is also the finite Dirichlet sum with each power evaluated by the
binomial polynomial `(n+1)⁻² Σ(k<K)cₖ(s)zₙᵏ`.
The coefficients satisfy `(1−z)f′=(2−s)f`, f(0)=1, and
`binomial_unique` proves uniqueness of this **formal coefficient** solution.
Thus the power construction has a checked recurrence and initial value;
this is not a theorem identifying it with the project's log–exp evaluator.

For J=m+1 and B=(m+3)^J, the checked finite estimates are

- |cₖ(s)| ≤ B;
- (k+1)Dₖ(N) ≤ 2;
- |R(s,K+L,N)−R(s,K,N)| ≤ 2(q+1)|c_K(s)| for K≥J;
- |R(s,K,N+L)−R(s,K,N)| ≤ KB/N for N>0.

The coefficient magnitudes decrease after J and contract on dyadic indices:
|c_(J·2^j)(s)| ≤ B ((2q+2)/(2q+3))^j. A sharper positive binomial
coefficient envelope is used in the actual outer-cutoff test; the geometric
estimate proves termination. Each approximation gives both cutoffs a
budget 1/(32(n+1)). Prefix intersection with radius four times that budget
produces nested valid boxes. Finite polynomial Lipschitz bounds supply a
concrete `IntervalRegularOn`, so arbitrary represented inputs use the
canonical adaptive input schedule, not synchronized input/output stages.

`dirichletRaw_valid` certifies finite Dirichlet sums at nonintegral rational
exponents. `inversePowerRaw_valid` and `inversePowerRaw_enclosure` certify the
individual terms against their explicit binomial polynomials.
`dirichlet_convergence` proves an effective enclosure form of convergence:
for every positive rational ε, sufficiently many terms and sufficiently fine
output stages put every point of the finite-sum and zeta boxes within ε.
The real-input function is the certified continuous extension of this
rational-input construction.

## Public compatibility

- `zeta_valid`: valid output for every represented s>1.
- `zeta_equiv`: equivalent input implementations give equivalent outputs,
  even when their domain searches select different charts.
- `raw_chart_equiv`: chart choice does not change the represented value.
- `zeta_integer_equiv`: for every p≥0, the new function at p+2 agrees with
  `DirichletSeries.zetaNatRaw (p+2)`.
- `zeta_three_equiv`: the Apéry target remains the existing ζ(3).

The nonintegral regression checks c₂(3/2)=3/8 and R(3/2,3,2)=171/128.
The latter is a finite approximation, not an asserted enclosure for ζ(3/2).

## Boundary

The reference evaluator has deliberately coarse bounds and is not optimized
for numerical speed, especially near s=1. A bridge from the binomial power
computation to `exp(-s log n)`, parameter derivatives, the Euler product,
analytic continuation, and the Apéry approximant-to-ζ(3) identification remain
open. No complex half-plane or continuation result is claimed here.

The axiom audit is `scripts/check_zeta_real.lean`. No new source uses
`sorry`, `admit`, `native_decide`, Mathlib, or a completed-real construction;
transitive foundational axioms are shown in the published audit.
