# Series computation strategies

Consult this reference when constructing or comparing a particular infinite
series. It guides the choice of finite computation and proof; it does not
prescribe a universal infinite-sum operator or a required certificate record.
Use `Series`, `PowerSeries`, and `AlternatingRemainder` as sources of checked
finite lemmas where their actual hypotheses fit the example.

## Choose a route from the terms

| Available information | Finite computation and proof route |
| --- | --- |
| Alternating signs and nonincreasing nonnegative magnitudes | Bracket by consecutive partial sums; prove the first omitted magnitude tends to zero with an explicit schedule. |
| A geometric bound after a known index | Prove a finite geometric-tail estimate with a rational ratio strictly below one; handle the initial prefix separately. |
| Factorial denominators | Bound the ratios beyond a computed cutoff, then use a geometric tail. |
| A telescoping identity | Prove the finite cancellation and bound the remaining endpoint terms. |
| Nonnegative terms bounded by another computation | Prove a finite tail comparison and a quantitative tail schedule; bounded increasing partial sums alone do not provide an executable convergence rate. |
| A power series on a specified input domain | Prove a uniform tail majorant on a smaller certified domain; handle boundary points separately. |
| A faster transformed series or recurrence | Prove a finite identity and bound the omitted correction; compare with the original ordered partial sums. |

These routes are examples, not an exhaustive list. Prove the estimates for
the actual terms and inputs. A recurrence for coefficients or a formal
power-series identity does not establish convergence of a value computation.

## Construct boxes without assuming the infinite sum

For exact rational terms, define the literal finite prefix
\[
S_N=\sum_{k=0}^{N-1}a_k.
\]
One useful route is to find nonnegative rational bounds satisfying
\[
\lvert S_M-S_N\rvert\le E_N\qquad(M\ge N),
\]
and give an explicit index selection making \(E_N\) arbitrarily small.
This estimates finite future prefixes; it does not assume that an infinite
sum already exists. The intervals
\[
[S_N-E_N,S_N+E_N]
\]
need not be nested. Prove nesting for the chosen construction, or justify
finite intersections or a checked stabilization method. Prove nonemptiness
and the width schedule as well; a small width alone cannot identify a sum.

For represented terms or inputs, compute a finite interval enclosure of the
prefix and add the tail allowance. Budget both accumulated term-evaluation
error and truncation error. Prove that the selected evaluation precisions
achieve that budget. For complex terms use rational rectangles and certified
coordinate bounds; do not introduce a completed complex field.

For an alternating series, use the sharper consecutive-prefix bracket when
its order and shrinking width are proved. An absolute-tail argument is not
required for a conditionally convergent ordered series.

## Finish the mathematical statement

Prove `RealRaw.Valid` or the corresponding complex validity for the actual
evaluator. State its finite-stage and convergence guarantees. When identifying
two computations, prove `RealRaw.Equiv` or `ComplexRaw.Equiv`; when inputs are
represented values, prove independence of equivalent input representations.
Hide incidental cutoffs and precision choices beneath the public theorem.

A proposed closed form still needs a comparison proof. Acceleration,
regrouping, reindexing, multiplication, termwise integration, and termwise
differentiation each need the relevant finite identity and error bounds.
Do not infer these from the existence of an evaluator or a coefficient identity.
In particular, conditional convergence does not justify arbitrary permutations.

For a divergence request, produce an obstruction for the actual partial sums,
such as a quantitative failure of the terms to tend to zero or a persistent
gap between arbitrarily late prefixes. Failure of one tail estimate proves
only failure of that method, not divergence.

As a routing example, the arctangent series can use a geometric bound strictly
inside \(\lvert x\rvert<1\), an alternating bracket at \(x=1\), and a
term-size obstruction for \(\lvert x\rvert>1\). These are different proofs
about a specified computation, not different universal definitions of a sum.
