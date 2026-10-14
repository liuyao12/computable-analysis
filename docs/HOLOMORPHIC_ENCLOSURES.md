# Holomorphicity from covered rational enclosures

The semantic interface is `DomainFunctions.IsEnclosureHolomorphic` in
`ComputableAnalysis/EnclosureHolomorphic.lean`. It asks for an open domain and
an enclosure derivative at every valid represented point. **Continuity of the
derivative is not a hypothesis.** The old `Holomorphic` records remain useful
stronger construction packages, with a checked adapter to the semantic core.

## Pointwise definition

For the actual function evaluation, base point \(a\), and proposed derivative
\(d\), put
\[
 R_{a,d}(z)=f(z)-f(a)-d(z-a).
\]
Choose nested positive rational radii \(r_n\le 2^{-n}\). At resolution
\(n\), the observations include both coordinates of **every** normalized error
\[
 \frac{R_{a,d}(z)}{H},\qquad
 0<H\le r_n,\qquad \|z-a\|_\infty\le H,
\]
for every valid represented \(z\) in the domain. Division here is just scaling
by the exact positive rational \(H\). The coordinate norm is shorthand for
four exact `RealRaw.Le` inequalities (`FunctionTheory.Small`); no completed
norm or complex field supplies the construction.

For each coordinate, `RawLimit.HasEnclosureValue` requires a two-index rational
interval family and cofinal maps \(n(k),m(k)\), whose selected intervals are a
valid represented zero and cover all observations at the selected neighborhood
resolution. Both indices eventually exceed every fixed bound. All nearby
complex directions are covered. A favorable path or subsequence is insufficient.
The coordinates can use different schedules because both cover their entire
neighborhoods and both represent zero.

This tests an **anchored** first-order error. Requiring all two-point complex
secants to collapse would impose a stronger pointwise condition; it is not
silently substituted here. Zero displacement causes no division problem.

## Checked equivalence and laws

`enclosureDerivative_iff` proves equivalence with existence of the actual
quantitative first-order certificate:
\[
 \forall\varepsilon>0\;\exists\delta>0\;\forall H,z,\qquad
 0<H\le\delta,\quad \|z-a\|_\infty\le H
 \quad\Longrightarrow\quad
 \|R_{a,d}(z)\|_\infty\le\varepsilon H.
\]
Both error and radius bounds are rational. The forward construction uses padded
zero intervals and finite radius minima. The reverse proof uses coverage,
cofinality, validity, and exact rational scaling to recover a radius. It does
not assume the estimate as a field. `rawDerivative_iff` gives the same
comparison for the existing raw-map interface.

The semantic derivative is unique on an open domain and invariant under
equivalent input and derivative names. Its optional canonical selection uses
logical choice; this is not an executable derivative algorithm. The concrete
function certificates retain their supplied algorithms and moduli.

The checked laws include value continuity, sum and product rules, the chain
rule (including openness of the composition domain), and exact agreement of
the selected derivative with the rule's proposed value. In
`EnclosureHolomorphicConstancy.lean`, represented rational bisection proves
\[
 \|f(q)-f(p)\|_\infty\le 2BW
\]
when the entire represented segment stays in the domain, its derivative is
bounded by \(B\), and its displacement is bounded by positive rational
\(W\). The factor \(2\) accounts for complex multiplication in the coordinate
maximum norm. Local radii may vary along the segment; no uniform modulus is
supplied by the caller. Consequently:

- zero derivative throughout the segment gives exact endpoint equality;
- two holomorphic functions with equal derivatives throughout a common
  segment and one equal endpoint value agree at the other endpoint.

These theorems depend on the enclosure core, not on a derivative-continuity
field. Their proof-dependency audit checks that distinction.

## Actual function portfolio

`EnclosureHolomorphicExamples.lean` checks the following existing computations.

| Function | Proven domain and evidence |
| --- | --- |
| Polynomials | Entire, with arbitrary valid represented complex coefficients |
| Rational functions and reciprocal | Every represented point where the actual denominator is nonzero; pole neighborhoods are constructed |
| Exponential | The established derived entire evaluator, with enclosure derivative equal to its value |
| Sine and cosine | Entire for arbitrary represented complex frequency \(a\), with derivatives \(a\cos(az)\) and \(-a\sin(az)\) |
| Logarithm | Actual normalized logarithm germs on their constructed branch domains, with derivative \(1/z\) |
| Lambert series | Every nonnegative degree on the full open Euclidean unit disk |
| Eisenstein functions | \(E_2,E_4,E_6\) on the full unit disk, with primary rational-input agreement |

The elementary sine extension has checked agreement and convergence from
primary rational complex power-series inputs and normalized rational angles.
The normalized frequency is the computed geometric \(\pi\), rather than a
rational substitute. Existing exponential comparisons identify the primary
rational sampler and the represented evaluator. Lambert and Eisenstein
extensions have quantitative sample-convergence constructions and exact
rational-input agreement; restricting a pre-existing represented map is not
treated as that bridge.

The negative test `conjugation_not_differentiable` excludes \(z\mapsto\bar z\)
at zero for **every** valid represented derivative candidate. Two exact rational
axis displacements force incompatible bounds in a sufficiently narrow
candidate box. Its executable continuity modulus is separately checked, so
continuity alone cannot accidentally satisfy the definition.

This portfolio and the comparison laws test the formalization; they are not a
claim that every special function or every classical complex-analysis theorem
has now been formalized. Cauchy and Taylor results already proved for stronger
`Holomorphic` packages keep their stated hypotheses. Deriving those results,
and derivative continuity, from the bare core is a further theorem task.

## Verification

```bash
lake build ComputableAnalysis
lake env lean scripts/check_enclosure_holomorphic.lean
lake env lean scripts/check_parametrized_foundation.lean
lake env lean scripts/check_holomorphic.lean
lake env .lake/packages/checkdecls/.lake/build/bin/checkdecls blueprint/lean_decls
```

The new audit checks standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), rejects transitive Mathlib imports, and checks the absence of the
stronger derivative-continuity field in the semantic calculus and segment
proofs. The downloadable source snapshot includes all imported project modules
and the audit scripts; its independent build receipt is published with it.
