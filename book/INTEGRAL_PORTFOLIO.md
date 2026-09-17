# Paired Wallis and integer-beta integral families

The native `ComputableAnalysis.IntegralApplications` entry point and optional
`MathlibComparison.IntegralApplications` give two independently checked routes
to the same computational propositions. Parameters range over all naturals.
This is two new theorem families with four principal applications, not sixteen
unrelated results: the audit additionally pairs their recurrence and evaluation
interfaces, for sixteen closed proof terms in eight matched obligations.

## Fixed computations before their evaluations

Write c(t)=C(t/2), lambda=pi/2 using the existing geometric pi=4*A(1).
`Wallis.integral n` is an independently specified dyadic computation of
W_n=integral_0^1 c(t)^n dt. It uses subdivision depth k and cosine evaluation
stage k, justified by a proved uniform sample-error bound. The chosen output
has width at most 2*(1+112*n)*2^(-k). Compatibility, validity and this bound do
not borrow the value theorem or recurrence.

`BetaIntegral.integral m n` computes integral_0^1 x^m*(1-x)^n dx. Its samples
are exact rationals. The function need not be monotone: a supplied Lipschitz
constant m+n bounds every cell, including its turn. A fixed dyadic schedule
and prefix stabilization give width at most 2*(m+n)*2^(-k). This is an explicit
construction and certificate; no native integrability predicate is added.

Both constructions have conservative bounds, not optimized numerical precision.
`book/checks/RunIntegralExamples.lean` executes representative native programs.
The reader's rational Wallis-product bounds come from these compiled evaluations,
not from Python trigonometry or a value substituted for the proposed integral.

## The paired calculus middle

The native Wallis proof differentiates s*c^(n+1), applies the reusable quantitative
FTC, and proves (n+2)W_(n+2)=(n+1)W_n, with W_0=1 and lambda*W_1=1.
The Mathlib route independently identifies the actual quadrature with its interval
integral, then invokes the library's cosine-power reduction theorem. That theorem
uses integration by parts. Neither recurrence is a validity hypothesis.

The beta primitive x^(m+1)*(1-x)^(n+1) has zero endpoint difference. Polynomial
product differentiation and the FTC give
(m+n+2)B_(m,n+1)=(n+1)B_(m,n), with (m+1)B_(m,0)=1.
The Mathlib route uses its polynomial derivative and interval FTC, together with
an independent finite-cell quadrature bridge. The bridge uses integral order and
finite additivity, not the beta value. It deliberately does not import a larger
gamma-function theory merely to evaluate integer-exponent polynomials.

The common native recurrence proposition is inhabited by each route. Pure
rational recurrence arithmetic is shared, not independently rewritten in Mathlib.
The exports also check identical complete types for the final evaluations:

    4^n*(n!)^2*W_(2n) = (2n)!
    (2n+1)!*lambda*W_(2n+1) = 4^n*(n!)^2
    (m+n+1)!*B_(m,n) = m!*n!

Equalities here mean the checked `RealRaw.Equiv` of the specified programs.

## Arithmetic applications

The rational Wallis product R_n is computed by finite recurrence, independently
of pi or the integral. Comparing consecutive cosine powers yields

    2*R_n <= geometric_pi <= 2*R_n*(2n+2)/(2n+1).

The endpoint inequalities are native `RealRaw.Le` and are proved for every n.
For beta, the rational normalizer is computed from the coefficient recurrence;
pure arithmetic identifies it with (m+n+1)!/(m!*n!). Scaling the integral gives
a computation equivalent to one. The normalizer is not 1/(computed integral).

## Maps and accounting

`integral-families.html` contains four theorem-margin maps, with separate
native/Mathlib route selectors. Definition inputs have black arrows. Proof
arrows enter a stored proof body; every abbreviated path has a reference witness.
Nodes are mathematical bundles with the exact checked declarations available.
The beta maps do not display trigonometry. Mathlib's real type, interval integral
and FTC are explicit; the Wallis branch also displays exponential/trigonometry.

The comparison panel uses actual stored type/body closures, not imports.
Full, statement-prerequisite-free, shared-prerequisite-free, and post-Cartwright
costs are available. The latter uses a matching route-specific prior baseline,
not an identical library for both routes. A portfolio union charges reused
mathematics once. LOC unions available compiler source ranges after excluding
comments and blank lines. Mapped/unmapped declaration coverage is explicit;
unavailable core source files are not described as zero-cost proofs.

No claim is made that either selected proof is the shortest possible Mathlib
or native proof, or that the measured families establish a generally minimal
calculus foundation. The source ranges, proof expressions, inherited axioms,
numerical runtime, and mathematical scope are different comparisons.

## Reproduce

From the repository root, with the pinned Lean toolchain:

```sh
lake build ComputableAnalysis.Cartwright ComputableAnalysis.IntegralApplications
(cd comparison && lake build MathlibComparison.Cartwright MathlibComparison.IntegralApplications)
(cd comparison && lake env lean checks/ExportCartwright.lean)
(cd comparison && lake env lean checks/ExportIntegralPortfolio.lean)
lake env lean book/checks/RunIntegralExamples.lean
```

After the original reader and Cartwright map build:

```sh
python3 book/add_integral_portfolio.py
python3 book/checks/test_integral_portfolio.py
python3 book/checks/integral_portfolio_browser.py
```

The audit rejects mismatched theorem types, use of an alternative proof root,
transitive sorryAx, native Mathlib or native-owned noncomputable dependencies,
and borrowing an evaluation to validate or identify its input quadrature. The
shared arithmetic is checked not to reach native or Mathlib real types. The
browser test checks all four maps, 32 accounting selections, all route views,
exact Lean text, mathematical rendering, the theorem iframe and mobile layout.
Existing cosine, dyadic, Cartwright graphs and prior measurements are preserved
by hashes. The original first two chapter sources are unchanged.
