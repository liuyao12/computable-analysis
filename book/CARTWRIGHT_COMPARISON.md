# Arithmetic — calculus — arithmetic

The proposed next comparison is the weighted cosine family

    J_n = integral from 0 to 1 of (1-t*t)^n C(t/2) dt,
    lambda^(2n+1) J_n = 2^n n! P_n(lambda^2), lambda = pi/2.

The intended arithmetic application is irrationality of the geometrically
constructed pi squared. This is NOT yet a completed Lean theorem in this branch.
The current contribution proves and audits the arithmetic interfaces, publishes
a clearly labeled mathematical plan, and establishes how later route lengths
will be compared. Existing cosine proofs, maps, metrics and chapters are kept.

## Checked arithmetic before and after the analytic step

`ComputableAnalysis/CartwrightArithmetic.lean` defines the two-term recurrence
for P_n at rational inputs, and the integer recurrence

    K_0 = 1, K_1 = b,
    K_(n+2) = (2n+3) b K_(n+1) - a b K_n.

`denominator_cleared` proves K_n = b^n P_n(a/b) for a nonzero denominator. This
clears denominators without importing a polynomial-degree framework.

`factorial_dominates` proves, at the explicit N = 2*a*a,

    2*a^N < 2^N * factorial N.

`integer_obstruction` excludes any positive integer k satisfying the reverse
bound after multiplication by k. `no_positive_small_sequence` applies this to
any integer sequence satisfying the required inequalities. These are conditional
arithmetic results. Their hypotheses are not advertised as already established
for the intended cosine construction.

The exporter traverses actual stored types and bodies, not just imports. It
rejects dependencies on native computed reals, pi, integration, FTC, Mathlib,
native-owned noncomputable declarations, and sorryAx. Standard logical axiom
reports remain visible. Importing an elementary factorial from a source module
named PowerSeries does not mean using that module's analytic developments.

## The precise missing middle

Independently define and validate the monotone weighted quadratures, with one
successful supplied joint schedule. Prove the moment recurrence and evaluation.
Under a hypothetical rational value lambda^2 = a/b with a,b positive, transport
it to the integer recurrence and prove

    0 < K_n and K_n * 2^n * n! <= 2*a^n.

The evaluation, positivity and upper bound, representation transports, and the
final irrationality assembly remain to be formalized. No dummy axiom, assumed
moment certificate, admitted proof or empty score is substituted for them.

The three proposed routes are finite summation identities, native FTC/integration
by parts, and Mathlib integration with explicit quadrature/value bridges. Their
complete target types and chosen moment programs must be identical before they
enter the general paired-statement benchmark. The pinned Mathlib source
`Mathlib/Analysis/Real/Pi/Irrational.lean` uses this moment family, but its private
supporting lemmas and its public irrational_pi theorem do not by themselves
supply a bridge for our native program or the stronger pi-squared conclusion.

## Two views of the graph

The role view groups finite arithmetic preparation, the proposed middle
arguments, and the finite arithmetic conclusion. Checked arithmetic uses solid
nodes and reference-witnessed edges; unproved steps and their proposed uses are
explicitly marked planned/dashed. It is not called a verified proof graph or a
completed three-way comparison. All exact Lean cards are genuine arithmetic
exports; no future theorem signature is disguised as a checked declaration.

The eventual complete irrationality theorem still has transitive dependencies
on the selected calculus middle. A calculus-free consumer lemma does not erase
those dependencies. A second, actual-reference view and its metrics must retain
them. Display-node grouping must never change the underlying cost.

## Accounting for length

Current measurements cover only the shared arithmetic. Report declaration
closures, per-body distinct-expression counts, and unions of available source
ranges, with coverage and missing Lean-library files explicit. The two arithmetic
blocks share dependencies, so their combined cost is a union, not a sum.

For each completed middle route D_r, compare the full application closure, the
increment beyond the shared arithmetic, and the increment after the already
established cosine development is available. Keep native/bridge/Mathlib costs
separate. The bridge is real work for a native-output contract, but is reusable
and charged once in a corpus. Keep identity, convergence and the arithmetic
application as separate obligations, then measure their union.

No scores for the proposed middle proofs or full irrationality application are
published yet. The existing comparison JSON and SVGs are hash-checked unchanged.
No native integrability predicate is introduced.
