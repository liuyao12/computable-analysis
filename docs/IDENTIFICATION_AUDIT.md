# Validity and mathematical identification

The governing strategy is [in the master formalization skill](../skills/computable-analysis-formalization/SKILL.md#validate-the-computation-identify-the-object).
The [detailed reference](../skills/computable-analysis-formalization/references/identification-laws.md)
explains how to apply it. A valid interval algorithm represents a value;
separate laws justify calling it a particular number, function, integral,
derivative, or solution. The public laws should be usable without inspecting
the program, even when their proofs derive inequalities from its details.

## Scope of this first pass

This is the start of a continuing claim-by-claim audit, not a certification of
the whole project. The fixed published input is commit
`c38cfc25d224a98fdd36f2bf018f3cf51da7c8da`. The
[source inventory](IDENTIFICATION_INVENTORY.json) indexes every Lean,
Markdown, TeX and HTML source in that snapshot: 3,472 files, including 3,220
Lean files. There are 2,329 distinct file contents across the whole inventory;
many sources are copies in pinned proof bundles. Every entry is initially
marked `indexed-only`. The findings below are the contracts actually reviewed.

| Source boundary | Indexed files |
| --- | ---: |
| Main library and its root import | 359 |
| Companion and published Lean source copies | 2,790 |
| Lean checkers and entry points | 24 |
| Other Lean sources, including historical material | 47 |
| Exposition and guidance | 252 |

The local working tree is different. Its cloud-backed master guidance and
most source files were unavailable for reading during this pass. A metadata
inventory found 50 readable Lean files in the searched directories; these
were copied and scanned separately, and 25 differed from or were absent from
the published snapshot. Only the particular readable local contracts named
below were reviewed. No conclusion about unavailable local contents follows
from the published audit. Preserve those changes when applying this strategy.

This pass reads theorem statements and proof bodies and checks an exact
rational counterexample. It does not rerun the Lean kernel, certify every
declaration, or infer proof correctness from a declaration's name. Existing
build records remain evidence for their own pinned revisions.

## Reviewed claims

### Square root already provides a reusable identification law

In the main library,
[`AlgebraicFunctions.lean`](../ComputableAnalysis/AlgebraicFunctions.lean)
separates `sqrtRaw_valid` from `sqrtRaw_mul_self_equiv_of_domain`. For every
nonnegative rational \(q\), the latter proves
\[
\operatorname{sqrtRaw}(q)\cdot\operatorname{sqrtRaw}(q)\simeq q.
\]
The stage specification supplies nonnegative endpoints and squared bounds;
the identity's proof derives actual product-interval overlap. This covers
every nonnegative integer without a new proof for each number.
`sqrtRaw_equiv_of_spec` compares computations satisfying the same squared
interval specification. Status: **a function-level identification contract
with a substantive rational-interval proof**, on the stated rational domain.

`squareOnUnit_forward_sqrtRaw_equiv_rat` and `sqrtOnUnitBisectionSearch`
give the inverse interpretation on \([0,1]\). This adapter's domain should
not be mistaken for the domain of the general square-root identity. Chapter
1's monotone-inverse discussion supplies the mathematical strategy; its
general statement still needs the particular construction and domain evidence
when applied to a new function.

The foundation bundle's
[`SquareRootSecantNewton` source](../book/foundation-story/sources/ComputableAnalysis.SquareRootSecantNewton.lean)
separates `sqrtTwo_valid`, `sqrtTwo_mul_self_equiv_two`, and
`sqrtTwo_equiv_bisection`. This is another positive example. It is a pinned
bundle result rather than a new export of the main library. The separate
[`RepresentedPositiveSquareRoot` source](../book/foundation-story/sources/ComputableAnalysis.RepresentedPositiveSquareRoot.lean)
contains `sqrtComplex_square_equiv_raw` for its `PositiveInput` package;
retain its positive-margin and bound hypotheses rather than calling it an
unrestricted nonnegative-real inverse theorem.

**Exposition direction:** identify square root once as the nonnegative inverse
of squaring on the established domain, then specialize to constants. Keep the
preface's code and digits as motivation and leave detailed verification
optional. Do not require readers to inspect a recurrence to use the identity.

### The general Euler exponential candidate fails validity

[`Exp.lean`](../ComputableAnalysis/Exp.lean) defines `expEuler` with
\[
m=(n+1)^2,\qquad c_n=(1+x/m)^m,
\]
and radius \(1\) at stage zero and \(1/(2n)\) thereafter. At \(x=2\),
\[
I_0=[2,4],\qquad I_1=[73/16,89/16],\qquad 4<73/16.
\]
These intervals are disjoint. Consequently the literal candidate is not a
valid represented exponential on arbitrary rational inputs. This is an
exact rational counterexample, reproduced by the audit command below.
It is stronger than merely failing to locate a validity theorem.

`ExpProofs.expEuler_valid_of_nested` is conditional on nesting. It does not
contradict the counterexample and should retain its statement. Likewise, a
result about the specialization at \(1\) does not establish arbitrary-input
validity. Status: **candidate with a disproved general-validity claim**.

**Correction made:** the candidate's source comment now explicitly records
this boundary. Repairing its enclosure schedule and proving the advertised
domain is a concrete next formalization task. Do not weaken the meaning of
validity to accommodate it.

### A comparison package is not a derivation of agreement

[`ExpProofs.lean`](../ComputableAnalysis/ExpProofs.lean) defines
`EThreeWayRemainders` with three fields that are already `Equiv` statements.
`eThreeWayAgreement_of_remainders` collects those fields into a conjunction.
Status: **packaging of supplied comparisons**, not an independent estimate
or identification proof. This says nothing against other exponential proofs
in that file. The comment now describes the actual content instead of
calling the fields remaining finite remainder estimates.

### Integral candidates and integral evidence are distinct

[`Calculus.lean`](../ComputableAnalysis/Calculus.lean)'s
`Integral.CandidateFor` stores a computation and a validity proof. Its own
comment correctly says that the integrand parameter is only a label.
`candidateValue_valid` proves numerical validity, not an integral relation.
[`IntegralEnclosure.lean`](../ComputableAnalysis/IntegralEnclosure.lean)'s
`EnclosurePlanFor` adds whole-cell range and literal finite-sum evidence.

Status: **the distinction is present; each advertised integral still needs
its particular justified bridge**. Preserve the project's method-independent
integral policy: this sufficient enclosure route must not become a mandatory
definition for every construction. Do not promote a candidate by monotonicity
alone, by an assumed endpoint equality, or by a numerical comparison.

### Valid ball formulas are not yet geometric volumes or Gamma integrals

[`NBallGaussian.lean`](../ComputableAnalysis/NBallGaussian.lean) proves
`NBallRaw.value_valid` and `value_equiv` for represented formula evaluations.
The [existing scope note](N_BALL_GAMMA.md) explicitly separates these from
geometric-volume, Gamma-integral, and Gaussian-normalization bridges.
Status: **valid formula and coefficient algebra, with named analytic and
geometric identifications open at that scope**. Other rational-polytope
companion theorems retain their separately supplied geometric hypotheses.

### Fourier tail convergence is not a reconstruction theorem

In the readable local `EffectiveFourierTail.lean`,
`EffectiveFourierTailCertificate` supplies finite stages, future-coordinate
tail estimates and shrinking radii. `toSeries_valid` derives a valid
stabilized computation. These are substantive convergence results.
Status: **conditional construction of a valid value**. Identifying it with a
named function's Fourier reconstruction needs coefficient/function evidence
and a separate reconstruction argument. No global reconstruction failure is
claimed merely because this generic convergence module does not prove one.

### Conditional uniqueness keeps its comparison hypotheses

[`ScalarODEUniqueness.lean`](../ComputableAnalysis/ScalarODEUniqueness.lean)'s
`SelfDerivativeDirectMeshComparison` and
[`PeanoBaker.lean`](../ComputableAnalysis/PeanoBaker.lean)'s
`SelfDerivativeVolterraComparison` retain comparison/error evidence linking
two supplied functions. Their `equivalent` theorems are scoped conditional
laws. Status: **conditional comparison**. Do not describe them as uniqueness
from a formal derivative identity or from solution naming alone. A concrete
ODE identification must construct the actual equation and comparison evidence
needed by the chosen route.

## Next review work

1. Correct the Euler candidate's finite enclosure on its intended domain and
   derive validity before advertising a general exponential evaluator.
2. For each named function, pair the constructor with its validity,
   identification and representation-invariance statements, starting with
   exponential/logarithm and the trigonometric presentations. Keep the
   square-root function law as the reference example.
3. Review each integral and ODE claim against its actual supplied evidence,
   distinguishing newly derived inequalities from assumed comparisons.
4. Follow the existing open volume/Gamma/Gaussian bridges into their concrete
   applications. Do not retell formula validity as geometric meaning.
5. Continue through every indexed source and reader claim, including pinned
   bundles and historical files. Record human findings at claim scope, not a
   blanket pass for every file containing `Valid` or `Equiv`.
6. Read and reconcile the unavailable local guidance and unpublished sources
   before claiming workspace-wide coverage. This inventory is a starting
   queue, not a substitute for that review.

## Reproduce the coverage and counterexample

Use a readable checkout of the fixed published input as `SOURCE_SNAPSHOT`:

```sh
python3 scripts/audit_identification.py \
  --root SOURCE_SNAPSHOT \
  --revision c38cfc25d224a98fdd36f2bf018f3cf51da7c8da \
  --output docs/IDENTIFICATION_INVENTORY.json --check
```

The command checks source coverage and hashes and repeats the exact rational
Euler counterexample. It does not certify the semantic findings or run Lean.
New reviewed claims should cite their source, domain, evidence, proof boundary
and remaining bridge, following the master strategy.
