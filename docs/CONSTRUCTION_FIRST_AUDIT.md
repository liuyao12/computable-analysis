# Construct the objects; prove their laws

The project studies particular, mathematically justified computations and
general laws about such computations. A theorem may start with supplied
constructions and their stated properties. It need not first solve the separate
problem of producing those constructions under the weakest possible hypotheses.

“Formally defined” means more than a Lean term with the right type. A raw
evaluator needs validity; a function needs its domain and representation
invariance; a purported derivative, integral, root, or solution needs evidence
connecting the computation to that mathematical role. Those properties are
legitimate hypotheses of a general law. They must be proved for a concrete
application. The law's conclusion must not be smuggled into the hypotheses.

## What was reviewed

The [inventory](CONSTRUCTION_FIRST_INVENTORY.json) covers every tracked Lean
source in the published development: 284 native modules and 70 other files
(14 entry points/checking scripts, 10 companion files, and 46 historical files).
Every source is assigned an area and bound to its content hash. Entry points,
theorem ledgers, representative theorem hypotheses and proof-data records,
and concrete applications were reviewed across the areas below.

This is an architectural and theorem-contract audit, not a new kernel check
of every declaration or a claim that every historical module is in the active
build. The source scanner verifies coverage and hashes; it cannot determine
whether a hypothesis carries the substance of a conclusion. The findings below
come from reading those contracts. The unpublished working tree was examined
separately; it is not silently included in the published proof inventory.

## Four different accomplishments

| Accomplishment | What must be proved | What it does not claim |
| --- | --- | --- |
| A construction | The specified algorithm has the required mathematical properties on its stated domain. | A universal construction for every classical input. |
| A conditional law | The stated properties of the supplied objects imply a new conclusion. | An algorithm producing all of the supplied objects. |
| A comparison or transport | An independently justified computation or property transfers to another presentation. | An independent derivation of a comparison already supplied as a premise. |
| An interface or target | The data and obligations are specified. | That anyone has constructed an instance or proved the proposed conclusion. |

A conditional law is a completed mathematical result on its stated domain,
not an unfinished existence theorem. A record declaration alone is not a law.
An existence theorem already proved remains valuable; this principle does not
weaken it or replace its proof with a hypothesis.

## Findings across the native development

The counts assign each module one primary area for navigation. Several modules
also support other areas. They are source counts, not theorem-completion scores.

| Area | Modules | Assessment and direction |
| --- | ---: | --- |
| Representations and function domains | 8 | `Basic`, `FunctionDomains`, and `Extension` distinguish evaluators from their certificates. Keep validity and equivalence invariance as mathematical obligations. `UniformRealFun.CertifiedExtension` supplies extension validity and invariance; it is packaging, not a derivation of them from the modulus alone. |
| Finite algebra and number theory | 29 | Exact arithmetic, inequalities, divisibility, and finite combinatorics already fit. Retain their proved generality; no analytic existence layer is needed. |
| Roots and inverses | 29 | Bisection, exclusion, deflation, and supplied-root formulas are good examples of separate constructors and laws. Removing a supplied root is a complete algebraic operation, not an FTA existence proof. Keep separation and branch evidence explicit. |
| Circle and geometry | 28 | Finite rational geometry, circle computations, rotations, and equivalence proofs supply concrete objects. Keep orientation and domain hypotheses, and distinguish a geometric comparison from a named representation target. |
| Real local calculus | 14 | Finite secant estimates and derivative certificates support laws about given differentiable computations. A general law may consume those certificates. A requested derivative of a named function still requires their construction and the appropriate represented-input bridge. |
| Integration | 22 | Whole-chunk sums and particular FTC comparisons fit directly. Enclosure records are optional proof organization. Candidate validity is not integrand semantics; endpoint comparisons are not independent integration arguments. |
| Series | 20 | Finite prefixes, alternating brackets, majorants, and comparison bounds fit. `RationalSeriesCertificate` is one sufficient construction pattern. Its one-step refinement condition is not a necessary definition of every convergent series; other stage choices and methods remain available. |
| Fourier computations | 6 | `EffectiveFourierTailCertificate` derives a valid computation from finite future-tail bounds. This is a substantive conditional result. Sample and coefficient records do not establish a general Fourier reconstruction theorem for arbitrary functions. |
| Elementary functions | 7 | Construct particular exponential, logarithm, and inverse computations and prove their relationships. Keep branch and inverse data where needed. Records collecting already-proved identities organize an application; they do not discover those identities. |
| Rational-function calculus | 25 | Supplied factorizations are legitimate hypotheses of partial-fraction and formula-compiler laws. Factorization existence is separate. A formal derivative identity still needs its analytic interpretation before it can be advertised as a definite-integral evaluation. |
| Complex local calculus | 12 | Finite jets, rational local models, and represented secant estimates support reusable algebra. A formal jet is not by itself a derivative of an evaluated function; preserve that distinction when assembling charts. |
| Contours and Cauchy reconstruction | 19 | Triangle cancellation and reconstruction from supplied Cauchy data are useful laws in their own right. The Cauchy representation and boundary-moment convergence are genuine hypotheses. Deriving them from complex differentiability and comparing quadrature to direct contour rectangles are separate results. |
| ODEs and growth | 5 | Finite recurrence algebra and growth estimates work without a universal solver. `LinearSolution.fuchs_growth` derives a growth bound from local solution estimates. The older mesh/Volterra uniqueness adapters also require an error comparison, which must remain visible. |
| Algebraic ODEs | 15 | Formal Frobenius recurrence, polynomial classifications, terminating solutions, and Painlevé seeds fit. Neither supplying a solution nor defining its equation proves the general Fuchs theorem or Painlevé classification. |
| Apéry constructions | 5 | Independent binomial sums yield the recurrence and differential equation; local series estimates give analytic meaning. This is a strong construction-first example. Identifying the arithmetic approximants with the separate zeta computation remains a different theorem. |
| Zeta and Basel | 25 | Keep the constructed zeta evaluator, proved native Basel identity, and finite Euler-sieve implication at their actual scopes. The prime-unboundedness implication may assume the stated irrationality fact; connecting the earlier proof of that fact is a separate application step. |
| Entry points and ledgers | 15 | Imports and theorem registries should report the distinctions above. An import, declaration count, or certificate name is not evidence of a classical theorem's full scope. |

## Representative contracts inspected

### A general growth law without general existence

[`LinearGrowth.lean`](../ComputableAnalysis/LinearGrowth.lean) defines
`LinearSolution` using valid vector boxes and a local residual estimate for
the supplied matrix function. It does not assume a growth conclusion.
`LinearSolution.fuchs_growth` proves, for rational endpoints
\(0<a\le b\le R\),
\[
\lVert y(a)\rVert_1\le \frac{b^N M}{a^N},
\]
from the endpoint norm bound \(\lVert y(b)\rVert_1\le M\) and the column-sum
bound on \(tA(t)\). This is precisely a useful theorem about supplied solutions.
It does not require a theorem constructing every solution or establish the
full complex regular-singular classification.

### Cauchy data imply a series representation

[`CauchyTaylor.Disk`](../ComputableAnalysis/CauchyTaylorDisk.lean) consumes
a Cauchy-kernel quadrature representation and separately convergent moments.
It constructs an independent series evaluator and proves exact agreement on
the certified rational disk. The given representation is not already a Taylor
expansion. This is a completed conditional reconstruction theorem. The
[larger Taylor programme](CAUCHY_TAYLOR.md) still has separate contour,
derivative-coefficient, and represented-input obligations.

### Local integration evidence versus assumed comparisons

[`EffectiveFTC`](../ComputableAnalysis/Calculus.lean) already supplies a
quantitative comparison between sampled sums and endpoint differences.
The subsequent equality theorem is a transport result from that evidence.
`EffectiveDerivativeBoundFTC` instead organizes whole-cell derivative bounds,
local controls, and precision agreement for a finite telescoping argument.
[`IntegralEnclosure`](../ComputableAnalysis/IntegralEnclosure.lean) retains
that range evidence. Both packages can be useful; their mathematical inputs
must be stated accurately. Neither is a required universal definition of an
integral. See the [integral audit](INTEGRAL_ENCLOSURES.md).

### Uniqueness needs a link to the particular solutions

[`SelfDerivativeDirectMeshComparison`](../ComputableAnalysis/ScalarODEUniqueness.lean)
and [`SelfDerivativeVolterraComparison`](../ComputableAnalysis/PeanoBaker.lean)
take an error function, a decay estimate, and a link from zero error to
equivalence of the two supplied functions. Their conclusions are legitimate
conditional uniqueness results. The solution certificates alone do not
construct these comparison data in those adapters. Documentation must not
abbreviate them to uniqueness from derivative existence alone.

### Optional series packaging is not the definition of convergence

[`RationalSeriesCertificate`](../ComputableAnalysis/SeriesFoundation.lean)
uses a finite prefix and remainder satisfying a one-step nesting inequality.
Its validity and addition laws are proved. The
[`AlternatingRaw`](../ComputableAnalysis/Series.lean) route proves a different
bracketing argument. Choosing between such constructions belongs in the
[series skill reference](../skills/computable-analysis-formalization/references/series-computation-strategies.md).
No effort to find the weakest common hypotheses is needed before either law
can be used.

## Boundaries retained

- Mathematical hypotheses remain substantive: domain compatibility, pole
  avoidance, branch selection, derivative or equation evidence, and justified
  convergence cannot be replaced by the statement that some code typechecks.
- Arbitrary valid represented inputs remain the domain of a theorem that
  claims real or complex inputs. Restricting to rational inputs is a separate
  scope choice and must be stated. Existential proofs of valid names do not
  automatically yield executable constructors; inspect computational witness
  dependencies separately from classical reasoning in proofs.
- The 46 historical files retain their source status. The 10 companion files
  include the isolated Mathlib Euler development and pinned comparison proofs.
  Their existence does not add a native represented-value theorem or a
  cross-foundation agreement proof.
- Unpublished FTA, PDE, boundary-value, polynomial-limit, and represented-kernel
  developments require their own contracts. In particular, formal differential
  algebra must be distinguished from an analytic realization of its carrier;
  a field containing a fundamental-solution equation is not an existence proof.

## Changes made after the audit

The governing guide, contributor instructions, roadmap, README, formalization
skill, and reader's purpose page now adopt this principle. The skill asks for
the supplied objects, their evidence, and the genuinely new conclusion before
choosing a construction method. Conditional laws and constructors are tracked
separately. Older scope notes remain as historical evidence, with a current
status explanation before them where needed.

No Lean statement has been weakened, no existence theorem has been replaced
by a premise, and no record has been removed merely for being general. The
existing mathematics can follow this principle without such a rewrite.
Future refactoring should be driven by a concrete application: remove a
redundant wrapper when it obscures a proof, and derive missing evidence when
the application needs it. It should not be driven by maximizing the generality
of sufficient conditions.
