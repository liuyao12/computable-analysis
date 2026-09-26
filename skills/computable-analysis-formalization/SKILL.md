---
name: computable-analysis-formalization
description: Formalize calculus, elementary-function, integral, series, inverse-function, or finite ODE claims in this repository using rational interval algorithms and explicit certificates. Use when an outside reader or agent needs to add, review, or explain a completeness-free computable-analysis construction in Lean.
---

# Computable Analysis Formalization

Build computable foundations with rational interval algorithms and explicit
error certificates; expose exact mathematical theorems over valid represented
reals using `RealRaw.Equiv`. Follow the
[governing policy](../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems).
Package internal bounds, precision schedules, and partitions beneath the public
theorem, proving the agreement and representation-invariance bridges needed to
do so. Symbolic differentiation or a rational-input certificate alone does not
complete a requested exact theorem for represented real inputs.

Read [FORMALIZATION_GUIDE.md](../../FORMALIZATION_GUIDE.md) before choosing an
interface. Read [references/computation-certificate-catalog.md](references/computation-certificate-catalog.md)
to route a new task. Read
[references/integral-computation-strategies.md](references/integral-computation-strategies.md)
for any definite-integral task, especially one with non-rational breakpoints.

## Start with the theorem contract

The project favors laws about supplied, justified constructions over the
search for maximally general existence conditions. Decide whether the task
asks for a construction, a conditional law, or a comparison. State the supplied
objects, their mathematical evidence, and the new conclusion before choosing
an interface. A proved conditional law is complete on its stated domain even
when no universal constructor is available. A record declaration is not a proof.

For a concrete application, construct the required evidence. Do not put the
requested conclusion into a certificate and call its projection the theorem.
Preserve genuine domain and branch restrictions, represented-input scope,
and the distinction between existence of a valid name and an executable
constructor. Use [theorem-contract strategies](references/theorem-contract-strategies.md)
when choosing the scope of a new result or reviewing an existing interface.

## Methods belong in the skill

Choosing how to compute a definite integral or an infinite series is a
formalization strategy. Keep that choice here and in the strategy references,
not in a universal Lean definition of integration or infinite summation.
For a particular example, define its finite computation and prove its range
or tail bounds, validity, and agreement with the intended expression.

Reuse proved finite arithmetic, enclosure, and convergence lemmas. A Lean
record may conveniently bundle the data already needed by such a proof; it
is optional proof organization, not the meaning of every integral or series.
Do not make an existing certificate record a mandatory public interface, or
add a new structure merely to encode a recipe. Prefer a concrete worked
construction before extracting shared proof data justified by actual reuse.

Consult [integral strategies](references/integral-computation-strategies.md)
for whole-chunk ranges, geometric complex segments, and comparisons, and
[series strategies](references/series-computation-strategies.md) for finite
prefixes, tail control, and comparisons. The strategy is guidance; every
mathematical bound and claimed equivalence still needs a Lean proof.

## Keep the foundation boundary

- Use project modules for the analytic foundation. The user permits abstract
  Mathlib point-set topology only after auditing its transitive imports to
  exclude Mathlib real and complex numbers. This supersedes the earlier
  blanket Mathlib ban; it does not authorize Mathlib real analysis.
- Use rational numbers, finite lists, natural recursion, and explicitly stated
  rational inequalities.
- Do not appeal to a completed real number, compactness, least upper bounds,
  or an unstated choice of a real point to bypass the computable estimates.
  Abstract topology is permitted under the import boundary above.
- Represent a non-rational value by a `RealRaw` interval algorithm and prove
  `RealRaw.Valid` before consuming it as a computation.
- Prove equality of implementations with `RealRaw.Equiv`, not by treating raw
  values as definitionally equal.

## Follow the certificate workflow

Use these steps for a concrete construction. For a conditional law, supplied
objects and certificates replace the corresponding construction steps; prove
the estimates and consequences needed for the new conclusion.

1. State the exact scientific or calculus claim on its full intended domain,
   including arbitrary valid represented inputs and coefficients. Keep genuine
   domain and branch hypotheses explicit; choose rational intervals or charts
   internally for the proof.
2. For a construction, choose a computation route from the certificate catalog.
   For a conditional law, retain the supplied evidence and prove the new
   consequence; do not require a universal constructor first.
3. Define a literal evaluator returning rational boxes. Make its stage
   computation inspectable by reduction or by a theorem describing it.
4. Prove its local algebra: ordered endpoints, inclusions, finite-sum
   identities, and an explicit width bound.
5. Prove validity and a rational convergence schedule. Use prefix
   stabilization when a shrinking candidate overlaps a valid anchor. If the
   evidence is a two-edge chain through a non-nested middle computation, use
   `RealRaw.overlapChainStabilize`; do not assume overlap is transitive.
6. State the function-specific semantic bridge: an endpoint identity, a
   range enclosure, a comparison with an independently valid raw evaluator,
   or a finite recurrence. Do not silently promote an interface to a theorem.
7. Prove the stated conclusion on its full intended domain, with representation
   invariance and any agreement needed to hide internal choices. Report a
   conditional law as such. For a requested concrete identity, construct its
   missing bridges; an uninstantiated interface is not its proof.

For complex differentiability and holomorphicity, use the
[holomorphic-functions skill](../holomorphic-functions/SKILL.md). It supplies
the local derivative and derivative-continuity workflow; formal jets alone
do not establish these properties.

## Choose the narrowest useful route

| Task shape | Start with | Required extra evidence |
| --- | --- | --- |
| Exact rational algebra or polynomial identity | `Basic`, `Algebraic`, `Polynomial` | Exact equality or finite factorization |
| One computable number | `RealRaw` and `QInterval` | Valid boxes, a width modulus, and equivalence when comparing definitions |
| Rational function on an interval | `FunctionDomains` | A denominator-apart certificate on the whole interval |
| Continuity of a boxed function | `IntervalRegularOn` | A literal rational epsilon-delta modulus |
| Derivative or closed-form definite integral | `Differential`, `EffectiveCalculusFoundation` | Finite-difference enclosure and a particular endpoint bridge |
| Definite integral | `IntegralFoundation` plus the integral reference | A construction for this function, not a general existence assertion |
| Turning point or irrational split | `TurningPointIntegral` | Shrinking rational brackets and a central range estimate |
| Power series or a tail | `PowerSeries`, `Series`, `ExpProofs` | A rational tail majorant and a rate |
| Monotone inverse or algebraic branch | `Extension`, `AlgebraicFunctions` | Separation, range, and bisection certificates |
| Sampled linear ODE | `PeanoBaker` | A finite recurrence, chronological product identity, and any stated tail bound |

## Treat integrals as particular computations

Use whole-chunk outer enclosures as the defining finite sums. Prove the
particular function's coordinate monotonicity or range bounds, then multiply
by chunk lengths or finite complex displacements. Pointwise samples alone
are not ranges. Geometrically subdivide straight complex segments; a real
parameter is optional comparison data, not their integral definition.

`Integral.EnclosureConstructionFor` retains the real range proofs;
`EnclosureRealizationFor` permits an endpoint or accelerated evaluator only
after its enclosure comparison. `CandidateFor` and `SampleConstruction`
certify numerical values only. Never promote them by validity alone. Read
[the native integral audit](../../docs/INTEGRAL_ENCLOSURES.md) when migrating
a legacy client.


Interpret a request for a primitive as an exact definite-integral identity
\(\int_a^x f(t)\,dt \simeq F(x)-F(a)\), or a normalized expression
\(G_a(x)\) with \(G_a(a)\simeq 0\). Do not introduce a separate primitive
or indefinite-integral notion. Certify the entire segment between the base
point and the variable endpoint, with no singularity crossing and valid
branches throughout. Checking only endpoints, or proving only the derivative
formula, does not establish this theorem. See the
[definite-integral convention](../../FORMALIZATION_GUIDE.md#state-integration-formulas-as-definite-integrals).

Construct a definite integral only after identifying why that integrand can be
controlled. Use one of the concrete routes in the integral reference:
monotone rectangles, a rational-Lipschitz Darboux estimate, a fixed rational
partition, a shrinking non-rational turning-point bracket, or a direct
finite change-of-variables comparison. Supply a separate completion theorem
that connects the runtime boxes to the intended integral value.

For a derivative-bound FTC proof, `EffectiveDerivativeBoundFTC` and
`FunctionOnInterval.ofRealFunRaw` can supply the data for
`Integral.enclosureRealizationOfEffectiveFTC`. Its `agreement` field packages
the endpoint comparison, while its `plan` retains the whole-cell ranges. This
is an available proof package, not a required definition for every example.
The older `Integral.effectiveFTCConstructionFor` exposes a numerical candidate
only; do not stop at that adapter or the internal stabilized raw evaluator.

Do not introduce a universal integral merely because a function is bounded,
continuous, or pointwise defined. Record a reusable pattern only when every
hypothesis needed for its finite proof is visible in the structure.

## Verify before claiming progress

Run the smallest relevant Lean file while iterating, then run:

```bash
lake build ComputableAnalysis ComputableAnalysis.Blueprint
lake exe checkdecls blueprint/lean_decls
rg -n '^import\s+(Mathlib|Mathlib\.|Std\.|Batteries\.)' ComputableAnalysis
rg -n '\b(sorry|admit)\b' ComputableAnalysis
```

Update the blueprint, `GOALS.md`, and `FORMALIZATION_GUIDE.md` whenever a new
certificate changes the public capability boundary. Mark a result as checked
only when its Lean theorem and its stated hypotheses have both been verified.
