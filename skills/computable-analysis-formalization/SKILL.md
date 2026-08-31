---
name: computable-analysis-formalization
description: Formalize calculus, elementary-function, integral, series, inverse-function, or finite ODE claims in this repository using rational interval algorithms and explicit certificates. Use when an outside reader or agent needs to add, review, or explain a completeness-free computable-analysis construction in Lean.
---

# Computable Analysis Formalization

Build a theorem as a checked computation with rational interval output. Keep a
mathematical result separate from the code that evaluates it, the certificate
that makes the evaluator valid, and any proof that two evaluators agree.

Read [FORMALIZATION_GUIDE.md](../../FORMALIZATION_GUIDE.md) before choosing an
interface. Read [references/computation-certificate-catalog.md](references/computation-certificate-catalog.md)
to route a new task. Read
[references/integral-computation-strategies.md](references/integral-computation-strategies.md)
for any definite-integral task, especially one with non-rational breakpoints.

## Keep the foundation boundary

- Import only project modules. Do not import `Mathlib`, `Std`, or `Batteries`.
- Use rational numbers, finite lists, natural recursion, and explicitly stated
  rational inequalities.
- Do not appeal to a completed real number, compactness, least upper bounds,
  topology, or an unstated choice of a real point.
- Represent a non-rational value by a `RealRaw` interval algorithm and prove
  `RealRaw.Valid` before consuming it as a computation.
- Prove equality of implementations with `RealRaw.Equiv`, not by treating raw
  values as definitionally equal.

## Follow the certificate workflow

1. State the scientific or calculus claim on a rational closed interval, with
   all domain, sign, orientation, and branch hypotheses explicit.
2. Choose a computation route from the certificate catalog. Prefer an existing
   concrete constructor to a new general abstraction.
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
7. Publish the friendly mathematical theorem only after the preceding
   certificates are checked.

## Choose the narrowest useful route

| Task shape | Start with | Required extra evidence |
| --- | --- | --- |
| Exact rational algebra or polynomial identity | `Basic`, `Algebraic`, `Polynomial` | Exact equality or finite factorization |
| One computable number | `RealRaw` and `QInterval` | Valid boxes, a width modulus, and equivalence when comparing definitions |
| Rational function on an interval | `FunctionDomains` | A denominator-apart certificate on the whole interval |
| Continuity of a boxed function | `IntervalRegularOn` | A literal rational epsilon-delta modulus |
| Derivative or textbook primitive | `Differential`, `EffectiveCalculusFoundation` | Finite-difference enclosure and a particular endpoint bridge |
| Definite integral | `IntegralFoundation` plus the integral reference | A construction for this function, not a general existence assertion |
| Turning point or irrational split | `TurningPointIntegral` | Shrinking rational brackets and a central range estimate |
| Power series or a tail | `PowerSeries`, `Series`, `ExpProofs` | A rational tail majorant and a rate |
| Monotone inverse or algebraic branch | `Extension`, `AlgebraicFunctions` | Separation, range, and bisection certificates |
| Sampled linear ODE | `PeanoBaker` | A finite recurrence, chronological product identity, and any stated tail bound |

## Treat integrals as particular computations

Construct a definite integral only after identifying why that integrand can be
controlled. Use one of the concrete routes in the integral reference:
monotone rectangles, a rational-Lipschitz Darboux estimate, a fixed rational
partition, a shrinking non-rational turning-point bracket, or a direct
finite change-of-variables comparison. Supply a separate completion theorem
that connects the runtime boxes to the intended integral value.

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
