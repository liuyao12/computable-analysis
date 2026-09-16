# Proof size inside the map, and Mathlib's actual calculus dependencies

The original cosine proof map now displays a comparison panel without leaving
the mathematical view. Declaration counts follow the stored theorem types and
bodies, including opaque proof bodies; they are not counts of imported modules.
The panel switches between endpoint identity, convergence, and their dependency
union. Shared prerequisites are charged once. It also offers full, beyond-the-
statement, and beyond-the-shared-library accounting baselines.

LOC means the union of available compiler source ranges, stripped of comments
and blank lines. It includes supporting definitions and proof scripts. Coverage
is shown beside every total. Source files or ranges that are unavailable are
not treated as zero-work proofs. The breakdown separates native project,
representation bridges, Mathlib, Lean/Std, and other dependencies. The original
benchmark roots, proof terms and measurement JSON are unchanged.

The full endpoint-identity totals at the current pinned proof source are:

| Route | Referenced declarations | Mapped source LOC | Source-mapped declarations |
| --- | ---: | ---: | ---: |
| Direct inequalities | 5596 | 8955 | 939 |
| Concave FTC | 5674 | 9124 | 960 |
| Mathlib with bridges | 42849 | 81510 | 25374 |

These are a footprint of a particular contract and source snapshot, not a proof
of conceptual minimality. Many generated declarations have no independent source
range; the source-line and declaration totals measure different objects.

## Expanded Mathlib branch

The existing exponential/trigonometry bundle remains one node. Four additional
bundles expose the mathematical construction used by the comparison:

- Nonnegative Lebesgue integral: finite simple functions and their supremum;
  also the norm-integral/measurability hypotheses used by Mathlib's L1 theory.
- General Bochner integral: simple-function integration, the continuous extension
  to L1, and the general function-level integral. The pinned definition defaults
  to zero when integrability or target completeness is absent. For real-valued
  functions it gives the usual Lebesgue integral.
- Mathlib interval integral: the difference of integrals over restricted measures
  on (a,b] and (b,a], normally using Lebesgue measure. Integral order and finite
  additivity are the steps used by the quadrature correspondence.
- Mathlib FTC: `integral_eq_sub_of_hasDerivAt`, `integral_deriv_eq_sub` and its
  primed variant, with their complete derivative/integrability hypotheses.

`integral_cos` really calls `intervalIntegral.integral_deriv_eq_sub'`; the new
arrow is not editorial guesswork. The arctangent bridge also uses an FTC theorem
for the rational kernel. The cosine quadrature correspondence still does NOT
use the cosine primitive identity. Each displayed connection is witnessed by
stored Lean references and distinguishes definition/type dependencies (black)
from proof-body use (colored).

Mathlib's `Integrable` predicate is displayed only as part of its foundation.
No native integrability predicate, noncomputable numerical dependency, or new
hypothesis has been introduced. The new selected declarations are already in
the measured Mathlib proof closure; displaying them does not increase its cost.

## Checks and implementation

`comparison/checks/ExportMathlibMap.lean` exports the exact checked Mathlib types
and selected definition equations. No production theorem imports this exporter.
`book/expand_mathlib_map.py` builds the reference-checked additional bundles and
computes the inline comparison using the existing raw measurement report.
The original native route graphs are unchanged. Comparison data is revision-
matched at load time, and is not substituted from a stale cached report.

`test_mathlib_comparison.py` validates source coverage, union accounting, native
route isolation, all new edge witnesses and the actual FTC dependency.
`mathlib_comparison_browser.py` tests nine accounting combinations, grouped Lean
statements, node colors, exact numbers, rendered mathematics, mobile layout and
the theorem-side iframe. The generic interval/FTC objects are kept visibly
separate from the native selected-stage construction and its certificates.
