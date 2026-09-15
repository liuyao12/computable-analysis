# A paired-statement benchmark, not a proof-quality leaderboard

The native package and optional Mathlib comparison are measured in the same
pinned Lean environment. `cases.tsv` is the registry: case ID, route, full proof
name, and whether the route must be Mathlib-free. Add a case by importing its
proof module in `checks/ExportProofBench.lean`, registering its alternatives,
and supplying its contract in `suite.json`. A missing name, non-theorem,
nonidentical complete type, cross-alternative reuse, forbidden native import,
or transitive sorryAx fails the export. Planned cases never receive scores.

Run from `comparison/`:

```sh
lake build MathlibComparison.ProofBenchExamples
lake env lean checks/ExportProofBench.lean
python3 ../blueprint/checks/build_proof_bench.py
```

The initial suite has three matched obligations: cosine endpoint identity,
validity of that same cosine integral, and a sine-zero calibration. The first
two constitute ONE calculus example. The calibration is excluded from the
calculus portfolio. No broad foundation-simplicity claim follows from this
sample. Eight additional families are specified before looking at their scores.

## The measured objects

For root r let D(r) be r and all recursively referenced declaration types and
stored bodies, including opaque bodies. This is NOT an import graph or a claim
of a minimal mathematical basis. For a matched case let T be the corresponding
closure of the complete statement's references, and H the intersection of all
alternative D(r). The report shows three explicit accounting baselines:

* full: D(r), including the specified algorithms and existing library;
* statement-free: D(r) minus T, charging only material not needed to state the task;
* shared-free: D(r) minus H, charging route-specific material within this case.

The last two treat their explicit baselines as already available; they are not
claims that those prerequisites cost nothing. Equal theorem types include ALL
parameters and hypotheses. An assumption that simply contains the desired
answer must be ruled out by reviewing the common contract, not just by type
comparison. Mathematical generality still needs human comparison.

Each set is partitioned by actual owning module: native project, comparison
bridges, Mathlib, Lean/Std, and other dependencies. Report stored-body tree size
with repeated occurrences, structurally distinct subexpressions per body, and
type-expression sizes separately. Referenced named constants are NOT unfolded.
Per-declaration DAG sizes are summed without cross-declaration deduplication.
Literal values and native certificates are atomic nodes: a large computation
is not being expanded into a long kernel-arithmetic proof. Native certificates
therefore require the accompanying axiom audit, not an unqualified size claim.

Source-line counts union available compiler source ranges and remove blank
lines/nested comments. Coverage (mapped declarations and missing files) is
reported. They depend on formatting and declaration granularity. No file-size,
whole-module line count, kernel time, or elaboration time is presented as an
interchangeable measure. This version does NOT invent cold-build timings.

## Reuse across theorems

For the ordered shared calculus cases the portfolio computes U(k) as the union
of D(r_i) through case k for each route. The marginal cost is U(k) minus U(k-1).
A shared lemma or bridge is charged once. The site exposes the order and also
the order-independent final union. Different theorem orders change the marginal
profile. Do not report the sum of independent closure sizes as total library
cost. The sine-zero control is not an additional calculus theorem.

## What 'simpler' can mean

A smaller dependency footprint demonstrates a smaller *used formal library for
this contract*, not a theorem that all calculus needs fewer concepts. Separate:
(1) exact execution on rational boxes and its invariants; (2) completeness and
abstract function/measure APIs; (3) proof reuse over the fixed suite; (4) domain,
regularity, and effectiveness hypotheses; (5) runtime and trust boundary.
Both are built on the same Lean kernel. Native proofs may avoid the completed
real type without being axiom-free or automatically constructive in every
logical sense. The native statement format favors the native representation;
the bridge cost must be reported explicitly, while a Mathlib-only baseline is
a DIFFERENT contract and not another proof of the native proposition.

The roadmap includes arithmetic, rational/algebraic functions, differentiation,
integration, complex exponentials, and ODEs. Completeness-dependent existence
statements without executable data should be recorded as scope differences,
not assigned an artificial infinite proof-size penalty or silently weakened.

## Plan and acceptance gates

For every new family: freeze a native computation and domain; state its validity
and semantic obligations; implement native and comparison routes without
cross-proof reuse; prove required representation bridges; run identical-type
and axiom audits; add human-readable strategy statements; measure cold,
statement-free, and shared-free closures; update cumulative unions. Keep
failed/planned cases visible. Reassess across families, not by cherry-picking
the next theorem with the largest favorable ratio. Review the chosen contracts
before interpreting measurements. The initial framework tests set accounting
and source-range unions independently of the Lean exporter.
