# Computable calculus for science and engineering

## Purpose

Develop an alternative foundation for the calculus used in science and
engineering, through terminating computations with certified rational output.
Numbers, elementary and special functions, integrals, derivatives and evolutions
must carry the data and estimates needed to compute with them. A broad existence
theorem is not a substitute for a construction.

The native foundation must not depend on Mathlib's completed real type or use
noncomputable declarations to obtain numerical data. The optional `comparison/`
package may deliberately import Mathlib to identify the same computations and
prove the same propositions by another route. The dependency is never reversed.

## Mathematics leads; Lean supports it

The public site is an evolving mathematical book. Keep the original Chapters 1
and 2 roughly intact. A theorem's margin links to a bundled proof map and, where
available, a comparison with Mathlib. Algorithms and convergence estimates are
mathematics and remain in the exposition; namespace plumbing, schedules chosen
only for software engineering, tactic scripts, and build logs do not lead the
narrative. Exact Lean declarations remain accessible behind the mathematical
bundles. An AI-curated bundle is a view of checked declarations, not a new axiom.

## Separate computation, correctness, and identification

Every public computation has a finite evaluator, explicit domain/branch or
separation data, and a proof that its output intervals are ordered, nested and
arbitrarily narrow. Useful moduli and conservative error estimates are stated
where needed. Terminating precision search is acceptable when its termination
is proved; no unspecified choice of a limit or real point can supply output.

An identity compares independently defined programs. Several proofs should
inhabit the same proposition with exactly the same hypotheses. Their common
statement cannot smuggle the desired identity into an assumed certificate.
Validity and endpoint equivalence remain separate proof obligations.

A computable numerical kernel does not imply a wholly constructive logic. The
compiler's noncomputable flags, uses of classical reasoning in proofs, and
native-computation axioms are separate audits. The new source inventory records
16 historical native `noncomputable def` declarations for replacement or
isolation; they are not silently accepted as meeting the target boundary.

## Development order and evidence

Start with the preserved interval and rational-geometry chapters. Build angle
and trigonometric theory from arctangent; show the cosine primitive as the first
fully compared worked theorem. Then extend the paired corpus to polynomial and
rational functions, actual derivative programs, exponentials and complex
rotations, and linear ODEs. Keep the existing later manuscripts available while
labeling their formal comparison status honestly.

For each family, freeze its domain and computation before measuring. Compare
full dependencies, reusable baseline costs, bridge costs, and cumulative unions
across theorems. Also test precision, execution, branch conditions and useful
error bounds. A smaller declaration graph for one example is not a proof of
conceptual minimality or engineering adequacy.

## Migration sequence

1. Replace the public documentation shell without rewriting protected chapters;
   provide theorem-side mathematical proof maps and preserve old bookmarks.
2. Audit the currently public native route and inventory all older noncomputable
   helpers. Replace choice-produced data with explicit witnesses or finite
   algorithms; split old compatibility interfaces where this requires a larger
   mathematical task. Do not remove `noncomputable` merely to improve a counter.
3. Grow proof maps and comparisons theorem by theorem, from the predeclared
   families in `comparison/proof-bench/suite.json`. Missing comparisons are not
   finished results. Keep formal status independent of prose maturity.
4. Add scientific worked problems with explicit inputs, certified tolerances,
   and performance measurements. Broader adequacy is established by these
   examples, not by a promise in the README.
