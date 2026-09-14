# Comparing the independent foundation with Mathlib

This is a maintained, optional Lake package **inside the same repository**.
It imports the native package by `path = ".."` and a pinned Mathlib revision.
The native `ComputableAnalysis` package neither requires nor imports Mathlib.
Installing or building this comparison is not required for native calculations.

## Build

From the repository root:

```sh
python3 comparison/checks/check_boundary.py
cd comparison
lake update
lake exe cache get Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean Mathlib/Tactic.lean
lake build MathlibComparison
lake env lean checks/ComparisonAudit.lean
```

The comparison uses the same Lean toolchain as the native package and pins
Mathlib to `51e6992efd06126df61a496bebf8f49482a4e129` (Lean 4.33.0-rc2).
The root package's dependency configuration is unchanged. CI builds the actual
comparison library and runs its audit, not just a sample Mathlib import.

## The three layers

`ComputableAnalysis/` remains the elementary rational-interval foundation.
`comparison/MathlibComparison/` imports both that foundation and Mathlib.
The comparison's proofs may use Mathlib's real completeness, calculus, and
special functions; those uses must be visible and must not become premises
of native proofs by a reverse import.

A theorem's hypotheses and target must be fixed before comparing proof sizes.
Compare the mathematical meaning of the same native algorithm, not merely
similar-looking formulas in different number types. The desired blueprint has
one statement node and labelled alternative proof routes; the raw declaration
reference graph is a separate audit view.

## Checked correspondence for numbers

`IntervalModel.lean` defines

```lean
Represents (X : RealRaw) (r : ℝ) : Prop :=
  ∀ n, ((X.compute n).lo : ℝ) ≤ r ∧ r ≤ ((X.compute n).hi : ℝ)
```

`RealModel.lean` proves that every valid native raw computation represents a
unique Mathlib real. Its noncomputable `denote X hX` uses a supremum **in the
comparison only**. On valid computations:

```lean
X.Equiv Y ↔ denote X hX = denote Y hY
X.Le Y ↔ denote X hX ≤ denote Y hY
```

The interpretation commutes with rational constants, addition, subtraction,
multiplication, and rational scaling. This is a faithful interpretation of
existing computations. It is not a claim of a computable evaluator for every
Mathlib real, or that real completeness has been derived inside the native
foundation. No universal inverse conversion is provided.

## Checked special-function bridges

`ArctanBridge.lean` proves, by Mathlib integral order on each rational rectangle,
that the native rectangle arctangent represents `Real.arctan`. The geometric
arctangent bridge follows from the previously checked native equivalence.
Four times the arctangent at one, `piCircleArea`, and `reciprocalPiRaw` are
identified with Mathlib's pi and its reciprocal.

`TrigonometryBridge.lean` proves, for the original inverse data
`B : ArctanInverseBisection` and rational `0 ≤ x ≤ 1/2`:

```lean
sine_represents B x hx :
  Represents (sinPiRawOfArctan B x hx) (Real.sin (Real.pi*(x:ℝ)))
cosine_represents B x hx :
  Represents (cosPiRawOfArctan B x hx) (Real.cos (Real.pi*(x:ℝ)))
```

These bridge the actual existing definitions, not replacements defined using
Mathlib. The proof identifies the inverse arctangent parameter, then uses
rational circle coordinates and Mathlib's double-angle/arctangent identities.
It does not invoke either native cosine-integral conclusion or the normalized
sine-derivative theorem. A closed native inverse provider can be substituted
for B without changing the bridge; this package does not assume that unpushed
closed-provider work is already part of the repository.

## What is not yet a third proof

`MathlibRoute.lean` proves the Mathlib-side formula

```lean
mathlib_cosine_primitive (t : ℝ) :
  (∫ x in (0:ℝ)..t, Real.cos (Real.pi*x)) = Real.sin (Real.pi*t)/Real.pi
```

The remaining link is an independent identification of the **native finite-sum
integral program** with this Mathlib interval integral. Pointwise sine/cosine
bridges alone do not prove that link. Using a native endpoint theorem to
identify that integral would make the proposed third proof circular as a
comparison. Accordingly, this file is not registered as a third inhabitant
of the native cosine-integral statement, and the live graph is not changed
by this package addition.

## Comparing costs fairly

Report final proof-body size, transitive prerequisite sizes, and reused/shared
material separately. The Mathlib route must charge its representation bridges
as well as the native statement and its Mathlib lemmas. Also report cold and
warm checking/elaboration separately from numerical runtime: noncomputable
Mathlib real functions are not a timing substitute for interval evaluators.
Record the toolchain, Mathlib revision, hypotheses, domains, and collected
axioms. Axiom counts alone neither measure completeness use nor mathematical
strength; the interpretation's use of a supremum is separately visible.

## Audits

`check_boundary.py` scans all native sources for reverse imports, checks that
the root package has no Mathlib dependency, checks matching toolchains and
an immutable comparison pin, and rejects new admitted/native-decision proofs
in comparison production files.

`ComparisonAudit.lean` exercises endpoint examples, inspects axiom dependencies
of 15 comparison results, checks that the sine/cosine bridges do not borrow
native derivative or integral conclusions, and checks native declaration
bodies remain free of Mathlib dependencies even in the combined environment.
Existing native-computation axioms inherited from the native library remain
visible; no claim of kernel-only arithmetic throughout the old library is made.
