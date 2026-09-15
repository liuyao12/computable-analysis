# Comparing the independent foundation with Mathlib

This optional Lake package lives inside the same repository. It imports the
native package by `path = ".."` and a pinned Mathlib revision. The native
package neither requires nor imports Mathlib.

## Build and audit

From the repository root:

```sh
lake build ComputableAnalysis.CosinePrimitive ComputableAnalysis.RotationSeries
python3 comparison/checks/check_boundary.py
cd comparison
lake update
lake exe cache get Mathlib.Analysis.SpecialFunctions.Integrals.Basic Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds Mathlib.Tactic
lake build MathlibComparison
lake env lean checks/ComparisonAudit.lean
mkdir -p reports
lake env lean checks/ThreeProofsAudit.lean
```

Mathlib is pinned to `51e6992efd06126df61a496bebf8f49482a4e129`, matching the
native Lean 4.33.0-rc2 toolchain. CI builds the actual modules, not just a
sample Mathlib import. The root dependency configuration is unchanged.

## Generic number interpretation

`IntervalModel.lean` defines `Represents X r` to mean that every rational
output interval of X contains the Mathlib real r. `RealModel.lean` proves
unique representation for valid computations, preserves arithmetic, and
identifies native equivalence and order with equality and order in Mathlib.
Its current `denote` implementation uses a supremum in the comparison only.
This does not turn arbitrary Mathlib reals into executable native programs.

## Value bridges

`ArctanBridge.lean` compares the native rational rectangle computation with
Mathlib's integral of the rational arctangent kernel. It identifies geometric
arctangent, four times arctangent at one, circle-area pi, and reciprocal pi.

`TrigonometryBridge.lean` proves, for the original inverse provider data and
all rational x in [0,1/2], that the original sine and cosine computations
represent `Real.sin (Real.pi*x)` and `Real.cos (Real.pi*x)`. These are not new
native definitions. The proof uses the inverse-clock residual, convergence
of rational approximations, and double-arctangent coordinate identities.
It does not use either native cosine-integral conclusion. The new basepoint
statement instantiates the bridge with `ClosedArctanInverse.provider`.

## Three proofs of one native statement

`CosineIntegralBridge.lean` proves that the actual native quadrature represents
Mathlib's interval integral. A Lipschitz bound controls each cell; finite
additivity gives an error at most `4*t^2/m`, inside the native allowance
`4000*t^2/m`. It does not invoke either native endpoint proof or a primitive
formula. Every expanded mesh box, and hence each output intersection,
contains the Mathlib integral.

`MathlibComparison/CosinePrimitive.lean` combines this correspondence with
the checked Mathlib primitive formula and sine/pi bridges. The results are:

```lean
ComputableAnalysis.CosinePrimitive.viaInequalities
ComputableAnalysis.CosinePrimitive.viaFTC
ComputableAnalysis.CosinePrimitive.viaMathlib
```

Their complete theorem types are identical. Each route also has an
independently justified validity proof. The Mathlib result is exported only
by this comparison package, never by the native import root.

## Blueprint and trust boundary

The chapter `06-three-cosine-proofs.tex` presents arctangent, pi, S and C,
then one theorem with three alternative proofs. The focused graph preserves
normal blueprint statement modals, selects mathematical milestones, and
retains route identity during contraction and reduction. A native
factorial-series complex exponential on rational imaginary inputs is an
optional companion, not a premise of these three proofs.

`ThreeProofsAudit.lean` compares the complete theorem types and walks stored
types and bodies. It checks native Mathlib-independence, forbids cross-proof
reuse, requires the third route to use both kinds of bridges, and rejects
transitive sorryAx. Existing upstream native-computation axioms remain in
the audit. The graph builder checks every displayed reference witness,
acyclicity, one common conclusion, and all Lean names in the new chapter.

Proof measurements distinguish the final application from native, bridge,
Mathlib and Lean/other prerequisites. They count generated helpers, and do
not measure mathematical elegance or discovery difficulty. The current
interpretation's use of a supremum is explicit; axiom counts alone do not
measure completeness use. Numerical runtime is separate from proof cost.
