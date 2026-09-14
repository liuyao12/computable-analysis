# Comparison with Mathlib

This project develops its own proof-oriented foundation for computable real
and complex analysis. The native foundation remains rational interval
algorithms, stage-indexed refinement, certified domains, and explicit
implementation-equivalence proofs. It does not import Mathlib's real numbers.

A maintained comparison package now lives in [comparison/](comparison/README.md).
It imports both **this same native package** and a pinned compatible Mathlib.
This is an explicit part of the repository, not a temporary external experiment.
The native package does not depend on the comparison package, so native users
do not have to install or build Mathlib.

## What the comparison proves

Every valid `RealRaw` has a unique interpretation as a Mathlib real. Native
`RealRaw.Equiv` and `RealRaw.Le` are equivalent to equality and order of these
interpretations; arithmetic is preserved. The comparison layer uses Mathlib
completeness to construct this interpretation, without putting completeness
into the independent foundation or claiming a computable reverse conversion
for every Mathlib real.

Checked special-function bridges identify the existing rectangle/geometric
arctangent, pi and reciprocal pi, and the first-quadrant inverse-arctangent
sine and cosine with Mathlib's definitions. The latter are proved for the
same inverse-provider data required by the native functions; they do not
replace the native algorithms or assume their comparison identities.

The Mathlib-side cosine integral formula is checked. An independent bridge
from the native quadrature program to Mathlib's interval integral is still
needed before this can be counted as a third proof of the same native
endpoint statement. Pointwise equality of integrands is not that bridge.

## Compare the same proposition

Fix the native domain, algorithm, and theorem statement. Native FTC,
native finite inequalities, and a Mathlib route with proved representation
bridges may then provide alternative terms of exactly that statement type.
The blueprint should show one statement node, with labelled alternative
proof routes converging on it. Keep the raw declaration-reference graph
separate rather than creating artificial cycles between a statement and
proof terms that mention it.

Measure final proof size, prerequisites, shared material, and bridge costs
separately. Measure numerical runtime separately from elaboration and kernel
checking. State where Mathlib real completeness is used; axiom counts alone
do not detect all uses of completeness or indicate mathematical strength.
A short library application is not the whole cost of a comparison proof.

A native theorem should still be evaluated by what its certificate supplies:

```text
domain -> stage algorithm -> validity -> finite estimate -> equivalence
```

The absence of a completed-real wrapper is not itself a defect. Conversely,
a certificate for a particular native computation is not automatically a
general classical theorem: its hypotheses and algorithm determine its scope.

See [the build instructions and audit](comparison/README.md). The repository
checks source boundaries and selected transitive theorem dependencies in the
combined environment. The comparison package is permitted to import Mathlib;
the native `ComputableAnalysis/` source tree is not.
