# Comparison with Mathlib

The native foundation consists of rational interval algorithms, refinement
certificates, and implementation-equivalence proofs. It does not import
Mathlib's real numbers. The optional [comparison package](comparison/README.md)
imports both this same native package and a pinned compatible Mathlib.

## One computational statement, three proofs

The common statement is `ComputableAnalysis.CosinePrimitive.Statement`:
for rational `0 <= t <= 1/2`, the independently computed cosine integral from
zero to t is `RealRaw.Equiv` to `S(t)/pi`. Here pi is literally four times the
native arctangent at one, and S and C use the closed native inverse provider.
No caller-supplied inverse provider or bridge hypothesis remains.

The three named proofs are `CosinePrimitive.viaInequalities`,
`CosinePrimitive.viaFTC`, and `CosinePrimitive.viaMathlib`. The first two are
native; the last is defined only in the optional comparison package.

The value bridges identify arctangent, pi, sine, and cosine with Mathlib's
functions. The independent quadrature bridge integrates cellwise Lipschitz
bounds and uses finite additivity to identify our actual cosine-sum program
with Mathlib's interval integral. It does not borrow a native endpoint proof.
The Mathlib primitive formula then supplies the third proof of exactly the
same computational proposition, not a parallel result about different objects.

Every valid RealRaw has a unique interpretation in Mathlib reals; equivalence
and order are reflected by this interpretation. Its current implementation
uses a supremum in the comparison layer. No universal computable reverse
conversion from arbitrary Mathlib reals is claimed.

## Graph and measurements

The [three-proof blueprint](blueprint/three-proofs/README.md) has one theorem
node with alternative proof routes converging on it. It uses ordinary
blueprint theorem modals, with selected mathematical landmarks and hidden
arithmetic helpers. Every contracted reference path is inspectable.

The audit checks complete theorem-type equality, native Mathlib-independence,
separation of the three proof routes, and absence of transitive sorryAx.
Final proof-body size, native prerequisites, bridge declarations, Mathlib
prerequisites, and Lean/other dependencies are reported separately. These
counts are not measures of mathematical elegance or discovery difficulty.
Axiom counts alone do not measure uses of completeness.

Native computable complex exponentials remain part of the project. The
existing factorial-series complex-box computation at rational imaginary
inputs is shown as an optional companion, not as Mathlib's exponential or
as a premise of any of the three integral proofs.
