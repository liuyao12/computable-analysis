# Sine-square and cosine-square definite integrals

The main checked targets, for every valid represented real \(x\), are
\[
\int_0^x\cos^2(\pi t)\,dt=\frac{x}{2}+\frac{\sin(2\pi x)}{4\pi},\qquad
\int_0^x\sin^2(\pi t)\,dt=\frac{x}{2}-\frac{\sin(2\pi x)}{4\pi}.
\]
Negative endpoints have signed orientation. The values at \(x=n/2\), for
\(n\in\mathbb Z\), are corollaries: both integrals equal \(n/4\).
The earlier half-interval symmetry proof and its numerical illustrations
remain as additional explanations of the case \(n=1\).

## Construction and exact statements

`TrigSquareVariable.lean` defines a scaled rectangle computation on every
rational partial chart. Its samples are literal sums of the geometric
cosine square, and `sineSumSample_mem` identifies the complementary sums
with literal sine-square rectangles. `definite_integral` equates this
computation with the separately evaluated endpoint expression. The
internal coordinate is \(u=2t\); its local expression is
\(u/2+\sin(\pi u/2)\cos(\pi u/2)/\pi\).

`TrigSquareGlobal.lean` alternates the cosine and sine charts. The
`cell_quadrature` theorem identifies each local computation with its
rectangle samples; `whole_cell_agreement` justifies compressing complete
cells into a signed multiple of one computed cell. `integralAt` adds the
remaining partial-cell quadrature. The endpoint evaluator is independent
of those sums.

`RationalLipschitzLift.lean` extends these rational-input algorithms to
arbitrary valid represented endpoints using proved uniform bounds and
prefix-intersected rational enclosures. Precision search is executable;
validity supplies its termination proof. `at_rational`, `congr`, and
`representation_equiv` prove agreement with the rational computations,
independence of equivalent implementations, and invariance under a change
of input representation. No real-floor oracle or endpoint chart is an
input to the public theorem.

The main declarations in `TrigSquareGlobal` are:

```lean
cosine_definite_integral (x : RealRaw) (hx : x.Valid) :
  (cosineIntegral x).Equiv (cosineClosedForm x)

sine_definite_integral (x : RealRaw) (hx : x.Valid) :
  (sineIntegral x).Equiv (sineClosedForm x)
```

The closed-form evaluator is the continuous extension of the explicit
geometric formula on rational charts. `closed_form_sample` spells out the
power-reduced formula with the signed doubled-angle sine sample. It does
not silently call a separate global trigonometric library. These are
function-specific integral constructions justified by quadrature, finite
FTC, and endpoint continuity, rather than a new universal integration
class or a conclusion inferred from numerical validity alone.

## Euler route and exponential prerequisite

`ImaginaryExponentialIntegral.lean` proves integration from the two
coordinate equations of \(E'=i\omega E\): the endpoint expressions are
\(I/\omega\) and \(-R/\omega\). `real_integral_equiv` gives an exact
`RealRaw.Equiv` theorem for supplied raw quadratures with proved sample
membership and mesh comparison. The desired integral equality is not a
hypothesis. Zero-derivative constancy and conservation of the squared
coordinate difference prove uniqueness of the supplied exponential ODE.

`TrigSquareEuler.lean` constructs the doubled-angle geometric exponential,
proves its initial value and differential equations, and characterizes it
by uniqueness. This is a differential construction of the imaginary
exponential, not a claimed new identification with a Taylor-series
exponential. `TrigSquareVariable.definite_integral_via_Euler` uses its
integration law and power reduction; the general raw theorems are
`cosine_definite_integral_via_Euler` and
`sine_definite_integral_via_Euler`.

The audit checks independence of the **local value proofs**: the Euler
route does not use the product-rule square model or its integral value.
The global routes share geometric foundations, continuity estimates,
chart assembly, and the represented-input adapter. The earlier symmetry
proof remains independent of FTC for its half-interval evaluation.

## Verified foundation and reproduction

This is a checked extension of the published proof snapshot
`f630241adeae35fc06a5fd4921a4df6396e291d0`. Its closed inverse, trigonometric
identities, and finite-sample calculus are retained at that exact revision.
The new modules are kept together here because the current root library and
the published reader use different source snapshots. They are not assumed
exports of the current root `ComputableAnalysis` import.

From the repository root, choose an empty build directory and run:

```sh
proof_base=$(mktemp -d)
git archive f630241adeae35fc06a5fd4921a4df6396e291d0 | tar -x -C "$proof_base"
cp book/cosine-square/ComputableAnalysis/*.lean "$proof_base/ComputableAnalysis/"
cp book/cosine-square/Check.lean "$proof_base/CosineSquareCheck.lean"
(cd "$proof_base" && lake build ComputableAnalysis.CosineSquareSymmetry ComputableAnalysis.TrigSquareGlobal)
(cd "$proof_base" && lake env lean CosineSquareCheck.lean)
```

`Check.lean` exports theorem types, complete inherited axiom lists, and
three elaborated dependency closures to `cosine-square-reports/proofs.json`.
It fails for unfinished proofs, Mathlib imports, missing proof prerequisites,
or reuse of the product-rule local value proof by the Euler route. The
inherited foundation uses native computation certificates; their axioms
remain visible. New rational constant checks use kernel reduction.

The publication workflow builds and audits this package before replacing the
reader page. It tests both GIFs and paused images, typeset mathematics,
responsive layout, all three route controls, pinned source links, and preservation
of unrelated artifacts. The earlier cosine theorem and its proof map remain
available from `cosine-primitive.html`.

The RMS application is explanatory context. The exported theorem is the
squared-cosine integral, not a new formal signal-processing library.
