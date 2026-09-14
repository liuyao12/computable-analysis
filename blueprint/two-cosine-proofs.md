# Two checked proofs of the geometric cosine integral

## One computation, one statement, two proofs

For the existing inverse provider `B : IntegralIdentities.ArctanInverseBisection`
and rational endpoints `0 <= a <= b <= 1/2`, the following two declarations
have definitionally identical theorem types, including every hypothesis:

```lean
ComputableAnalysis.CosineFTC.integral_cosPi_viaInequalities
ComputableAnalysis.CosineFTC.integral_cosPi_viaFTC
```

Their common statement is `CosineFTC.IntegralCosineStatement B a b ha hb hab`:

```lean
(CosineFTC.integral B a b ha hb hab).Equiv
  (RealRaw.mul SinPiIntegral.reciprocalPiRaw
    (SinPiIntegral.sinPiRawOfArctan B b hb -
      SinPiIntegral.sinPiRawOfArctan B a ha))
```

These are the existing geometric sine and cosine, not factorial-series
substitutes. Their rational argument is normalized: write them informally
as `S(x)=sin(pi*x)` and `C(x)=cos(pi*x)`. Thus the endpoint formula is
`(S(b)-S(a))/pi`. The normalization factor is retained as an explicit
computable reciprocal, not treated as a rational constant.

The computation and proposition live in `CosineIntegralData.lean`, which
imports neither proof module. The old theorem name
`integral_cosPi_equiv_sinPi_endpoints` remains a compatibility alias to the
direct proof. Both substantive proofs are exported by `IntegralFoundation`.

`B` is the data already needed to define the existing geometric functions.
Neither final theorem adds a concavity, derivative, FTC, monotonicity,
uniform evaluation-rate, or endpoint-equivalence hypothesis. Equal endpoints
are covered. This work does not construct a new default provider `B`, extend
the trigonometric chart beyond `[0,1/2]`, or assert a numerical evaluation with
an otherwise missing concrete provider.

## The unchanged integral program

Set `L=b-a`. Let `R_(k,q)` be the interval-valued left Riemann sum using
`k+1` equal cells, with every original cosine sample evaluated at stage `q`.
`fixedMesh_compute_eq_riemannLeftInterval` proves literal equality to the
repository's existing finite rectangle computation.

At stage `n`, the integral returns

\[
 I_n=\bigcap_{k=0}^{n}\operatorname{expand}
       \left(R_{k,n},\frac{4000L^2}{k+1}\right).
\]

It evaluates only cosine and finite rational arithmetic. The endpoint
program is separate. All loop bounds are fixed by `n`; this integral adds
no accuracy-driven stopping search to the existing sample evaluator.
The constant 4000 is deliberately conservative, not a quadrature optimization.

Retaining older meshes is essential under pointwise sample convergence.
One first fixes a mesh with small discretization error; its finite collection
of samples then converges. Evaluating only the newly introduced mesh at its
matching stage would assume an unjustified uniform evaluation rate.

## First route: direct finite inequalities

`GeometricSineFiniteBounds.lean` contains rational circle and clock residual
inequalities. `GeometricSineDirectBounds.positive_increment_error` uses them
to prove the finite local bound without invoking a derivative theorem.

For a fixed positive rational increment `h` and sufficiently late stage `n`,
all rational selections `u,v,c,p` from the two sine boxes, the cosine box,
and the pi box satisfy

\[
 |u-v-hpc|\le4000h^2.
\]

The proof chooses only proof-side common stages. It does not modify the
runtime computation. It uses the finite geometric error estimates with
`eta=h^2/64`, rather than obtaining this result as a corollary of
`sinPi_derivative_explicit`.

For any fixed finite mesh, its finitely many bounds have a common stage.
The rational sine selections telescope. A single shared pi selection and
its reciprocal corner convert the residual to an error for the cosine sum.
Nesting then transports the result to arbitrary earlier sum and endpoint
stages. Finite intersections give the stated `RealRaw.Equiv` and a separate
validity theorem.

`CosineFTC.lean` imports neither the concavity proof nor the general concave
FTC. The direct proof does not depend on either normalized sine derivative
theorem, even transitively through a theorem body or definition.

## Concavity established from geometry

The missing geometric theorem is now checked:

```lean
GeometricSineConcavity.sine_concave B :
  ExactConcaveOn (CosineFTC.sineFun B) 0 (1/2)
```

`ExactConcaveOn` is the project's cross-stage rational endpoint order,
not a claim about unspecified completed real values.

For rational circle slopes `0 <= u <= v <= 1`, put
`t=(v-u)/(1+u*v)`. Finite rational identities compare the circle chord
increment with its two tangent slopes. Together with the arctangent clock
bounds `t/(1+t*t) <= arctan(t) <= t`, these give supporting-secant inequalities.
The arbitrary rational slack from finite clock/source boxes is removed by
validity and nesting, yielding all-stage order inequalities.

In represented-number notation, for rational `x<y` on the chart,

\[
 \pi C(y)\preceq\frac{S(y)-S(x)}{y-x}\preceq\pi C(x).
\]

The same argument gives supporting slopes `C` for `P=S/pi`. The three-point
secant inequality then proves exact concavity of both `S` and `P`.
No first or second derivative theorem is used to establish concavity.

## The actual concavity-based derivative program

For an interior rational `x`, set `r=min(x,1/2-x)>0` and `h_k=r/(k+1)`.
At evaluation stage `q`, form the outward secant bracket

\[
 B_{k,q}(x)=\left[
   \left(\frac{S(x+h_k)-S(x)}{h_k}\right)_q^-,
   \left(\frac{S(x)-S(x-h_k)}{h_k}\right)_q^+
 \right].
\]

The derivative at stage `n` is the finite intersection of `B_(k,n)(x)` for
`k<=n`. Its computation reads sine only. Concavity proves compatibility
between every pair of these brackets, at every pair of evaluation stages.
The supporting-slope bounds, pointwise validity, and an explicit Lipschitz
estimate prove shrinking widths. The checked conclusions include:

```lean
GeometricSineConcavity.sineDerivative_valid
GeometricSineConcavity.sineDerivative_equiv_pi_cosine
```

This is a **two-index fixed schedule**: older secants are reevaluated at the
current output stage. It is not a claim that every one-index schedule that
freezes each source evaluation at `sigma(k)` converges. No uniform bound on
the evaluation rate of arbitrary `B` was supplied, so such a claim would be
unjustified. Both loop bounds here are predetermined; there is no
error-dependent search. This two-index construction is a reusable extension
of the blueprint's frozen-stage secant construction.

The two-sided derivative is constructed for `0<x<1/2`. Supporting-secant
certificates cover the closed chart, so integration includes 0 and 1/2
without pretending to have two-sided derivatives outside the domain.

## Second route: the general concave FTC

`ConcaveSecantFTC.lean` packages exact concavity, a valid slope computation,
the cross-stage supporting-secant bounds, and a natural-number Lipschitz
bound as `ConcaveFTC.DerivativeData`. It proves validity and equivalence for
the literal concavity-based derivative above.

`ConcaveFTCIntegral.lean` proves a general FTC for such data. Its premises
contain no integral overlap or endpoint identity. In particular, source-box
widths are not silently canceled in a telescoping argument.

For a cell of length `h`, after the primitive and derivative boxes at its
endpoints have width at most `tau`, the finite residual bound is

\[
 |F_n^-(y)-F_n^-(x)-hD_n^-(x)|
       \le K h^2+(1+h)\tau.
\]

For a fixed `m`-cell mesh, choose `tau=eps/(m(1+h))` and a common stage for
the finitely many samples. Telescope the rational lower selections, remove
arbitrary positive rational slack, and prove overlap of every expanded
finite sum with every endpoint box. The two-index closure then proves the
integral valid and equivalent to primitive endpoints.

The geometric client instantiates this theorem with the already proved
concavity and derivative data for `P=S/pi` and `D=C`, using the conservative
Lipschitz constant 32. The existing error allowance 4000 is larger, so the
very same integral algorithm is covered. A finite distributivity argument
identifies `P(b)-P(a)` with `reciprocalPiRaw*(S(b)-S(a))` independently of the
direct proof.

This is an extension of the existing FTC infrastructure, not a fabricated
inhabitant of the older same-stage-containment provider. That provider asks
for stronger scheduling/containment data than pointwise convergence gives.
The new general theorem explicitly handles cross-stage secants and finite
sample convergence. Existing FTC declarations remain available.

## Proof independence and verification

Run:

```sh
lake build ComputableAnalysis
python3 blueprint/checks/check_cosine_ftc.py
python3 blueprint/checks/check_two_cosine_proofs.py
```

`TwoCosineProofsAudit.lean` compares the complete theorem types using Lean's
`Meta.isDefEq`. It traverses stored bodies and types transitively and verifies
that neither proof calls the other, the direct route avoids derivative/FTC
results, and the FTC route genuinely uses the concavity instance and generic
local FTC estimate rather than the direct geometric residual theorem.
It also verifies that constructed derivative validity uses exact concavity
and cross-stage secant compatibility.

The tests cover both endpoint formulas, equal endpoints, concavity, an
interior derivative, and the literal unchanged integral stage equation.
The earlier delayed-evaluation regression remains checked as well.

Local checks used Lean 4.33.0-rc2, rebuilt all changed proof modules and their
affected public-import clients through `ComputableAnalysis`, and ran both
audits using the already compiled unchanged project dependencies. This is
not a claim of a fresh cold rebuild of every upstream module.

Both final proofs and the concavity/derivative theorems have no transitive
`sorryAx` dependencies. New production proof modules introduce no custom
axioms, admitted proofs, or `native_decide` calls. The dependency closures
still include the repository's existing native-computation axioms and the
standard Lean axioms reported by the audit. In the local audit, the direct
proof has 106 axiom dependencies and the FTC proof has 92; these counts are
not proof-size or mathematical-strength measures.

## Multiple proofs are intentional

The canonical object is the computation and the canonical theorem type, not
a single mandatory proof term. Distinct substantive proofs may be retained
under descriptive names and checked for identical hypotheses and conclusions.
Logical proof irrelevance does not remove their distinct dependency graphs.
An alias that merely invokes another theorem is a compatibility wrapper,
not an independently verified second argument.
