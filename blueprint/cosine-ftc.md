# Checked geometric cosine FTC

## Statement and scope

The theorem is

```lean
ComputableAnalysis.CosineFTC.integral_cosPi_equiv_sinPi_endpoints
```

For `B : IntegralIdentities.ArctanInverseBisection` and rational
`0 <= a <= b <= 1/2`, it identifies two independently executable interval
programs:

\[
 \operatorname{Integral}_{\cos_\pi}(a,b)
 \simeq \operatorname{reciprocalPiRaw}\,
       (\operatorname{sinPiRawOfArctan}(B,b)
        -\operatorname{sinPiRawOfArctan}(B,a)).
\]

This is the project's existing geometric sine/cosine convention, with
rational normalized-angle inputs. The factor `1/pi` must not be dropped.
The factorial/radian sine is not substituted for the geometric sine.

`B` is exactly the data already needed by those public sine and cosine
constructors. The theorem takes no additional derivative, FTC, endpoint
identity, monotonicity, or evaluation-rate assumption. It does not construct
an otherwise missing global inverse provider or extend the chart beyond
`[0,1/2]`.

Equal endpoints are included. The result is `RealRaw.Equiv`, with a separate
proof of `RealRaw.Valid`; it is not definitional equality of output boxes.

## The integral algorithm

Write `L=b-a`. Let `R_(k,q)` be the interval-valued left Riemann sum with
`k+1` equal cells and every cosine sample evaluated at stage `q`. Its formula
is the existing `riemannLeftInterval`, as proved by
`CosineFTC.fixedMesh_compute_eq_riemannLeftInterval`.

Use the explicit, deliberately conservative discretization radius

\[
 E_k = 4000 L^2/(k+1).
\]

At overall stage `n`, output

\[
 I_n = \bigcap_{k=0}^{n}
       \operatorname{expand}(R_{k,n},E_k).
\]

This is finite rational arithmetic with fixed loop bounds. It reads cosine
samples, not sine endpoints; it does not run an error-based precision search.
`CosineFTC.integral_compute` exposes this stage equation literally.
The program is packaged as `Integral.ConstructionFor` for a restriction of
the original `SinPiIntegral.cosPiOnHalf B`.

## Why both indices matter

Pointwise validity of the inverse-based evaluator does not give a uniform
rate over newly introduced sample points. Consequently, merely evaluating
mesh `n` at stage `n` would not justify shrinking widths.

Here every earlier mesh is retained. Given a tolerance, fix a mesh with small
`E_k`; that mesh has only finitely many sample points, so its evaluation
width eventually becomes small. All later outputs are contained in its
expanded enclosure. No uniform rate for a changing mesh is assumed.

The reusable closure proof is `Integral.Dovetail.raw_valid`. It uses all-stage
overlap with one valid endpoint algorithm, not a transitivity assertion about
arbitrary overlapping intervals. The endpoint appears only in the proof,
not in the computation.

## Finite proof

1. Refactor the existing normalized derivative proof to expose its already
   proved uniform step radius `eps/4000` as
   `GeometricSineDerivative.sinPi_derivative_explicit`. The original
   `sinPi'_eq_pi_cosPi` theorem remains available with the same statement.
2. For a fixed mesh width `h`, choose a common sufficiently late evaluation
   stage for its finitely many sample points. The sine increment residual
   is bounded by `4000*h*h` on each cell.
3. Telescope the rational sine increments. Use a single rational selection
   `p` from the pi box and its reciprocal corner to get the cosine-sum
   residual bound. The pi boxes are bounded below by `2`, so division is
   justified without a real-field operation.
4. Use nesting to transport that finite witness back to arbitrary earlier
   sum and endpoint stages. This proves
   `CosineFTC.fixedMesh_overlaps_endpoint` for *every* pair of stages.
5. Intersect the mesh enclosures, prove nesting and arbitrary-precision
   shrinking, and obtain the displayed endpoint equivalence.

## Verification

```sh
lake build ComputableAnalysis
python3 blueprint/checks/check_cosine_ftc.py
```

The checked API is exported by `ComputableAnalysis.IntegralFoundation` and
therefore by the canonical `ComputableAnalysis` import.

The audit checks the first-quadrant theorem, the equal-endpoint case, the
literal runtime equations, and a delayed-evaluation regression showing why
retaining earlier meshes matters. Its transitive axiom report contains no
`sorryAx`. The new modules introduce no `sorry`, `admit`, custom axiom, or
`native_decide` call. They inherit the repository's existing upstream
native-computation axioms, so this is not a claim that the entire dependency
closure has been converted to kernel-only evaluation.

No numerical evaluation with a new concrete `B` is claimed here. The
formal identity is uniform in exactly the inverse data used by the existing
geometric trigonometric programs.
