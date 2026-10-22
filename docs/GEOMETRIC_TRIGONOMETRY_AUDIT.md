# Geometric arctangent, inverse search, sine and cosine

Audit date: 2026-10-19. This reviews the current local construction and cold-builds its 52-module proof closure. The downloadable source snapshot and SHA-256 manifest identify the precise inputs; the working tree contains additional work outside this audit.

## Present the computation before its geometric interpretation

The definitions of geometric arctangent and pi are successive rational
updates. Begin with the arctangent interval $[x/(1+x^2),x]$ for
$0\leq x\leq1$. Bisect each current parameter interval; add the explicit
increment to the lower endpoint and subtract the explicit decrement from
the upper endpoint. The input is stage $n$. At $x=1$, multiply both
endpoints by four to obtain the pi computation.

The proof identifies the updates as signed triangle areas in inner chord
and outer tangent fans and proves nested, shrinking bounds. Read the
[computation-first definition and its justification](PI_ARCTAN_COMPUTATION.md).
This exposition update leaves the recorded proof snapshot and its checked
scope unchanged.

## Fixed spatial grids: useful construction, separate specification

A fixed dyadic lattice is a good construction for a cumulative integral. At stage \(n\), use cells \([k2^{-n},(k+1)2^{-n}]\), include the whole cells between the base point and the endpoint, and handle the last partial cell with justified bounds. Stage zero already sums the required integer cells. Refinement splits those cells, without moving the old grid when the endpoint changes.

This helps compare nearby upper limits: common whole-cell contributions cancel, leaving the short intervening segment and endpoint-cell errors. It can make the proof of differentiation much cleaner. It still needs containment, shrinking error, and a local increment estimate. For an integral \(F\) of a continuous function \(f\), a useful target is

\[
\left|\frac{F(x+h)-F(x)}{h}-f(x)\right|\leq \omega_x(|h|)+\eta_n/|h|,
\]

where the justified oscillation bound \(\omega_x\) tends to zero and the stage error \(\eta_n\) is made small relative to \(|h|\). This is a proposed proof shape, not a new theorem claimed by this audit. Domain boundaries, negative orientation and singularities need their own treatment.

**Recommendation:** make this a reusable, justified cumulative-integral constructor. Do not replace every integral or make this the definition of being an integral. Function-specific geometric, series and other constructions should retain their laws and acquire comparison theorems where needed. This agrees with `docs/INTEGRAL_SPECIFICATION.md`.

In the active arctangent chain, `staticDyadicPlan` fixes the number of subdivisions and the precision schedule. It does **not** fix spatial nodes independently of the endpoint. `Calculus.mesh a b n` scales by the interval length. `arctanAreaLoopInitial x` starts with the single interval \([0,x]\); later stages bisect it. Thus its grid is \(kx/2^n\), rather than \(k/2^n\). This finding concerns the audited chain, not every grid module in the repository.

The scheduled arctangent starts deeper: `arctanScheduledStage n = Nat.log2 (32*(n+1)) + 1`. Its external stage zero uses \(64\) cells. The inverse's first midpoint lookup uses precision \(256\), hence internal stage \(14\), or \(16{,}384\) cells. This explains substantial stage-zero work without implying an integer-anchored spatial grid. The audit proves symbolic inequalities; it does not expand those large rational sums numerically.

## The construction actually followed

1. **Geometric area.** `ArctanGeometry.arctanGeom` uses rational geometric bounds for the unit-sector area. Rectangle sums for \(1/(1+u^2)\) are compared with the geometric computation. The scheduled rectangle representation has an exact equivalence theorem with that geometric value.
2. **Order and derivative.** `ArctanSecantFoundation.value` is the scheduled rectangle representation. Its `increment_bounds` gives, for \(0\leq x\leq y\leq1\),
   \[
   (y-x)\frac{1}{1+y^2}\leq A_n^+(y)-A_n^-(x),\qquad
   A_n^-(y)-A_n^+(x)\leq(y-x)\frac{1}{1+x^2}.
   \]
   The module supplies `hasDerivative`, `derivative_valid_and_equiv`, integral bounds and a conditional FTC theorem. Endpoint-scaled subdivisions therefore already support a concrete derivative proof.
3. **Inverse.** `ArctanInverseConstruction` bisects the slope interval \([0,1]\). Separated midpoint and target boxes select a half; overlapping boxes select the middle half using the quantitative separation/error estimates. Its `bracket_target` and `forward_valid_and_target` require target validity, a fast width bound and the correct target range. These are substantive inverse laws.
4. **Circle coordinates.** `ArctanInverseCircle` maps the recovered half-angle slope \(u\) to
   \[
   S(u)=\frac{2u}{1+u^2},\qquad C(u)=\frac{1-u^2}{1+u^2}.
   \]
   On \([0,1]\), sine is increasing and cosine decreasing. The cosine enclosure must reverse the slope endpoints; the code does this.
5. **Clock.** `quarterTarget t` represents \(tA(1)\), the half-angle target. Since \(4A(1)\simeq\pi\), `sineQuarter t` and `cosineQuarter t` are intended at physical angle \(\pi t/2\), for \(0\leq t\leq1\). The first-quadrant public `sinPiRawOfArctan` uses internal coordinate \(2x\), giving physical angle \(\pi x\) on \([0,1/2]\).

## New exact identification check

`ComputableAnalysis/ArctanInverseCircleAudit.lean` adds proofs about the **actual concrete inverse**, without an interface field assuming the desired coordinate identities.

For every rational \(u\in[0,1]\), `inverse_at_geometric_source` proves

\[
\operatorname{inverseExtension}(A(u))\simeq u.
\]

The proof derives order reflection from strict geometric-arctangent separation, then shows every actual inverse bracket contains \(u\). `geometric_chart_check` consequently proves that the computed coordinates at half-angle target \(A(u)\) are exactly \(S(u)\) and \(C(u)\). This is a quantified identity over rational slopes, not a decimal spot check.

`circle_coordinates_at_preimage` also allows any valid, appropriately scheduled target equivalent to \(A(u)\). `quarter_chart_check` applies that law to the existing quarter-turn functions. Its premise equating the target angle with \(A(u)\) remains explicit; it does not assert that every normalized angle has a rational half-angle slope.

Further checks prove:

- Both coordinate computations are valid, and every interval lies in \([0,1]\).
- `quarter_unit_circle`: \(s(t)^2+c(t)^2\simeq1\).
- `quarter_endpoints`: \((s(0),c(0))\simeq(0,1)\) and \((s(1),c(1))\simeq(1,0)\).
- `geometric_pi_clock`: \(4A(1)\simeq\pi\), with the project's geometric area computation of \(\pi\).
- `quarter_angle_normalization`: \(4\operatorname{quarterTarget}(t)\simeq t\pi\), establishing the quarter-turn clock above.

The checker also kernel-checks the rational coordinate example \(u=1/2\), which gives \((S,C)=(4/5,3/5)\).

## Why the circle identity alone is insufficient

`inverseExtension_valid Y` holds for **every** raw target, even an invalid or out-of-range target: its geometrically shrinking slope boxes still define some value. Consequently the coordinate validity, range and unit-circle identity can hold even when the target has no interpretation as an angle in this chart. They establish a point on the circle, not the speed or angle labeling of its traversal.

The inverse law, geometric clock and chart comparisons are what connect that point to its claimed angle. In particular, the elementary `sine theta` and `cosine theta` definitions in this module yield valid first-quadrant coordinates for all rational inputs, but their geometric interpretation requires the half-angle target range. They are not already global periodic sine/cosine merely because their outputs are valid.

## Independent analytic test and remaining bridges

The project already contains a useful independent test in `GeometricCircleODEComparison`: `geometric_rotation_all_rational` compares the rational geometric circle point, at its geometric angle, with the analytic rotation computation for every rational slope. `geometric_sine_powerSeries` and `primary_agreement_on_overlap` supply related comparisons. The route uses actual geometric/analytic error estimates and ODE comparison; it can detect a wrong angular clock that the unit-circle identity misses.

Those source arguments and the function-identity skill's worked comparison were reviewed here. Their separate analytic proof closure was **not** rebuilt in this run. The new cold check covers the concrete inverse-circle closure and the new chart/clock theorems, not that separate module or a newly composed global analytic sine/cosine theorem.

The older `IntegralIdentities.ArctanInverseBisection` requires a geometric branch, range-certified quarter targets, and actual `InverseBisectionSearch` objects. `SinPiIntegral.ArctanSinPiConstruction` consumes such a supplied inverse. These are conditional interfaces; their existence is not a consequence of displaying their field projections. The newer concrete inverse needs a checked adapter/comparison before its correctness can be transferred through those older public interfaces.

Similarly, `HalfIntegralFTCCertificate.ftc` is supplied endpoint-agreement evidence; `halfIntegral_equiv_endpoint` returns that evidence. Its fixed equal-dyadic plan does not itself prove the FTC or identify the integrand.

The next complete function-identification theorem should connect the concrete inverse's forward evaluator with the project's derived arctangent evaluation, establish representation invariance under the required rescheduling, and compose the existing independent rotation comparison. Then extend through justified quadrant, sign and periodicity rules to the public global functions. Such a theorem must cover every valid input in its stated domain; the rational-slope check here must not be advertised as that global result.

## Reproduction and precise validation scope

The proof bundle includes all 52 Lean source modules in this check's import closure, the checker, a Python runner, `lean-toolchain`, and the actual `verification/report.json` and `verification/check.log`. It preserves the exact audited local sources without changing unrelated canonical modules.

With Lean `leanprover/lean4:v4.33.0-rc2` installed, from the extracted bundle:

```sh
python3 scripts/run_arctan_inverse_circle_audit.py --source-root . --build-dir /tmp/arctan-circle-check --lean lean --jobs 2
```

The runner recompiles the entire closure in dependency order with an isolated `LEAN_PATH`; it uses no existing project object files. The successful run built 52 modules and passed the exact checks. All seven audited theorem endpoints report only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. None depends on `sorryAx` or the project's legacy native-decision axioms. The closure imports no Mathlib real or complex numbers.

This is a completed audit and a reproducible first-quadrant identification check. It is not a claim that every historical trigonometric API or every integral in the repository has now been identified.
