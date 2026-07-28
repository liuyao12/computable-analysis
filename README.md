# Computable Analysis

*calculus without the completeness of the real numbers*

This project is about proof-facing computable analysis, not building a
general floating-point or numerical-functions library. Existing numerical
libraries are already the right tool when the goal is fast computation.

The goal here is to express transparent rational interval algorithms in Lean,
prove their validity and equivalence, and package certificates that can be
used inside other mathematics proofs or in science and engineering arguments.
We prefer simple, inspectable constructions and clear proof obligations over
being as fast as possible.

See `GOALS.md` for the current mathematical roadmap and links to the Lean
definitions/proved bridge theorems.

## Linear differential equations

The foundation now has a finite Peano--Baker entry point in
`ComputableAnalysis/PeanoBaker.lean`: rational matrices, sampled linear
systems, and an executable noncommutative ordered-word expansion. The finite
identity between that expansion and the chronological Euler product is proved.
The finite layer also now exposes the general transition
`S_(N-1) * ... * S_0` for a sampled recurrence, proves that it acts exactly
on the homogeneous trajectory, and gives the inhomogeneous trajectory as that
transition of the initial state plus its zero-initial forcing response. It now
also expands that response as the explicit time-ordered Duhamel sum
sum_(k<N) S_(N-1) * ... * S_(k+1) * g_k. It proves finite uniqueness: every candidate sequence satisfying the sampled
recurrence is that trajectory, and a zero-initial homogeneous candidate is
identically zero. This is the exact discrete core of the later constructive
uniqueness proof, not a substitute for its continuous simplex-integral and
factorial-tail estimates.  The scalar factorial-tail estimate is now checked
as well: for a nonnegative norm-length product `C = M*T`, the computable
start `2 * |C.num| + 1` makes every finite omitted prefix of
`sum C^r/r!` at most twice its first term, with an additional factor
`(1/2)^shift` after any further shift.  This is the rational tail certificate
for the eventual Peano--Baker matrix boxes.  Its epsilon modulus is now also
checked: `peanoBakerFactorialTailShift M T eps` is an explicit rational-data
stage after which every finite remaining tail prefix is at most `eps`.
For a constant coefficient, the corresponding degree-`r` ordered-simplex
matrix term is now the checked rational polynomial `T^r/r! * A^r`, with the
recurrence obtained by prepending `A` and multiplying by `T/(r+1)`. This is
the algebraic common core with the exponential series; simplex quadrature and
component interval arithmetic are still separate work.
The familiar forced oscillator is now a checked two-dimensional instance:
its Euler state update gives the exact scalar recurrence
`q_(n+2) - 2 q_(n+1) + q_n = -h^2 omega^2 q_n + h^2 r_n`. This is the
intended bridge from the chapter's second-order introduction to the general
inhomogeneous vector formalism; it makes no claim that the mesh has converged.
Constant Euler increments reduce exactly to `(I + B)^N`, while the zero
coefficient case is the identity. A square-zero sampled coefficient family
reduces exactly to `I + sum B_k`, so the finite word series already covers a
nontrivial nilpotent case. Local matrix associativity and a chronological
product-splitting law are proved; pairwise-commuting increments now commute
with their accumulated finite transition. Its
continuous successor will solve `x' = A(t)x + b(t)` by certified simplex
integrals and factorial tail bounds, beginning with constant, commuting,
scalar, piecewise-constant, and higher-order triangular cases. This broadens
the calculus foundation. The Pi integration suite records which independent
capabilities its checked routes exercise; it intentionally has no completion
fraction for calculus.

The blueprint now makes the intended direction explicit: begin with the
forced second-order oscillator that practitioners recognize, convert it to an
inhomogeneous first-order vector system, construct its general solution by
Peano--Baker plus Duhamel, and prove uniqueness by iterating the zero-initial
Volterra identity until its explicit factorial bound is below any requested
rational tolerance.  The familiar sine/cosine and exponential formulae are
then recovered by that uniqueness theorem, rather than used as definitions.
For the scalar `E' = E`, `E(0) = 1` specialization this identifies the
power-series, repeated-multiplication, and inverse-logarithmic-integral
exponentials once each has its own derivative certificate.  The resulting
canonical positive inverse is the logarithm needed by the deliberately long
arctangent integration-by-parts Pi route.  This is a dependency route for one
coverage benchmark, not a claim that Pi rows measure ODE progress.

## Calculus readiness ledger

The Pi table below is deliberately an integration suite, not the project
score.  It is good at detecting that independently developed finite geometry,
series, integration, and inverse-function bridges agree on one demanding
constant.  It is not a good proxy for the ability to formulate and solve a
new scientific model: several Pi rows can share the same arctangent bridge,
while a major advance such as a continuous Peano--Baker theorem need not move
the Pi count at all.

We therefore use the following gates for the actual calculus goal.  A gate is
marked **checked** only for the stated end-to-end theorem, not merely because
the vocabulary for it exists.  There is intentionally no single percentage:
the gates have different dependencies and none can substitute for another.

| Gate | Current checked boundary | Next boundary |
| --- | --- | --- |
| Rational interval foundation | `RealRaw.Valid`, equivalence by overlap, and the no-completeness/no-Mathlib-analysis audit | Continue dependency auditing as modules grow |
| Continuity and extension | `IntervalRegularOn.epsilonDeltaContinuous` gives literal rational $\varepsilon$--$\delta$ continuity; scheduled `sqrtOnUnit`, the non-exact rectangle arctangent, and the concrete (xarctan x) derivative candidate now have checked finite moduli | Representation-respecting extension needs general closure theorems, beyond the current certified-extension interface |
| Finite integration and FTC | Certified integral constructions, a reusable rational-Lipschitz Darboux constructor, finite geometric integration by parts with increasing/decreasing-piece corner bounds, a partition maximum-step-to-corner-error bridge (including the \(1/n\) unit-mesh coordinate estimate), positive bounded interval products including the concrete unit-branch evaluator \(x\arctan x\), and certificate-to-endpoint FTC bridges are checked; concrete rectangle and compactified Cauchy/quartic integrals run end to end | Extend the constructor from rational Lipschitz kernels to interval-regular functions and derivative certificates for the standard table |
| Monotone inverse functions | Branch-local inverse API and bisection are checked; `sqrt` supplies the concrete unit-interval rational-target example | General represented targets, then sine/arcsine and exponential/logarithm branches |
| Differentiated elementary functions | Formal power-series derivative table, two-sided finite product-error algebra, interval-valued affine/square examples, the rectangle arctangent certificate `d(arctan x)/dx = 1/(1+x*x)`, and the two-sided derivative of its actual product evaluator `d(x*arctan x)/dx = arctan x + x/(1+x*x)` on `[0,1]` are checked | Effective FTC for the concrete derivative, then an analytic certificate that the chosen exponential has derivative itself and the log/exp identities |
| Linear ODEs | Finite Peano--Baker, chronological products, discrete variation of constants, and a factorial-tail majorant with an explicit rational epsilon modulus are checked | Interval-matrix simplex integrals and componentwise boxes yielding continuous variation of constants—the constructive linear Picard--Lindelöf theorem |

The Pi suite remains useful as a secondary release test: add a row only when
it exercises a genuinely new foundation or a new end-to-end bridge.  Do not
inflate it with presentation variants of the same arctangent construction.
The checked registry records its primary coverage family in Lean as
`PiProofs.PiPresentation.integrationFamily`; that makes the shared
dependencies explicit instead of turning the number of presentation variants
into a progress percentage.

## Pi registry coverage suite

`PiProofs.PiCoverageBridge` is a supporting registry, not the public list of
pi formulas.  It has one constructor for each distinct end-to-end bridge, and
its `equivalent` theorem checks both sides as valid `RealRaw` computations and
proves their `RealRaw.Equiv` relation.  Public chapters instead state natural
theorems such as an integral evaluation or the Basel identity; registry
agreement is a derived corollary.  This is evidence for a calculus
capability—not a percentage for the whole foundation.

| Natural theorem family | Checked registry role | Certified width metric |
| --- | --- | --- |
| finite Archimedean theorem | perimeter and area presentations agree | cross-fan: $w_n\le10/(n+1)$ |
| arctangent power-series theorem | geometric and series presentations agree | Leibniz: $w_n=4/(4n+1)$ |
| arctangent integral evaluation | integral and series presentations agree | rectangle $\pi$ raw: $w_n\le16/(n+1)$ |
| Cauchy integral evaluation | full-line integral and area presentations agree | Cauchy $\pi$ raw: $w_n\le16/(n+1)$ |
| reciprocal-quartic integral evaluation | quartic and Cauchy integral presentations agree | dyadic quadrature: $w_n=64/2^n$ |
| Euler identity and complex logarithm (target) | $\exp(i\pi/2)=i$ and $\pi=-2i\log(i)$, tying complex exp/log to the rotation system and ODE uniqueness | Planned: matrix Peano--Baker factorial tail plus represented-input extension modulus |

This deliberately does not measure the primary application gaps: an
exponential raw with `d/dx exp = exp`, reusable derivative/FTC constructions,
or the continuous matrix Peano--Baker theorem would each be major progress
without adding a π equivalence.  Rendered copy:
[front page: π equivalence coverage](https://liuyao12.github.io/computable-analysis/).

The width metric is attached to the named checked $\pi$ raw evaluator, not
automatically transported across an equivalence proof.  The previous dyadic
`224/2^n` Cauchy figure is retained in Lean as the shrinking comparison
envelope for the quartic bridge; it is not the convergence rate of the public
Cauchy raw evaluator.  The table is a useful cost/precision diagnostic for a
construction, rather than a second score for the underlying theorem.

The next intended π registry benchmark is the arctangent
integration-by-parts evaluation, not another arctangent variant.  Its public
statement will be the natural integral formula; its derived presentation
agreement will become a sixth coverage bridge only after the remaining
effective-FTC route, its common monotone-piece refinement, and the
canonical exponential/logarithm alignment are all checked.  This is intentionally the long
elementary-function route: identify `log 2` with the inverse of the canonical
exponential, use linear Peano--Baker/Picard--Lindelöf uniqueness to prove the
exponential representations agree, then use
`pi = 4 * integral_0^1(arctan x) + 2 * log 2`.  The positive bounded product
representation itself is now checked, including the concrete domain-aware
`IntegralIdentities.coordinateTimesArctanIntegralRectangleOnUnit` evaluator:
at every stage it is exactly the two-corner box `[x * A.lo, x * A.hi]`.
The exact rational product-difference identities, including the explicit
`h * D_h x * D_h(arctan)` corner remainder, are now checked as well.
Their three-term absolute-error estimate is checked too: the two component
derivative errors are multiplied by the opposite point value, and the final
budget is exactly `h * |D_h x| * |D_h(arctan)|`.
The exact unit coordinate now also carries an interval-valued derivative
certificate with derivative `1`, obtained from the literal affine
difference-quotient identity.
The exact square now tests the nonzero-error case of the same interface:
its quotient is `2*x + h`, and the signed step is allocated directly to the
requested rational precision.  The product-error theorem now uses `|h|`, so
it applies to the two-sided rational steps required by that interface.
The concrete product now closes the positive-step enclosure: at each rational
unit-branch point, `coordinateTimesArctanIntegralRectangleOnUnit_forwardDerivativeAt`
certifies the forward derivative box `arctan(x) + x/(1+x*x)`. It uses the
actual rectangle box for `arctan(x)`, the arctangent quotient at stage
`8*(n+1)`, and the step budget `h <= 1/(72*(n+1))`; the finite endpoint
identity controls the remaining corner term. The full interval certificate is
now also checked as `coordinateTimesArctanIntegralRectangleOnUnit_hasDerivative`:
negative steps are reversed to a positive quotient at `x+h`, and explicit
rectangle/kernel transport closes with the stricter budget
`|h| <= 1/(648*(n+1))`. The remaining gate is the effective FTC bridge, not
a product derivative.
The resulting derivative candidate is now also proved nondecreasing on the
same branch.  Its rational correction is ordered by the finite identity
`(y-x)*(1-x*y) >= 0` after clearing the two positive denominators, and the
arctangent summand retains its geometric endpoint order.  This yields
endpoint derivative ranges for later positive-cell FTC bounds; it does not
yet give their required secant containment.
The positive product branch is now also proved nondecreasing: for
`0 <= x <= y <= 1`, the literal product endpoints satisfy
`x * A.lo(x) <= y * A.hi(y)`. This supplies the declared monotone direction
for `x * arctan x` in the single-piece integration-by-parts plan, together
with its checked forward derivative; an endpoint FTC identity remains open.
Its endpoint data are now checked too: the product box at `0` is exactly
`[0,0]`, the box at `1` is the geometric rectangle evaluator for
`arctan(1)`, and their endpoint-difference raw is valid and equivalent to
the geometric arctangent value. This supplies boundary data for the finite
rectangle identity, not a product derivative or a fundamental-theorem step.
The first derivative test of this actual product evaluator is now checked
as well: at the zero basepoint, its positive-step quotient is exactly the
arctangent rectangle box, so it has forward derivative `0`. This remains
an endpoint certificate, not the global product derivative needed for
integration by parts.
The uniform-grid core of that
refinement is now formalized: the `m*n` rational grid explicitly contains
both the `m` and `n` grids, and its mesh is the old width divided by the
positive factor.  The two embeddings are packaged as a checked
`CommonRefinement` certificate.  General piecewise synchronization now has a
checked arbitrary-breakpoint insertion primitive: `locateInsertionCell` scans
the finite partition to select and certify an enclosing cell, and
`insertionChainOfPointList` turns any finite in-range rational list into a
composable sequence of those insertions.  The general merge is now checked:
`commonRefinementOfPartitions` inserts one partition's `breakpointList` into
the other and uses a bounded `firstOccurrence` scan to reconstruct the second
monotone index embedding.  It deliberately keeps duplicate breakpoints, so it
is a deterministic certified merge rather than a minimal-union optimization.
The finite upper-endpoint order certificate for rectangle arctangent is now
checked as well: if \(0\le x\le y\le1\), the lower stage box at \(x\) is at
most the upper stage box at \(y\).  It is a separate fact from monotonicity
of the reciprocal kernel and is packaged as a weak nondecreasing
interval-function witness.  The compatible rational sampling path is now
also checked: the cumulative maximum of earlier lower endpoints stays in
each current box by that weak order and is nondecreasing by construction.
The rectangle function itself now has the literal epsilon--delta certificate
`arctanIntegralRectangleOnUnit_epsilonDeltaContinuous`.  At a common stage,
the tangent-chart transport proves `A.lo(x+h) - A.hi(x) <= h`; choosing
`delta = eps` and stage `4 * (eps.den + 1)` then bounds both cross-box gaps
and both widths by `eps` on the whole rational unit branch.  This is finite
continuity data, not a shortcut from differentiability to FTC: cellwise
secant containment and a compatible shrinking partition remain open.
The actual product derivative candidate now has its own literal continuity
certificate as well.  Its rational correction `x/(1+x*x)` is proved
3-Lipschitz by combining the 2-Lipschitz reciprocal kernel with the exact
product difference; allocating `eps/2` to rectangle arctangent and an input
budget `eps/6` to the correction makes the derivative boxes `eps`-near.
It therefore instantiates the unit-mesh corner-error bound without treating
arbitrary adjacent box endpoints as a monotone path.  Its two finite error
knobs are now explicit: mesh `eps.den + 1` makes the corner correction at
most `eps`, while evaluation stage `4 * (eps.den + 1)` makes each selected
sample lie within `eps` of either endpoint of its rectangle box.  The
same concrete samples now also instantiate finite integration by parts:
the two left-endpoint strip sums plus the corner correction equal the final
arctangent sample exactly, and the strip-sum total lies between that endpoint
and the endpoint minus \(1/\mathrm{mesh}\) (or minus the requested
precision under the denominator-plus-one schedule).  This remains a finite
mesh certificate: the remaining arctangent--logarithm route work is the
effective FTC comparison certificate that connects its two strip
sums to the displayed integrals.  The same bracket now produces a valid
supplementary direct raw evaluator: at stage `n` it widens the point interval
at the finite sum `S_(n+1,n)` by `1/(n+1)` and stabilizes the finite prefix
with the verified public radius `4/(n+1)`.  Its candidate width is exactly
`2/(n+1)`, and the stabilized computation is equivalent to the rectangle
arctangent at one; multiplying by four gives a checked pi regression
evaluator.  This does not count as the arctangent--logarithm scoreboard row,
because it does not identify either strip sum with a definite integral or
with `log 2`.
`Logarithm.logTwoSeries` additionally gives a valid alternating-harmonic raw
presentation of `log 2`, with exact stage width `1/(2*n+1)` and hence a
certified `O(1/n)` rate.  Independently,
`Logarithm.logTwoReciprocalIntegral` is now a literal finite
Lipschitz--Darboux integral for the translated reciprocal kernel
`t ↦ 1/(1+t)` on `[0,1]`: its boxes have exact width `2/2^n`.
There is now an exact finite bridge between the two styles of calculation:
for every positive `n`,
`Logarithm.logTwoLo_eq_logTwoKernelRightRiemann` identifies the alternating
lower endpoint with the literal uniform right Riemann sum
`(1/n) * Σ_{k<n} 1/(1+(k+1)/n)`.  The proof first rewrites it as
`H_(2n) - H_n` and then cancels the mesh factor term by term.  Thus it is a
finite rational identity, not an appeal to an integral limit.
The shared `IntegralIdentities.LipschitzDyadic` constructor now proves that a
literal uniform right sum lies inside its matching finite Darboux box.  The
area-loop mesh is proved to be the usual `2^stage` uniform mesh, so
`Logarithm.logTwoDarbouxCompute_contains_dyadicSeriesLower` encloses the
matching alternating-series lower endpoint.  Nestedness and the cofinal rational bound
`k + 1 <= 2^k` then give the checked raw-real theorem
`Logarithm.logTwoSeries_equiv_logTwoReciprocalIntegral`.  This completes the
concrete logarithm-at-two endpoint bridge using only finite rational boxes;
identification with the inverse branch of the selected canonical exponential
remains a separate log/exp theorem.
The next endpoint step is now also finite and explicit.  On the `n`-cell
unit mesh, `Logarithm.logTwoSquareMesh_substitution_identity` proves that the
left Stieltjes sum for `t = x*x` equals the ordinary mesh expression for
`2*x/(1+x*x)` plus a named correction.  The correction is nonnegative and at
most `1/n` (`logTwoSquareMeshCorrection_le_one_div`).  This is the exact
square-substitution algebra needed by the arctangent--logarithm formula.
The pullback `x ↦ 2*x/(1+x*x)` is now certified 2-Lipschitz, and its
Lipschitz--Darboux integral has exact width `4/2^stage`.
`logTwoSquareStieltjesRaw` stabilizes the literal Stieltjes mesh with the
same rational budget and is proved equivalent to that pullback integral.
The finite common-refinement is now checked too: the uniform `n^2` mesh
decomposes into square blocks of `2*k+1` cells, and reciprocal-kernel
monotonicity plus its Lipschitz bound gives an aggregate error at most `4/n`.
Thus `logTwoSquarePullbackIntegral_equiv_reciprocalIntegral` proves the
specialized square substitution
`∫₀¹ 2*x/(1+x*x) dx ≡ ∫₀¹ dt/(1+t)`.  This uses only finite rational
mesh comparisons; identifying the resulting logarithm with the inverse of
the selected canonical exponential remains separate.
The first integration-by-parts strip is now also a direct certified integral:
`Logarithm.arctanLogKernelIntegral` uses the kernel `x/(1+x*x)` and a
Lipschitz constant of `1`.  Natural rational scaling of the finite Darboux
boxes is checked stage by stage, giving
`two_arctanLogKernelIntegral_equiv_logTwoReciprocalIntegral`:
`2 * ∫₀¹ x/(1+x*x) dx ≡ log_rec 2`.  This clears the logarithmic strip of
the arctangent integration-by-parts route. Its direct dyadic evaluation has
the exact width `4/2^stage` (`two_arctanLogKernelIntegral_compute_width`).
The complementary rational strip `(1-x)/(1+x*x)` is now also a literal
3-Lipschitz Darboux integral.
Composing the already independent alternating-series comparison adds the
direct endpoint theorem
`two_arctanLogKernelIntegral_equiv_logTwoSeries`:
`2 * ∫₀¹ x/(1+x*x) dx ≡ log_series 2`.  This is still only an equality of
the certified rational-name computations at two; it does not assume that
either is the inverse of the selected canonical exponential.
`LipschitzDyadic.compute_add` proves that its boxes and the logarithmic-strip
boxes add exactly to the 4-Lipschitz boxes for `1/(1+x*x)`, and common
uniform-left sums prove the resulting raw sum equivalent to the existing
sharper arctangent-kernel integral.  This is a finite rational decomposition,
not yet the claim that the complementary strip is `∫ arctan`: that still
requires the effective FTC identification, followed by
canonical exp/log transport.  The finite triangle part is now a checked,
reusable reindexing theorem:
`uniformTriangleRightSum_eq_complementUniformLeftEndpointSum` proves that an
outer right sum of growing inner left sums is exactly the left sum for
`(1 - x) * f(x)`.  It is the literal finite integration-by-parts rectangle
identity, not a continuous Fubini axiom; relating its inner prefix to
`arctan` is the remaining semantic effective-FTC step.
The direct dyadic specialization is now a valid raw real too:
`arctanKernelTriangleRaw` executes only the finite triangle sums for
`1/(1+x*x)` and carries the public `6/2^n` enclosure radius.  Its stagewise
overlap with `arctanComplementKernelIntegral` is checked, so it is equivalent
to the complementary rational strip without being mislabeled as an integral
of arctangent.  The missing effective FTC theorem remains the sole semantic
step in that identification.
There is now also a complete direct companion computation:
`arctanKernelTrianglePlusLog` adds that triangle raw to the certified
`x/(1+x*x)` logarithmic strip.  The finite two-strip comparison proves it
equivalent to `arctanGeom(1)`.  This is intentionally not the pending
displayed calculus identity `4 * ∫ arctan + 2 * log 2 = pi`: the triangle has
not yet been identified with `∫ arctan`, and the logarithm is not yet the
canonical inverse-exponential one.
The independently checked equality
`2 * arctanLogKernelIntegral ≡ logTwoSeries` now gives a supplementary
executable pi formula too:
`Logarithm.piTriangleLogSeries = 4 * triangle + 2 * log_series(2)`.
Lean proves it equivalent to `4 * arctanGeom(1)`, hence to the preferred
circle-area pi by the existing geometric bridge. It is deliberately excluded
from the Pi coverage count: it is a cross-check of the same arctangent
endpoint, not a substitute for the missing global effective FTC bridge.
The same generic construction now has a checked specialization for the
arctangent kernel `t ↦ 1/(1+t*t)` on `[0,1]`.  Its entirely rational
factorization gives the Lipschitz constant `2`, hence the raw
`IntegralIdentities.arctanKernelLipschitzIntegral` has exact stage width
`4/2^n`.  At every stage its Darboux box and the established geometric
arctangent rectangle box contain the same finite right-endpoint sum; the
resulting checked raw-real equivalence
`arctanKernelLipschitzIntegral_equiv_rectangleForAtOne` is therefore a
comparison of two genuine integration algorithms.  It is deliberately not a
new pi-registry row, and it asserts neither the derivative of arctangent nor
an FTC theorem.
The next derivative-facing finite fact is now checked directly on the
geometric rectangle boxes: for every rational `x >= 0`, their box lies in
`[x - x^3, x]`.  At the zero endpoint the box is exactly `[0,0]`, so every
positive rational difference quotient is enclosed by `[1 - h^2, 1]`.
The new forward finite-difference interface packages this as a checked
one-sided derivative certificate `arctan'(0+) = 1`, evaluated at its exact
stage-zero boxes. The transport to nonzero basepoints is now checked on the
whole unit branch.  The ordinary step `h` corresponds exactly to the chart step
`h / (1 + x * (x + h))`; the chart reaches `x + h`, and its reciprocal scale
differs from `1 / (1 + x*x)` by at most `h`.  The resulting geometric
arctangent addition identity is a finite raw-real equivalence.  Combined with
backward quotient reversal and the rational Lipschitz bound for the kernel,
it proves `arctanIntegralRectangleOnUnit_hasDerivative`: the rectangle
arctangent has the two-sided derivative `1/(1+x*x)` on `[0,1]`.  Its finite
schedule uses derivative stage `8*(n+1)` and signed step budget
`1/(72*(n+1))`; the remaining work is product closure and FTC, not an
arctangent derivative.
The derivative interfaces now make that scheduling obligation expressible:
their evaluation stage depends on the rational basepoint, nonzero step, and
requested output precision.  A stage depending only on output precision would
leave a fixed box width that becomes unbounded after division by arbitrarily
small steps.  Exact affine and quadratic examples use the constant-zero
special case, while arctangent and the eventual exponential certificates will
use genuine step-aware schedules.
The reciprocal kernel itself also has a finite interval-regularity and
epsilon--delta continuity proof on `[1,2]`, using `[1/r, 1/p]` for an input
box `[p,r]`; extending the new Lipschitz construction to that general
interval-regularity interface remains separate work.
The dyadic stages used by existing Riemann
algorithms now have direct point-preservation and mesh-halving theorems as
well.  The finite corner correction now has a checked rational vanishing
schedule on the unit mesh: it is exactly `1/n`, hence at most a requested
positive epsilon at `n = epsilon.den + 1`.

The direct chord-path route now also has a checked
`piCircumferenceStabilized` representative. It evaluates only a finite prefix
of widened chord-path intervals, using the public rational modulus `4/(n+1)`;
the area loop is used only in the proof that this radius is sound. This is a
useful general interval-normalization bridge, but deliberately not a new
coverage bridge: it does not prove the original `piCircumference` endpoints
refine stage by stage.

The direct proof has a sharper checked boundary: the rational curvature chord
certificate is converted to a bisection lower bound with its explicit width
loss, and `AdjacentChordCurvatureMarginCoversFineWidths` states the sole
remaining finite margin inequality.  Its implication to the original local
endpoint-refinement condition is formalized; the universal margin proof is
still open.

The useful output of the completed rows is now formalized as a registry rather
than another percentage. `PiProofs.piCertified : Real` uses `piCircleArea` as
its preferred evaluator and literally retains every currently certified raw
route as an equivalent alternative, including the supplementary
curvature-corrected fan. `PiProofs.PiPresentation` gives the primary routes
stable names, and `PiProofs.piCertifiedPresentation` retrieves a named
`Real.Representation`. This includes the geometry, stabilized circumference,
single Machin, Leibniz, Nilakantha, rectangle, Cauchy, and reciprocal-quartic
routes, together with the two certified perimeter normalizations; it excludes
unproved rows and arbitrary presentation variants. The complementary named
views `PiProofs.pi.curvatureFan`, `PiProofs.pi.integrationByPartsMesh`, and
`PiProofs.pi.triangleLogSeries` do not create additional calculus-coverage
rows. The last two are finite mesh and triangle--logarithm-series evaluators,
not the pending arctangent--logarithm/FTC theorem.

### Full implementation inventory

The following longer table preserves every checked implementation and future
probe.  It is a regression inventory, not the progress board: Machin is the
single power-series formula, while Nilakantha and the normalization variants
are supplementary tests; the direct perimeter, arcsine/Newton, and Gaussian
entries diagnose future calculus gates.  Basel and Brouncker remain
advanced-analysis entries; the Euler/logarithm-at-`i` route is now a named,
unmarked long scoreboard target because it exercises the exp/log/ODE chain.

| Computation | Blueprint | Formula | Def. | Equiv. |
| --- | --- | --- | --- | --- |
| `piCircleArea` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-area-stage-algorithm), [validity](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:geometric-pi-validity) | $a_{n+1}=a_n+\Delta_n,\ b_{n+1}=b_n-\nabla_n,\ \pi\in[4a_n,4b_n]$ | ✓ | N/A |
| `piCircleAreaPolygon` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-area-stage-algorithm), [finite Archimedes bridge](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:finite-archimedes) | rational chord and tangent polygon fans | ✓ | ✓ |
| `piCircumference` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-circumference-stage-algorithm), [comparison](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:finite-archimedes) | $\pi\in[L_n,U_n],\quad U_n-L_n\to0$ | ✗ | ✗ |
| `piCircumferenceFan` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-circumference-stage-algorithm), [finite Archimedes bridge](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:finite-archimedes) | exact inscribed cross-fan lower bound with circumscribed polygonal upper bound | ✓ | ✓ |
| **Arctangent routes** | [geom](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:arctan-area-stage-algorithm), [integral](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:arctan-integral), [series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [area](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:power-series-arctan-area-pi), [Machin](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-machin) | $\pi=4\arctan(1)=4\int_0^1\frac{dt}{1+t^2}=4\sum_{k\ge0}\frac{(-1)^k}{2k+1}$ |  |  |
| `4 * arctanGeom(1)` | [definition](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:arctan-area-stage-algorithm), [equiv](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:geometric-arctan-one-area-pi) | $\pi=4\,\arctan_{\mathrm{geom}}(1)$ | ✓ | ✓ |
| `4 * arctanIntegralRectangleForAtOne` | [rectangles](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:finite-arctan-integral-comparison), [equiv](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:arctan-integral-pi) | $\pi=4\int_0^1 \frac{dt}{1+t^2}$ | ✓ | ✓ |
| `4 * arctanSeries(1)` | [series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [endpoint](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-arctan), [finite Riemann bridge](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:power-series-arctan-area-pi) | $\pi=4\sum_{k\ge0}\frac{(-1)^k}{2k+1}$ | ✓ | ✓ |
| `Logarithm.piTriangleLogSeries` | [finite triangle](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:finite-uniform-triangle-reindexing), [logarithm strip](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:arctan-log-first-strip) | $\pi=4T_{\triangle}+2\log_{\mathrm{series}}2$ | ✓ | ✓ |
| `piNilakantha` | [finite series transformation](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:nilakantha-pi) | $\pi=3+\frac4{2\cdot3\cdot4}-\frac4{4\cdot5\cdot6}+\frac4{6\cdot7\cdot8}-\cdots$ | ✓ | ✓ |
| `piMachin` | [series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [identity](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:machin-tangent), [finite bridge](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-machin) | $\pi=4(4\arctan_{\mathrm{series}}(1/5)-\arctan_{\mathrm{series}}(1/239))$ | ✓ | ✓ |
| `6 * arcsinIntegral(1/2)` | [definition](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:inverse-elementary-integral-identities) | $\pi=6\arcsin(1/2)=6\int_0^{1/2}\frac{dx}{\sqrt{1-x^2}}$ | ✗ | ✗ |
| `NewtonSegmentPi` | [sources](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | $\pi=12(\int_0^{1/2}\sqrt{1-x^2}\,dx-\sqrt3/8)$ | ✗ | ✗ |
| `GaussianPi` | [sources](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | $\pi=\frac12(\int_{-\infty}^{\infty}e^{-x^2/2}\,dx)^2$ | ✗ | ✗ |
| `cauchyFullLineIntegral` | [reciprocal-tail compactification](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:reciprocal-tail-compactification) | $\pi=\int_{-\infty}^{\infty}\frac{dx}{1+x^2}$, represented by a finite reciprocal-tail chart | ✓ | ✓ |
| `piReciprocalQuarticCompact` | [kernel](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:reciprocal-quartic-test-kernel), [route](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:reciprocal-quartic-route-package) | $\pi=\int_{-1}^{1}\frac{1+x^2}{x^4-x^2+1}\,dx$ | ✓ | ✓ |
| `baselSeriesRaw` / `pi^2/6` | [definition](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:zeta-two-raw), [RHS valid](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:basel-geometric-rhs-valid) | $\zeta(2)=\sum_{n\ge1}\frac1{n^2}=\pi^2/6$ | ✓ | ✗ |
| `Brouncker(4/pi)` | [sources](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | $\frac4\pi=1+\cfrac{1^2}{2+\cfrac{3^2}{2+\cfrac{5^2}{2+\cdots}}}$ | ✗ | ✗ |
| **Logarithm-at-i routes** | [overview](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes), [series](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-series-at-i), [path](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-path-integral-at-i), [inverse](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-inv-exp-at-i), [Euler](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | $\exp(i\pi/2)=i,\quad \log(i)=i\pi/2,\quad \pi=-2i\log(i)$ |  |  |
| `-2i * logSeries(i)` | [series](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-series-at-i), [route](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes), [Euler](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | $\pi=-2i\,\log_{\mathrm{series}}(i)$ | ✗ | ✗ |
| `-2i * logPathIntegral(i)` | [path](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-path-integral-at-i), [route](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes) | $\pi=-2i\int_{\gamma:1\to i}\frac{dz}{z}$ | ✗ | ✗ |
| `-2i * logInvExp(i)` | [inverse](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-inv-exp-at-i), [route](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes), [Euler](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | $\pi=-2i\,\log_{\exp^{-1}}(i)$ | ✗ | ✗ |

Lean hooks:

- `piCircleArea`: `PiProofs.AreaLoopValidity.areaValid`,
  `PiProofs.four_arctanGeom_one_equiv_piCircleArea`.
- Unit arctangent: `ArctanGeometry.arctanGeom_valid_on_unit`,
  `ArctanGeometry.arctanGeom_valid_on_powerSeriesDomain`.
- Triangle/logarithm series: `Logarithm.piTriangleLogSeries`,
  `PiProofs.piTriangleLogSeries_equiv_piCircleArea`.  Its triangle and
  logarithm components retain their own public metrics: the triangle
  enclosure radius is $6/2^n$, while the alternating logarithm-series box
  has width at most $1/n$ for positive stage $n$.  This representation is a
  supplementary endpoint cross-check, not the integration-by-parts coverage
  bridge.
- Generic arctangent bridge: `PiProofs.arctanEqualsGeom_finiteRiemannBridge`.
  It supports the series-to-geometry comparison but is not a separate pi-scoreboard route.
- Nilakantha series: `piNilakantha`, `Nilakantha.compute_width_eq`,
  `Nilakantha.valid`, `Nilakantha.equiv_piLeibniz`, and
  `PiProofs.piNilakantha_equiv_piCircleArea`.  This is a direct rational
  series row; its finite summation transform uses the Leibniz endpoints only
  to identify the value, rather than treating it as a second Machin formula.
- Rectangle arctangent:
  `PiProofs.four_arctanIntegralRectangleForAtOne_equiv_piCircleArea`,
  `PiProofs.four_arctanIntegralRectangleMonotoneForAtOne_equiv_piCircleArea`,
  `IntegralIdentities.arctanIntegralRectangleUnitFunctionAgreement`.
- Reciprocal-tail Cauchy integral:
  `IntegralIdentities.ReciprocalTailCompactification`,
  `IntegralIdentities.cauchyFullLineIntegral_valid`,
  `PiProofs.cauchyFullLineIntegral_equiv_piCircleArea`.
- Old point-Riemann arctangent:
  `IntegralIdentities.arctanIntegral_compute_width_zero`,
  `IntegralIdentities.arctanIntegral_stages_constant`.
  This legacy wrapper is kept for conditional FTC bridge statements, but it is
  not a separate scoreboard row because it has no canonical standalone
  refining computation.
- Static dyadic integral API:
  `Integral.staticDyadicSubdivisions`, `Integral.staticDyadicPlan`,
  `Integral.staticDyadicAlgorithm`, `StaticDyadicEffectiveFTC`,
  `FTC.EndpointScheduleAgreement`,
  `FTC.endpointScheduleAgreement_of_effectiveFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_staticDyadicEffectiveFTC_stageSchedule`,
  `FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint`,
  `FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement`,
  `Integral.definiteIdentity_of_staticDyadicEffectiveFTC`,
  `Integral.definiteIdentity_of_staticDyadicEffectiveFTC_endpointAgreement`,
  `PiProofs.piFromArctanIntegral_equiv_piCircleArea_of_staticDyadicEffectiveFTC`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_staticDyadicEffectiveFTC`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_staticDyadicEffectiveFTC_stageSchedule`.
- Constant integral sanity laws:
  `Integral.constantIntegral_add_equiv`,
  `Integral.constantIntegral_scaleRat_equiv`,
  `Integral.constantIntegral_adjacent_additive`.
- Monotone-first integral API:
  `NondecreasingOnInterval`, `NonincreasingOnInterval`,
  `MonotoneOnInterval`, `MonotoneOnInterval.ofNondecreasing`,
  `MonotoneOnInterval.restrict`, `NondecreasingOnInterval.restrict`,
  `NonincreasingOnInterval.restrict`,
  `Integral.NondecreasingConstructionFor`,
  `Integral.NondecreasingConstructionFor.restrict`,
  `Integral.nondecreasingIntegralFor_valid`,
  `Integral.MonotoneConstructionFor`, `Integral.MonotoneConstructionFor.restrict`,
  `Integral.monotoneIntegralFor_valid`,
  `Integral.PiecewiseMonotoneConstructionFor`,
  `Integral.PiecewiseMonotoneConstructionFor.ofMonotone`,
  `Integral.PiecewiseMonotoneConstructionFor.ofNondecreasing`,
  `Integral.piecewiseMonotoneIntegralFor_valid`,
  `Integral.piecewiseMonotoneIntegralFor_ofMonotone_equiv`,
  `Integral.piecewiseMonotoneIntegralFor_ofNondecreasing_equiv`,
  `Integral.GeneralConstructionFor`, `Integral.generalIntegralFor_valid`,
  `Integral.generalIntegralFor_ofMonotone_equiv`,
  `Integral.generalIntegralFor_ofNondecreasing_equiv`,
  `FunctionOnInterval.PointwiseLe`,
  `Integral.LinearFor`,
  `Integral.CompatibleWithScaleRatFor`,
  `Integral.AdditiveOnAdjacentIntervalsFor`, `Integral.OrderPreservingFor`,
  `Integral.BasicPropertiesFor`,
  `Integral.PiecewiseMonotoneLinearFor`,
  `Integral.PiecewiseMonotoneCompatibleWithScaleRatFor`,
  `Integral.PiecewiseMonotoneAdditiveOnAdjacentIntervalsFor`,
  `Integral.PiecewiseMonotoneOrderPreservingFor`,
  `Integral.PiecewiseMonotoneBasicPropertiesFor`,
  `Integral.GeneralOrderPreservingFor`,
  `Integral.GeneralBasicPropertiesFor`,
  `RealRaw.sub_add_sub_cancel_middle_equiv`,
  `RealRaw.scaleRat_valid`, `RealRaw.scaleRat_equiv`,
  `endpointDifferenceRaw_adjacent_additive`,
  `FunctionOnInterval.endpointDifferenceRaw_adjacent_additive`,
  `Integral.DefiniteIdentityFor.integral_add_equiv_of_endpoint_additive`,
  `Integral.MonotoneDefiniteIdentityFor.integral_add_equiv_of_endpoint_additive`,
  `Integral.DefiniteIdentityFor.integral_equiv_add_of_endpoint_add`,
  `Integral.MonotoneDefiniteIdentityFor.integral_equiv_add_of_endpoint_add`,
  `Integral.DefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat`,
  `Integral.MonotoneDefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat`,
  `Integral.DefiniteIdentityFor.integral_le_of_endpoint_le`,
  `Integral.MonotoneDefiniteIdentityFor.integral_le_of_endpoint_le`,
  `Integral.MonotoneDefiniteIdentityFor`,
  `Integral.GeneralDefiniteIdentityFor`,
  `Integral.GeneralDefiniteIdentityFor.toDefiniteIdentityFor`,
  `Integral.GeneralDefiniteIdentityFor.transportConstruction`,
  `Integral.GeneralDefiniteIdentityFor.ofDefiniteIdentityFor`,
  `Integral.GeneralDefiniteIdentityFor.integral_equiv_integral`,
  `Integral.GeneralDefiniteIdentityFor.integral_add_equiv_of_endpoint_additive`,
  `Integral.GeneralDefiniteIdentityFor.integral_equiv_add_of_endpoint_add`,
  `Integral.GeneralDefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat`,
  `Integral.GeneralDefiniteIdentityFor.integral_le_of_endpoint_le`,
  `Integral.GeneralDefiniteIdentityFor.ofMonotone`,
  `IntegralIdentities.arctanKernelIntervalAtOne_monotone`,
  `IntegralIdentities.arctanIntegralRectangleMonotoneForAtOne`,
  `IntegralIdentities.arctanIntegralRectangleMonotoneFunctionAgreement`,
  `IntegralIdentities.arctanGeomUnitRectangleMonotoneDefiniteIdentity`,
  `IntegralIdentities.arctanGeomUnitRectangleGeneralDefiniteIdentity`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_monotoneDefiniteIdentityFor`,
  `PiProofs.piFromArctanGeneralIntegralFor_equiv_piCircleArea_of_generalDefiniteIdentityFor`,
  `PiProofs.piFromArctanGeneralIntegralFor_equiv_piCircleArea_of_definiteIdentityFor_generalConstruction`,
  `PiProofs.piFromArctanGeomUnitRectangleGeneralDefiniteIdentity_equiv_piCircleArea`.
- FTC bridge to domain-aware integral identities:
  `Integral.DefiniteIdentityFor.transportConstruction`,
  `Integral.definiteIdentityFor_of_effectiveFTC`,
  `Integral.definiteIdentityFor_of_effectiveFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_effectiveFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_effectiveFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_staticDyadicEffectiveFTC`,
  `Integral.definiteIdentityFor_of_staticDyadicEffectiveFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_staticDyadicEffectiveFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_staticDyadicEffectiveFTC_stageSchedule`,
  `endpointDifference_valid_of_fun_valid`,
  `FTC.endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_candidateDerivativeFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_curvatureFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_convexFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_concaveFTC_stageSchedule`,
  `derivativeBoundFTC`, `candidateDerivativeFTC`,
  `CurvatureFTCCertificate`, `curvatureFTC`,
  `ConvexFTCCertificate`, `convexFTC`,
  `ConcaveFTCCertificate`, `concaveFTC`,
  `Integral.definiteIdentityFor_of_derivativeBoundFTC`,
  `Integral.definiteIdentityFor_of_derivativeBoundFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_derivativeBoundFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_derivativeBoundFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_candidateDerivativeFTC`,
  `Integral.definiteIdentityFor_of_candidateDerivativeFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_candidateDerivativeFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_candidateDerivativeFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_curvatureFTC`,
  `Integral.definiteIdentityFor_of_curvatureFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_curvatureFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_curvatureFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_convexFTC`,
  `Integral.definiteIdentityFor_of_convexFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_convexFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_convexFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_concaveFTC`,
  `Integral.definiteIdentityFor_of_concaveFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_concaveFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_concaveFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_effectiveFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_candidateDerivativeFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_curvatureFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_convexFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_concaveFTC_stageSchedule`.
Series target:

$$
\forall\,0\le p\le r\le1,\qquad
\frac{r-p}{1+r^2}\le
\int_p^r\sum_{j=0}^{2N}(-1)^jx^{2j}\,dx,\qquad
\int_p^r\sum_{j=0}^{2N+1}(-1)^jx^{2j}\,dx
\le
\frac{r-p}{1+p^2}.
$$

Uniform cell certificates through
$1-x^2+\cdots+x^{20}$,
$1-x^2+\cdots-x^{22}$:
`PiProofs.LeibnizRectangleBridge.evenKernelCellBound_ten`,
`PiProofs.LeibnizRectangleBridge.oddKernelUnitCellBound_eleven`.
Finite unit-cell package through the same prefix:
`PiProofs.LeibnizRectangleBridge.leibnizRectangleUniformUnitCellBoundsAtOneUpToFive`,
with transport to finite cell, kernel, raw-overlap, and scaled-route overlap targets.
Finite stage regression:
`PiProofs.LeibnizRectangleBridge.leibnizRectangleKernelCellBoundsAtOneUpToFifteen`,
`PiProofs.leibnizRectangleRawAtOneOverlapsUpToFifteen`,
`PiProofs.fourArctanSeriesRectangleRouteOverlapsUpToFifteen`.
Unit-cell scaled-route corollary:
`PiProofs.fourArctanSeriesRectangleRouteOverlapsUpToFive_of_unitUniform`.
All finite unit-cell prefixes now feed the full table route through
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_unitUniformCellBoundsUpToAll`
and `PiProofs.leibnizEqArea_of_unitUniformCellBoundsUpToAll`.
The all-prefix conditions are named and reversible for the unit-cell, cell,
kernel, raw-overlap, and scaled-route layers, so future certificates can enter
the proof chain at the most convenient finite expression.
Sharper unit-cell bridge:
`PiProofs.LeibnizRectangleBridge.LeibnizRectanglePointwiseUnitIntegralBridgeAtOne`,
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_pointwiseUnitIntegralBridge`.
Calculus-facing order target:
`Integral.ExactCellOrderPreservation`,
`PiProofs.LeibnizRectangleBridge.KernelPartialExactCellOrderPreservationOnUnit`,
`PiProofs.LeibnizRectangleBridge.unitCellOrderPreservation_of_kernelPartialExactCellOrderPreservation`,
`PiProofs.LeibnizRectangleBridge.LeibnizRectangleUnitCellOrderPreservation`,
`PiProofs.LeibnizRectangleBridge.pointwiseUnitIntegralBridgeAtOne_of_unitCellOrderPreservation`,
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_kernelPartialExactCellOrderPreservation`,
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_unitCellOrderPreservation`,
`PiProofs.leibnizEqArea_of_kernelPartialExactCellOrderPreservation`,
`PiProofs.leibnizEqArea_of_unitCellOrderPreservation`.

A complementary all-degree route now begins with exact rational Riemann
algebra in `Taylor.ArctanKernel`: `powDifferenceFactor` proves the
finite factorization of `r^n-p^n`,
`monomialIntegralBetween_endpoint_bounds` brackets each exact monomial
primitive by its endpoint rectangles, and
`monomialIntegralBetween_endpoint_error_le` bounds either endpoint error by
`k * (r-p)^2` on a unit cell.  This does not yet establish the Leibniz
equivalence; the remaining work is finite alternating-polynomial summation
over the existing dyadic square-mesh budget.

Circumference target:

$$
L_n\le L_{n+1}\le U_{n+1}\le U_n,\qquad U_n-L_n\to0.
$$

Shrinkage: `PiProofs.circumferenceWidthsShrink`.
Comparison target: `PiProofs.CircumferenceQuarterLengthRemainders`.
All finite refinement prefixes now feed validity through
`PiProofs.circumferenceValid_of_quarterLengthStepRefinesUpToAll`.
The finite-prefix and global refinement predicates are linked by
`PiProofs.circumferenceQuarterLengthStepRefines_iff_upToAll` and
`PiProofs.circumferenceStepRefines_iff_upToAll`, with a direct completion
package `PiProofs.CompletionCircumferenceQuarterLengthUpToAllRemainders`.

Reciprocal quartic algebra:

$$
\int_{-\infty}^{\infty}\frac{dx}{x^4-x^2+1}
=
\int_{-\infty}^{\infty}\frac{du}{1+u^2}
=\pi.
$$

Expected-value route:
`PiProofs.reciprocalQuarticMinusOneExpectedPi_equiv_piCircleArea`.
Scoreboard target: `ReciprocalQuarticMinusOneProjectiveRoute`.

When asked for the pi score, reproduce this table and update the counts if the
Lean formalization has moved.

## Blueprint

The rendered blueprint is available at
[liuyao12.github.io/computable-analysis](https://liuyao12.github.io/computable-analysis/).

The LaTeX blueprint lives in `blueprint/`.  It is
organized around the computable-real foundations, the effective FTC, the FTA,
and classical pre-completeness results such as Archimedes' pi, Leibniz/Machin,
Taylor expansions, and Basel.

To build it from the repository root:

```bash
python -m pip install -r blueprint/requirements.txt
leanblueprint web
leanblueprint serve
```

The rendered blueprint is produced by the `Build blueprint pages` workflow.
Pull requests that touch the blueprint run `leanblueprint web` as a render
check.  The public GitHub Pages site is deployed from that same workflow after
a merge or push to the repository default branch, or by manually running the
workflow from the Actions tab.
The generated `blueprint/web` directory is a build artifact and should not be
committed.
