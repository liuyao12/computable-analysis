# Formalization Guide

This is the contributor and agent entry point. The project formalizes explicit
rational algorithms and the certificates that make them usable as real or
complex quantities. It does not rebuild ordinary analysis by importing a
completed real line.

## Start here

```lean
import ComputableAnalysis
```

For faster iteration, import the narrowest foundation listed in
[GOALS.md](GOALS.md). The supported calculus build target is:

```sh
lake build ComputableAnalysis.CalculusFoundation
```

Foundation modules are import surfaces, not renaming namespaces. Refer to a
declaration by the name in its subject module; do not add an `effective...`
alias merely because a theorem is re-exported by a broader foundation.

## Infrastructure first; calculations are disposable tests

The permanent deliverable is reusable mathematics and executable constructors,
not a catalogue of completed exercises. Keep specially interesting applications
and their genuine alternative proofs; otherwise formalize a calculation in a
temporary module against a fixed library revision. If it needs a reusable rule,
review that addition separately, then retry with the library fixed. Do not pass a
test by adding the problem's conclusion to a provider record.

After a successful test, discard its proof unless it is deliberately retained
for reproducibility, comparison, or a previous-defect regression. A short record
of the problem, source hash, library hash, compiler result, and dependency audit
records the test; it is not a reproducible proof archive. Small specification
regressions belong in `book/checks/`, never in the native import surfaces.

`book/checks/run_disposable_lean.py` checks named result roots, refuses admitted
proofs and Mathlib dependencies, checks that native source did not change during
the test, and removes the temporary module. Supply `--discard-input` to remove
the original generated file as well. Only the logical axioms `propext`,
`Classical.choice`, and `Quot.sound` are accepted by this runner. This is a tool
for trusted agent-generated tests, not a security sandbox or a proof that a
poorly chosen theorem statement expresses the intended exercise.

## An integral needs meaning as well as numerical validity

`RealRaw.Valid` certifies a number, not its interpretation as an integral. The
legacy `Integral.ConstructionFor F` stores no relation to F; the older
`Integral.Construction` uses F in a left-sum formula but its number-validity
certificate does not by itself require spatial refinement. A permanently coarse
left rule can compute a perfectly valid wrong number. Existing concrete value
proofs retain their stronger evidence and are not invalidated by this observation.

For the supported quantitative dyadic routes, use
`ComputableAnalysis.QuadratureAdapters`. `Quadrature.Certificate f a b value`
keeps validity and selected samples together with a bound against **all tagged
sums** on each fixed dyadic mesh. The spatial bound decreases with mesh size;
evaluation precision is refined after that finite mesh and its tags are fixed.
Different valid representations, selected samples, and schedules are allowed.

The reusable operations are `Certificate.equiv_of_pointwise`, `congr_function`,
`add`, `scale` (including negative coefficients), and `zero_interval`.
`value_of_exact_rule` identifies a separately certified output when a finite
quadrature rule is exact. `ofRationalLipschitz` and `ofMonotoneSamples` certify
existing unit-interval algorithms without changing their numerical instructions.
`Quadrature.ConstructionFor` preserves the semantic evidence for an existing
`FunctionOnInterval`; `toLegacy` is an explicit forgetful adapter, not a converse.

This is a sufficient certificate for particular computations, not a universal
integrability predicate or a claim that every integral has an O(mesh) estimate.
The general certificate accepts ordered rational endpoints. The supplied concrete
adapters currently use the unit interval. General oriented-interval transport,
arbitrary-partition comparisons, the effective-FTC adapter, splitting and
substitution migrations remain separate tasks. Do not replace an existing FTC
constructor by an unrelated new evaluator merely to obtain a new type.

The reusable dyadic mesh and fixed-finite-sample comparison results no longer
import trigonometry. Historical declaration namespaces are retained for source
compatibility; actual owner modules, not names alone, determine dependencies.

## The four layers

1. **Finite evaluator.** At stage `n`, compute a rational interval or complex
   box.
2. **Validity.** Prove ordered boxes, cross-stage nesting, and widths shrinking
   to zero.
3. **Representation edge.** Prove overlap with another implementation at all
   stages.
4. **Abstract object.** Bundle useful implementations and a maintained tree of
   equivalence edges.

Do not put equivalence proofs inside a raw evaluator. When adding an
implementation, connect it to one existing implementation; pairwise edges
against the whole family are unnecessary.

## Real numbers

Use `RealRaw` for one algorithm and `Real` for the abstract represented number.
A valid raw computation proves:

```lean
RealRaw.ValidCompute compute
```

which consists of stage orderedness, cross-stage nesting, and eventual
arbitrary rational precision.

Two valid implementations represent the same number through `RealRaw.Equiv`.
This relation is stagewise overlap. Never compose arbitrary interval overlaps
as though overlap itself were transitive.

### Non-nested candidates

Finite algorithms chosen independently at each precision often shrink without
being nested. Use one of these canonical repairs:

- `RealRaw.prefixStabilize` when the candidate overlaps one valid anchor;
- `RealRaw.overlapChainStabilize` when the available evidence is
  `candidate ↔ bridge ↔ anchor` and the bridge is not itself valid.

The chain construction widens the candidate by the bridge width, which tends
to zero, and then performs prefix stabilization against the valid anchor.

## Functions

Use `FunctionRaw` for one complex-variable computation with its natural
represented domain. Use the abstract function layer to retain alternative
implementations and agreement proofs on intersections of domains.

Do not attempt to classify every acceptable function. Add a special function
when an application needs it, and prove:

1. its domain;
2. validity of its boxes;
3. one useful derivative, integral, ODE, or representation theorem;
4. equivalence to another implementation only when that edge is used.

Routine scalar multiples, sign changes, polynomial combinations, and finite
piecewise definitions should use existing algebra and assembly theorems.

### Applying a continuous computation to a real

For `F : ContinuousFunctionOnInterval`, use:

```lean
F.applyReal x hsource
F.applyReal_equiv hxy hxsource hysource
F.mapImplementation x hsource impl himplSource
```

`applyReal` is the public abstract operation. Underneath it, `applyRealRaw`
searches the stages of the preferred implementation until its interval is
narrow enough, evaluates the rational interval algorithm, and
prefix-stabilizes the image boxes. It does not require an advertised
convergence rate. `applyReal_equiv` is the sole representation-congruence
rule, and `mapImplementation` transports one parent-child edge through the
function. Do not rebuild this argument for named functions or define a public
same-stage composition `evalInterval (x.compute n) ... n`; its validity does
not follow from `x.Valid`.

Inverse branches use the same mechanism through
`InvertibleFunctionOnInterval.forwardRealRaw`; there is no separate
same-stage composition API.

### Inverse branches

Package a regular monotone computation as an
`InvertibleFunctionOnInterval`; do not add a second evaluator merely to change
scale. The canonical arctangent branch is the one-half view of the sector-area
clock in `SectorAreaReparametrization`.

Inverse data should be target-local. For trigonometry, construct the native
scaled-endpoint target with `arctanOnUnitRegularTarget`, prove its geometric
meaning once, and supply a finite search only for those normalized targets.
Do not demand an inverse for every value carrying a nominal endpoint-range
certificate.

Reuse the quantitative rectangle facts in `ArctanGeometry`—in particular
`arctanIntegralRectangleCompute_width_le_sixteenth_input_precision` and
`arctanIntegralRectangleCompute_boxes_strictly_separated`. Do not re-prove
their finite tail estimate in a scaled presentation module.

For a total target-driven search, attach a
`GapAwareTargetWidthCertificate`: it gives a named stage whose target box has
width at most `1 / (16 * (n + 1))`. This cannot be recovered computationally
from `RealRaw.Valid` alone. The canonical quarter-turn target already supplies
`arctanOnUnitRegular_gapAwareTargetWidth`.

Use `InvertibleFunctionOnInterval.source_equiv_of_forward_equiv` for
uniqueness: equivalent forward interval computations imply equivalent source
computations when the separation schedule resolves every positive rational
gap. This is a finite interval theorem, not an appeal to real completeness.
An `InverseBisectionSearch` must provide both its literal finite target
brackets (`value_overlaps`) and the representation edge
`forward_equiv_target`. The former alone can be vacuous when an unscheduled
image box is too wide; the latter certifies the canonical adaptive
application.

When the output precision needed to distinguish two source points depends on
their actual rational gap, use `GapAwareInvertibleFunctionOnInterval` and a
`GapAwareInverseBisectionSearch`. The canonical arctangent branch is exposed
as `arctanOnUnitRegular_gapAwareInvertible`: the denominator of the source
gap selects its separating rectangle stage. Its public result is
`GapAwareInverseBisectionSearch.preimage`, with checked validity,
source-domain containment, and finite forward-image/target overlap. The
corresponding `GapAwareInverseRaw.apply` exposes the same three facts for a
target-local evaluator. This interface intentionally does **not** claim a
`RealRaw.Equiv` edge: add that only after the search has supplied the separate
all-stage argument. The exponential regression searches are examples of this
weaker, already implemented interface.

Do not require a strict left/right comparison at every midpoint. A target box
can genuinely overlap the finite image box of its midpoint. In that case a
total search needs a certified small central source bracket. Its forward-image
overlap is obtained from
`IntervalRegularOn.evalInterval_overlaps_of_point_overlaps`: an interval image
containing the midpoint image still overlaps the target. The separate work is
to prove that the chosen central brackets are nested, shrink, stay in the
source interval, and carry the required forward-equivalence edge.

## Integrating a new function

Choose the first applicable route.

### Monotone rectangles

For a rational interval on which the evaluator is increasing or decreasing,
use endpoint rectangles. Supply interval regularity, monotonicity, and a width
schedule. The Darboux constructors provide a valid integral raw.

### Finitely many turns

Split the interval at certified critical points. Build one monotone integral
per cell and combine them with the finite raw-sum/telescope API. For example,
absolute value is two affine integrals, not a new general integration theory.

### Effective FTC

This is the preferred route when a primitive is known. Construct an
`EffectiveDerivativeBoundFTC` certificate. The main output is:

```lean
h.stabilizedBoundedIntegralRaw endpointValid
```

Use:

```lean
EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw_valid
EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw_equiv_endpointDifference
Integral.effectiveFTCConstructionFor
Integral.effectiveFTCIntegral_equiv_endpointDifference
```

For a public integral, certify `dF.Valid` and its domain on `[a,b]`, then use
`FunctionOnInterval.ofRealFunRaw` and `Integral.effectiveFTCConstructionFor`.
The raw stabilizer remains the internal value computation; clients should
normally expose the resulting `ConstructionFor`.

When an endpoint identity itself must be packaged, use
`Integral.DefiniteIdentityFor`. Pass a certified endpoint computation to the
direct constructor for the relevant FTC certificate. Endpoint-agreement and
stage-schedule conversion lemmas belong in `FTC`; duplicating one adapter for
every certificate subtype is not part of the public integral API.

These theorems do not assume the native finite sums are already nested. The
older `FTC.effectiveFTCStabilizedRaw_valid` route is compatibility API for
existing `EffectiveFTC` clients and is not the preferred foundation.

For algebra on certified integrals, reuse
`Integral.Construction.addOfCommonPlan` and
`Integral.Construction.scaleRat`; their corresponding `integral_*_equiv`
theorems transport the result. Addition requires a shared finite plan, making
the exact rectangle identity explicit instead of hiding a resampling step.

### Stieltjes/change of variable

When the natural sampling coordinate is not the public variable, represent the
computation as a finite Stieltjes sum. A substitution theorem is then an
equivalence between two explicit sum algorithms, not an appeal to a general
completed-real change-of-variables theorem.

Keep one canonical computation and one canonical theorem statement. Distinct
substantive proofs of that statement are welcome under descriptive names
(such as `viaFTC` and `viaInequalities`), with identical hypotheses and
conclusions. Keep the algorithms independent of which proof certifies them.
Audit transitive declaration dependencies to distinguish independent arguments
from aliases; `#print axioms` alone does not establish independence.

The geometric cosine example now has both routes; see
[the two-proof blueprint](blueprint/two-cosine-proofs.md). Exact concavity is
proved geometrically before constructing its secant derivative. The new
`ConcaveFTC` route retains old secants and meshes while refining their finite
samples, so it requires no unproved uniform rate at moving sample points.
Its local FTC estimate retains source interval widths before telescoping.
Use this two-index fixed schedule when only pointwise validity is available;
do not assert that a frozen one-index source schedule converges without a
separate resolution theorem.

## Effective FTC provider checklist

For primitive `F`, derivative `dF`, and rational interval `[a,b]`, provide:

- `F.Valid` and `dF.Valid` on the required domains;
- finite partitions for every stage;
- a derivative interval on every cell;
- containment of the cell endpoint increment in cell width times that box;
- a global width bound by the stage tolerance;
- validity of the canonical endpoint-difference computation.

Then use `Integral.effectiveFTCConstructionFor`. Do not separately prove
nesting for the bounded-sum candidate.

The representative nonlinear regression is
`sineTaylorPrefixThreeSquareEffectiveFTCConstruction_equiv_value`, which
proves the domain-aware integral of `(x-x^3/6)^2` on `[0,1/2]` is
`6389/161280`.

For a genuinely non-polynomial client, copy the shape of
`arctanEffectiveFTCConstruction` and
`arctanEffectiveFTCIntegral_equiv_arctanGeom_one`: the module supplies the
finite derivative certificate and endpoint interpretation, while the generic
effective FTC supplies stabilization and validity.

## The squared-sine transport

The canonical route is a pairwise chain:

```text
public equal-dyadic square sum
        ↕ finite circle/sample overlap
nested-radical square sum
        ↕ common witness
normalized tangent-square anchor
        ↕ endpoint value
1/4
```

Use `dyadicPublicSquareIntegralRaw_chainStabilized`. Its current open provider
instances are:

- `DyadicSquareCircleOverlapFamily`;
- `DyadicNestedRadicalSquareAnchorCommonWitness` for
  `normalizedTangentSquareEffectiveFTCIntegralRaw`.

The public API deliberately has no three-way shared-witness certificate: such
a certificate asks for stronger same-stage data than the proof needs.
The normalized anchor is already valid, and
`normalizedTangentSquareEffectiveFTCIntegralRaw_equiv_quarter` gives its value
directly from the tangent-square effective FTC.  The chain theorem is not a
completed value theorem until the two finite transport providers are
inhabited.  Derive them from the canonical tangent representation edge rather
than reviving finite candidate searches.

For unsquared sine, use
`DyadicHalfAngleTangentEquivalenceFamily`. The nested-radical evaluator already
stabilizes both its explicit half-angle tangent and sine sample into valid
`realRaw` representatives. A provider supplies only the tangent equivalence
edge to the inverse-arctangent computation; `sine_equiv` transports that edge
through the rational circle chart. The algorithms may use different stage
schedules, so do not replace this edge with same-stage containment or add
rational searches and parallel certificate APIs.

## Series

An infinite series belongs in the foundation only when it has:

1. an executable finite prefix;
2. a rational tail interval;
3. a proof that the tail width shrinks;
4. an equivalence or functional identity used downstream.

Finite sum identities alone should remain dependencies or local lemmas. One
representative tail proof should serve routine coefficient variants.

## Fourier analysis

Finite transforms and orthogonality are algebraic prerequisites, not the goal.
A meaningful Fourier theorem must connect finite coefficients and partial
reconstructions with an explicit tail or approximation schedule. Prefer one
nontrivial function class over many finite transform examples.

## Differential equations

The canonical linear route is:

```text
finite sampled recurrence
→ chronological products and Duhamel sums
→ simplex/Peano–Baker terms
→ explicit factorial tail
→ valid represented trajectory
→ uniqueness by a shrinking zero-initial envelope
```

Finite matrix algebra is reused. New work should target the interval simplex
provider and tail/uniqueness bridges, not additional fixed-size matrix demos.

## Wiedijk's list

Only the analysis-relevant 16-item subset is canonical. The registry is
`ComputableAnalysis.wiedijkAnalysisEntries`. Subject modules own the proofs;
the scoreboard never re-exports them under numbered alias names.

## What not to add

- a theorem already available in Lean's finite algebra or combinatorics;
- a second wrapper whose proof is merely `exact existing_theorem`;
- several degree-specific or fixed-stage examples of one pattern;
- a provider structure presented as though an inhabitant had been built;
- a finite check advertised as an unrestricted infinite theorem;
- measure-theoretic or completed-real machinery hidden in an import.

## Documentation rule

The blueprint states the algorithm, invariant, theorem, and current frontier.
Lean carries proof details. Link directly to the canonical declaration. Do not
link compatibility aliases, repeat historical progress logs, or list every
supporting arithmetic lemma.

## Verification

Before committing:

```sh
lake build ComputableAnalysis.CalculusFoundation ComputableAnalysis
rg -n '\b(sorry|admit)\b' ComputableAnalysis
git diff --check
```

For blueprint changes, run the declaration checker and `leanblueprint web`.
After pushing, confirm Lean CI and the Pages deployment rather than assuming a
successful local render is already live.

## Weighted cosine moments and an arithmetic application

`Cartwright.lean` exports `CartwrightMoments.evaluation_viaFinite`,
`evaluation_viaFTC`, `piSquared_viaFinite`, and `piSquared_viaFTC`.
`MathlibComparison.Cartwright` adds the corresponding `viaMathlib` results.
The complete theorem types are checked to agree across each family.

The moment computation itself is in `CartwrightMoments.lean`, with convergence
provided by `MonotoneSampleIntegral` for its explicit uniform sample-error
certificate. Its dyadic mesh/evaluation diagonal is justified quantitatively;
it is not assumed from pointwise validity. Positivity is proved independently
in `CartwrightMomentBounds` before the recurrence is evaluated.

`FiniteSampleCalculus.Model` is a bounded local quadratic-remainder certificate;
its product construction and `chosen_samples_FTC` are reusable for concrete
polynomial/special-function clients with a separately proved mesh comparison.
Do not apply the concave-primitive theorem to a general polynomial product
without a curvature proof. The Cartwright FTC route instead supplies the actual
product/remainder data for its primitive. The direct route uses the separate
`FiniteSummationByParts` identities and remainder accumulation, without calling
that FTC or constructing the composite-primitive model.

Both native routes share local trigonometric bounds and finite algebra. The
Mathlib route independently identifies the same native quadrature with its
interval integral by monotone rectangles, then uses Mathlib FTC/integration by
parts. It does not borrow a native moment recurrence or a ready-made irrationality
theorem. All routes use the same `CartwrightArithmetic` integer contradiction.
The optional exporter `comparison/checks/ExportCartwright.lean` audits these
boundaries and measures actual stored-reference closures, not import lists.

## Reusable integral families after Cartwright

`ComputableAnalysis.IntegralApplications` exports closed Wallis and integer-beta
applications. The optional `MathlibComparison.IntegralApplications` gives proofs
of the identical native propositions, not look-alike real-only identities.

The Wallis computation samples powers of the existing quarter-turn cosine.
Its prescribed mesh/evaluation diagonal has a proved uniform error bound;
monotonicity and sample convergence establish validity before the recurrence.
`Wallis.FactorialStatement` and `Wallis.ProductBoundsStatement` reuse one
arithmetic endpoint recurrence with either the native or Mathlib analytic laws.

The beta computation has exact rational polynomial samples and generally one
turn. `RationalLipschitzIntegral` takes a supplied finite Lipschitz bound, gives
an explicit dyadic radius, and proves prefix-intersection validity. Do not
assert global monotonicity of x^m(1-x)^n. Its factorial and density-normalization
statements are uniformly quantified in both natural parameters. The normalizer
is a rational recurrence, not the reciprocal of the integral evaluator.

The native product/power derivative models use explicit finite remainders;
they do not assume arbitrary composite primitives are convex or concave.
No native integrability predicate or noncomputable numerical choice is added.
Every comparison first proves the actual quadrature corresponds to Mathlib's
integral, without using its proposed evaluation.

Run `checks/ExportIntegralPortfolio.lean` in the comparison package to audit
complete types, actual dependencies, convergence/evaluation separation, and
costs. Count these as two families. The four applications and their internal
recurrences are reusable obligations, not independent successes per parameter.
