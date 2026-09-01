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

Use `InvertibleFunctionOnInterval.source_equiv_of_forward_equiv` for
uniqueness: equivalent forward interval computations imply equivalent source
computations when the separation schedule resolves every positive rational
gap. This is a finite interval theorem, not an appeal to real completeness.

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

### Stieltjes/change of variable

When the natural sampling coordinate is not the public variable, represent the
computation as a finite Stieltjes sum. A substitution theorem is then an
equivalence between two explicit sum algorithms, not an appeal to a general
completed-real change-of-variables theorem.

Expose one evaluated theorem for the resulting integral. Keep FTC or chart
arguments as reusable certificate transports; do not publish a second value
theorem whose only distinction is the proof route used to obtain it.

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
- `DyadicNestedRadicalSquareAnchorCommonWitness` for the normalized anchor;
- `TangentSquareIntegralEffectiveFTCOverlap`.

The public API deliberately has no three-way shared-witness certificate: such
a certificate asks for stronger same-stage data than the proof needs.
The normalized anchor is already valid, and
`TangentSquareIntegralEffectiveFTCOverlap.normalized_equiv_quarter` gives its
value from the tangent-square FTC bridge.  The chain theorem is not a completed
value theorem until these providers are inhabited.  Derive them from the
canonical tangent representation edge rather than reviving finite candidate
searches.

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
