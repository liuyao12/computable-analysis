# From arctangent to the residue theorem

PNT+ is a useful **external formal reference**, not a dependency of this
project. The audited reference snapshot is
[`a5154676af9aa3095150ee410cdda80555aa0642`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/a5154676af9aa3095150ee410cdda80555aa0642).
Its source is Apache-2.0 licensed. This addition links and explains the
upstream argument; it does not copy Mathlib declarations into our foundation.

## What PNT+ actually checks

In `PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean`:

| Declaration | Mathematical role | Foundation |
| --- | --- | --- |
| `HolomorphicOn.vanishesOnRectangle` | A holomorphic regular part contributes zero | Mathlib rectangle Cauchy theorem |
| `integral_const_div_sq_add_sq` | Integrate `y/(x²+y²)` using arctangent | Mathlib real interval integral |
| `ResidueTheoremAtOrigin'` | Integral of `c/z` around a rectangle containing zero is `2πic` | Arctangent identities and cancellation of logarithms |
| `ResidueTheoremInRectangle` | Translate the pole to any interior point | Rectangle translation and normalization |
| `ResidueTheoremOnRectangleWithSimplePole` | Remove a supplied simple principal part | Regular-part vanishing and pole normalization |
| `RectangleIntegral'_eq_sumResiduesIn` | Sum residues at a finite set of simple poles | Meromorphic normal forms, regular-part removal and linearity |

The last theorem assumes **simple poles** and no boundary poles. It is not
an arbitrary-order residue theorem. More general statements in
`GeneralMeromorphic.lean` are commented out and are not counted as checked.

The explicit Cauchy derivative formula is in
`PrimeNumberTheoremAnd/StrongPNT.lean`, declaration `cauchy_formula_deriv`.
It invokes Mathlib's circle-integral derivative formula directly. It does
**not** have the rectangle/arctangent dependency path. The value formula
below is a mathematical consequence of the simple-pole theorem, not a
claim that PNT+ exports a separate rectangle formula declaration by that name.

## Rectangle-first contour interface

For this route, rational rectangles suffice as contour primitives. Parameterize
each oriented side from a to b by `z(t)=a+t(b-a)` on `[0,1]`, and integrate
the two real components of `G(t)=F(z(t))*(b-a)`. The orientation and side
length belong to this pullback, not to an after-the-fact sign convention.

A useful initial class supplies a finite partition on which each component
of G is monotone, computable endpoint value boxes, and rational range bounds.
For a monotone piece of length L, range width V, maximum mesh δ and endpoint
box widths at most η, the Darboux gap is at most `δ*V+2*L*η`. Finite assembly
adds the budgets. Start with supplied rational breakpoints; for an irrational
turn, use shrinking rational brackets and a range bound on the remaining
central cell. Reuse `FinitePiecewiseRectangles`,
`Integral.PiecewiseMonotoneConstructionFor` in `Calculus`, and
`TurningPointIntegral`; do not postulate a universal integral.

For the rational pole kernel, the horizontal-side components reduce (up to
constant factors) to `x/(x²+y²)` and `y/(x²+y²)` with fixed nonzero rational y.
Their monotonicity splits are explicitly `x=±|y|` and `x=0`; vertical sides
are analogous. Thus the class fits the arctangent normalization directly.

Permit finite sums of certified integrals so regular-part subtraction does
not require automatically discovering a new monotonicity partition for a
sum. Products and new quotients still need their own enclosure certificates.

Separate **integrability certificates on the four sides** from **complex
analyticity certificates in the region away from supplied poles**. The first
constructs the integral; the second proves Cauchy and residue identities.
For example, the side pullbacks of `conj(z)` have affine real and imaginary
components, but its counterclockwise rectangle integral is `2i*area`, not
zero. Piecewise monotonicity alone cannot prove a Cauchy theorem.

This is the selected design direction, not a claim that a generic rectangle
adapter is already formalized. The existing polygonal interfaces are retained.

## The native arctangent normalization

Reuse the existing rational square contour work in
`ComputableAnalysis/PDE/CauchyContour.lean`. Its only imports are `CauchyPi`
and `HolomorphicJet`; the latter supplies finite rational-complex inverse
algebra. No exponential, reciprocal calculus or PDE construction is needed.
The canonical π remains `piCircleArea`.

Split the counterclockwise boundary of `[-1,1]²` into eight half-edges.
For the right side, write `z=1+iu`, so

```
(1/z) dz = (u+i)/(1+u²) du.
```

Pair the upper and lower halves, then rotate through the four sides.
The odd real contributions cancel before taking any limit:

```
sum of the eight oriented pullbacks = 8i/(1+u²),  0 ≤ u ≤ 1.
```

The literal rational rectangle boxes bracket every tagged sum on the
specified partition. The partitions cover `[0,1]`, and their imaginary
width is at most `16/2^n`. Thus the constructed `ComplexRaw` is valid and
is equivalent to `8i A(1) = 2πi`. Translation and nonzero rational dilation
leave the pole pullback unchanged. A negative real dilation rotates the
square by a half turn and still preserves orientation.

Checked declarations in `ComputableAnalysis.PDE.CauchyContour`:

- `square_endpoints`, `point_avoids_pole`, `scaledPullback_eq`;
- `density_exact`, `stage_partition_covers`;
- `raw_encloses_taggedSum`, `raw_encloses_stageSum`;
- `raw_valid`, `raw_height_geometric`, `raw_equiv_twoPiI`;
- `twoPiI_not_equiv_zero`.

This promotes the existing workspace's square normalization with a narrower
import and an elementary inverse-order proof. It does not replace its
existing downstream Cauchy, reciprocal or PDE modules.

## How residues give the Cauchy value formula

For a rectangle Ω and an interior point p, write

```
f(z) = g(z) + a/(z-p).
```

Once contour vanishing for the regular part and contour transport of the
normalized pole are available, finite linearity gives

```
∮∂Ω f(z) dz = 2πi a.
```

For a holomorphic F, the required decomposition is

```
F(z)/(z-p) = [F(z)-F(p)]/(z-p) + F(p)/(z-p).
```

Extend the divided difference across p using a certified local series
chart. Its constant term is F′(p), and its remaining coefficients are the
shifted coefficients of F. It is therefore the regular part. The result is

```
∮∂Ω F(z)/(z-p) dz = 2πi F(p).
```

This multiplication form avoids inserting a reciprocal computation into
the public statement. Division by `2πi` requires a separate certified
nonzero reciprocal; the native normalization already supplies separation.

## Remaining native obligations

Only the square-pole normalization above is included as a checked native
result in this publication. The general residue and Cauchy formulas are
external checked references plus a native construction plan. In particular,
we do not assume either formula as a field in a certificate.

The full native adaptation needs these concrete bridges:

1. Local chart or uniform affine-remainder certificates for the regular
   part; finite subdivision cancels interior edges. On a unit square with
   N² cells, a quadratic remainder bound `M/N²` gives total contour error
   at most `4M/N`, hence an explicit vanishing schedule.
2. A finite rectangle-with-holes subdivision, with a positive rational
   distance from every pole, relating the actual outer and inner contour
   computations. A finite identity alone is not yet that convergence bridge.
3. Computable regular-part subtraction, a certified extension of each
   divided difference, and contour linearity for the constructed integrals.
4. For higher-order principal parts, the remaining negative powers have
   explicit primitives; their closed contour integrals need their own FTC
   bridges. PNT+'s checked finite simple-pole theorem does not supply this.

The original workspace has further finite-grid and sampled-contour work;
this publication does not claim it as a completed general theorem or ship
unrelated unfinished modules.

## Dependency outline

```
Native checked                         PNT+ / Mathlib checked
rational inverse + oriented sides      log/arctan primitives on sides
             ↓                                      ↓
8i/(1+u²), all-tag enclosure            rectangle integral of a/(z-p)
             ↓                                      ↓
valid boxes + geometric π              + regular-part Cauchy theorem
             ↓                                      ↓
square integral of 1/z = 2πi            simple-pole residue theorem
                                                    ↓
                                       finite sum of simple residues
                                                    ⇢
                                       Cauchy value formula (derivation)

PNT+ cauchy_formula_deriv ← Mathlib circle-integral derivative theorem
```

The arrow to the value formula records the displayed mathematical
derivation, not an extracted declaration dependency or a checked native
formula. The two foundations share an argument, not Lean imports.

## Verification

Run `lake build ComputableAnalysis ComputableAnalysis.Blueprint`,
`lake exe checkdecls blueprint/lean_decls`, and
`lake env lean scripts/check_cauchy_arctan.lean`. The last command audits
axioms, rejects Mathlib imports and `sorryAx`, checks the geometric and
finite-enclosure dependencies, exports their combined project closure, and
executes the first four rational stages. It does not certify upstream's
build; the PNT+ entries are a pinned-source review.
