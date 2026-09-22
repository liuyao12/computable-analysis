# Leibniz's geometric transmutation, reconstructed finitely

This is a modern finite reconstruction of Leibniz's method, not a transcription
of a single original proof. Horváth distinguishes the early proof using moments
from the general transmutation argument developed after 1674. Both pass from
the circle to a rational curve and then quadrature powers. We reconstruct the
transmutation version, with exact rational identities replacing infinitesimals.

Sources: Miklós Horváth, [On the Leibnizian quadrature of the circle](https://ac.inf.elte.hu/Vol_004_1983/doi/075_04.pdf)
(1983), especially printed pp. 78–81; Ranjan Roy,
[The Discovery of the Series Formula for π by Leibniz, Gregory and Nilakantha](https://doi.org/10.1080/0025570X.1990.11977541)
(1990), pp. 291–306. Historical priority and a verbatim formalization of Leibniz's
manuscripts are not claimed.

## The geometry

Use the unit circle with centre (1,0). Its upper-left quadrant has rational
coordinates

    X(t) = 2t²/(1+t²),  Y(t) = 2t/(1+t²),  0 ≤ t ≤ 1.

They satisfy (X−1)²+Y²=1. The tangent's intercept on the vertical axis is t:
its equation is (X−1)(x−X)+Y(y−Y)=0, and Yt=X. At t=0 the tangent is vertical;
this endpoint formula does not assert a unique intercept.

For an arbitrary finite chain, trapezoid areas satisfy

    2 Σ trapezoid = endpoint rectangle difference + Σ intercept moment.

For a straight segment y=mx+z, its intercept moment is z Δx. This is the
finite geometric content of transmutation. Complementation of the rectangle
interchanges the two coordinates. In conventional integral notation, the two
identities become

    2∫ y dx = xy + ∫ t dx,     ∫ t dx + ∫ x dt = xt.

At the circle's endpoint (1,1), complementation gives the quarter-circle area

    A(1) = 1 − ½ J,    J = ∫₀¹ X(t) dt.

Here the integral notation describes our rational rectangle computations; it
does not introduce a completed real line or a new π.

## Exact finite replacement

For each rational cell 0 ≤ p ≤ r, put

    T(p,r) = (r−p)(X(p)+X(r))/2,
    E(p,r) = (r−p)³ / (2(1+p²)(1+r²)).

The existing geometric sector lower increment equals exactly

    (r−p) − T(p,r)/2 − E(p,r).

For the dyadic mesh with 2ⁿ cells this gives an all-stage identity

    geometricLower(n) = 1 − ½ ΣT − ΣE,
    0 ≤ ΣE ≤ ½·4⁻ⁿ.

The cell identity also places each geometric increment between the two
complemented endpoint rectangles. This proves overlap with the existing
geometric area computation at every stage. Validity includes nesting and
shrinking widths; the transformed integral has width at most 8/(n+1).

## From the rational curve to the series

Finite geometric division gives

    X(t) = 2(1 − Σ[k=0..N] (−1)ᵏt²ᵏ)
           − 2(−1)ᴺ⁺¹t²ᴺ⁺²/(1+t²).

Quadrature of powers and the alternating remainder bound then give

    J = 2(1/3 − 1/5 + 1/7 − ⋯),
    A(1) = 1 − 1/3 + 1/5 − ⋯,    π = 4A(1).

The implementation transports the existing all-degree polynomial quadrature
through the exact identity 1−X(t)/2=1/(1+t²). It does not duplicate that
infrastructure. Thus the new geometric bridge has a distinct dependency path,
while power integration is shared with the Taylor/FTC proof. This is not a
claim of a wholly independent third native analysis library.

## Checked interface

New modules:

- `ComputableAnalysis/FiniteTransmutation.lean`: reusable finite trapezoid,
  intercept-moment and complement identities, including finite chains.
- `ComputableAnalysis/LeibnizTransmutation.lean`: rational circle, exact cell
  correction, transformed-area computations, convergence and series comparison.

Main declarations (in `ComputableAnalysis.LeibnizTransmutation` unless stated):

- `circle_equation`, `tangent_intercept`, `tangent_support`
- `sector_cell_transmutation`, `geometric_polygon_transmutation`
- `transmutation_error_bound`
- `transmutedIntegralRaw_valid`, `transmutedIntegralRaw_width`
- `areaRaw_equiv_geom`, `circle_transmutation`, `transmuted_integral_series`
- `transformed_curve_expansion`
- `ComputableAnalysis.pi_eq_leibniz_transmutation : piCircleArea.Equiv leibnizRaw`

The final theorem retains the canonical π and the existing Leibniz computation.
Its project declaration closure has 861 entries at this revision, including
private helper declarations and type dependencies. `scripts/check_leibniz_transmutation.lean`
checks that finite transmutation and polynomial quadrature actually occur and
that neither the old mesh comparison nor the old rectangle/geometry bridge
occurs. It separately checks the geometric bridge has no calculus certificates.
The audit exports the entire closure, checks `sorryAx` is absent, and reports
inherited axioms. Existing arithmetic proofs use `native_decide`; this work
adds no new such uses and does not claim the inherited trusted basis vanished.
No Mathlib import or new `noncomputable` definition is introduced.

Mathematical outline:

    circle and tangent intercept → finite transmutation → geometric area
                  rational curve → power quadrature     ↗
                                      ↓
                             alternating series → π = Leibniz

The public reader uses the cosine primitive's graph interaction pattern.
The Mathlib branch remains an analogous theorem in a different foundation;
no formal representation bridge to it is claimed by this comparison.
