import ComputableAnalysis.EnclosureHolomorphic
import ComputableAnalysis.RiemannHilbert.ContourHigherDerivatives
import ComputableAnalysis.RiemannHilbert.ContourFixedCauchy

/-!
# Cauchy and Taylor laws from enclosure holomorphicity

The only analytic hypothesis is the revised enclosure holomorphicity property:
an open domain and shrinking covered boxes for all nearby computed complex
secants. First-derivative continuity, representation invariance and quantitative
derivative estimates are derived by the proved two-way bridge. The existing rectangle-cancellation proof,
constructed contour limits, and geometric kernel remainder then prove the
Cauchy identities and exact local series. No Cauchy, Taylor, or higher-derivative
conclusion is assumed as a field.
-/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy
open ComplexRaw FunctionTheory DomainFunctions RectangularContour RadialLogarithmChains
set_option autoImplicit false

/-- The actual normalized fixed-rectangle Cauchy boundary sums recover every
represented interior point. All of the closed rectangle must stay in the domain. -/
theorem cauchy_formula (f : Map) (h : IsEnclosureHolomorphic f)
    (J : QInterval × QInterval)
    (inside : ∀ z, representedRectangleContains J z → f.domain z)
    (a : Scalar) (ha : RectanglePoleInterior J a) :
    Converges (normalizedFixedRectangleCauchyContour f J inside a ha)
      (f.eval a (inside a (rectanglePoleInterior_mem J a ha))) :=
  normalizedFixedRectangleCauchyContour_converges f h.toHolomorphic J inside a ha

/-- Every justified limit of those same actual boundary computations has the
exact Cauchy value. No identity or integral role is postulated for a candidate. -/
theorem cauchy_limit_identity (f : Map) (h : IsEnclosureHolomorphic f)
    (J : QInterval × QInterval)
    (inside : ∀ z, representedRectangleContains J z → f.domain z)
    (a : Scalar) (ha : RectanglePoleInterior J a) (u : Scalar)
    (limit : Converges (normalizedFixedRectangleCauchyContour f J inside a ha) u) :
    u ≈ f.eval a (inside a (rectanglePoleInterior_mem J a ha)) :=
  normalizedFixedRectangleCauchyContour_limit_identity f h.toHolomorphic J inside a ha u limit

/-- The local square and all edge-bound and precision data are constructed
internally at every represented domain point. -/
noncomputable def localContour (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : Nat → Scalar :=
  normalizedFixedSquareCauchyContour f h.toHolomorphic a ha

theorem local_cauchy_formula (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : Converges (localContour f h a ha) (f.eval a ha) :=
  normalizedFixedSquareCauchyContour_converges f h.toHolomorphic a ha

/-- Actual represented Cauchy coefficient values, from bounded rational
boundary computations with proved convergence. -/
noncomputable def coefficient (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) : Scalar :=
  localCauchyMoment f h.toHolomorphic a ha n

/-- The computed normalized contour value, rather than an unspecified limit,
recovers the original value exactly. -/
theorem constructed_cauchy_formula (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : coefficient f h a ha 0 ≈ f.eval a ha :=
  localCauchyMoment_zero f h.toHolomorphic a ha

theorem coefficient_converges (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) :
    Converges (localCauchyMomentContour f h.toHolomorphic a ha n) (coefficient f h a ha n) :=
  localCauchyMoment_converges f h.toHolomorphic a ha n

theorem coefficient_representation_invariance (f : Map) (h k : IsEnclosureHolomorphic f)
    (a b : Scalar) (ha : f.domain a) (hb : f.domain b) (he : a≈b) (n : Nat) :
    coefficient f h a ha n≈coefficient f k b hb n :=
  localCauchyMoment_congr f h.toHolomorphic k.toHolomorphic a b ha hb he n

/-- An actual summed series on a constructed positive neighborhood. -/
noncomputable def taylor (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : Map := localCauchyTaylor f h.toHolomorphic a ha

noncomputable def taylorRadius (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : QPos := localCauchyTaylorRadius f h.toHolomorphic a ha

/-- The constructed positive Taylor neighborhood contains its center. -/
theorem taylor_center (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : (taylor f h a ha).domain a := by
  refine ⟨0,Rat.le_refl,(taylorRadius f h a ha).property,?_⟩
  exact Small.congr (ofQComplex_valid _) (Centered.offset a a).property
    (equiv_symm (add_neg_equiv a.val a.property)) (Small.zero Rat.le_refl)

theorem taylor_domain (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) (z : Scalar) (hz : (taylor f h a ha).domain z) :
    f.domain z := localCauchyTaylor_domain f h.toHolomorphic a ha z hz

/-- Exact Taylor expansion for arbitrary represented centers and inputs in
its constructed neighborhood; finite estimates alone are not the conclusion. -/
theorem taylor_expansion (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) (z : Scalar) (hz : (taylor f h a ha).domain z) :
    (taylor f h a ha).eval z hz ≈ f.eval z (taylor_domain f h a ha z hz) :=
  localCauchyTaylor_agrees f h.toHolomorphic a ha z hz (taylor_domain f h a ha z hz)

/-- Available numerical error beneath the exact expansion. The radius and
coefficient bound are produced from the supplied function, not caller choices. -/
theorem taylor_prefix_error (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) (z : Scalar)
    (hz : Small (Centered.offset a z).val (taylorRadius f h a ha).val)
    (hza : f.domain z) (N : Nat) :
    Small (sub (f.eval z hza).val (cauchyMomentPrefix f h.toHolomorphic a ha z N).val)
      (16*(localCauchyCoefficientBound f a ha).val*((1:Rat)/8)^N) :=
  localCauchyMomentPrefix_error f h.toHolomorphic a ha z hz hza N

/-- The reconstructed value is independent of holomorphicity witnesses,
center names, and input names wherever the respective local constructions apply. -/
theorem taylor_representation_invariance (f : Map) (h k : IsEnclosureHolomorphic f)
    (a b : Scalar) (ha : f.domain a) (hb : f.domain b) (z w : Scalar)
    (hz : (taylor f h a ha).domain z) (hw : (taylor f k b hb).domain w) (he : z≈w) :
    (taylor f h a ha).eval z hz≈(taylor f k b hb).eval w hw :=
  localCauchyTaylor_value_congr f h.toHolomorphic k.toHolomorphic a b ha hb z w hz hw he

/-- The derivative's holomorphicity is proved from Cauchy reconstruction;
only continuity of the first derivative was required in the original definition. -/
noncomputable def derivativeMap (f : Map) (h : IsEnclosureHolomorphic f) : Map :=
  DomainFunctions.derivativeMap f h.toHolomorphic

theorem derivative_holomorphic (f : Map) (h : IsEnclosureHolomorphic f) :
    IsEnclosureHolomorphic (derivativeMap f h) := h.toHolomorphic.derivative_holomorphic.enclosure

/-- Constructed higher derivative maps retain the entire original domain. -/
noncomputable def higherDerivative (f : Map) (h : IsEnclosureHolomorphic f) (n : Nat) : Map :=
  iteratedDerivativeMap f h.toHolomorphic n

theorem higherDerivative_domain (f : Map) (h : IsEnclosureHolomorphic f) (n : Nat) (z : Scalar) :
    (higherDerivative f h n).domain z ↔ f.domain z :=
  iteratedDerivative_domain f h.toHolomorphic n z

theorem higherDerivative_holomorphic (f : Map) (h : IsEnclosureHolomorphic f) (n : Nat) :
    IsEnclosureHolomorphic (higherDerivative f h n) :=
  (iteratedDerivativeHolomorphic f h.toHolomorphic n).enclosure

/-- These maps are actual successive enclosure derivatives, not formal jets. -/
theorem higherDerivative_successor (f : Map) (h : IsEnclosureHolomorphic f) (n : Nat)
    (a : Scalar) (ha : f.domain a) :
    HasEnclosureDerivativeAt (higherDerivative f h n) a ((higherDerivative_domain f h n a).2 ha)
      ((higherDerivative f h (n+1)).eval a ((higherDerivative_domain f h (n+1) a).2 ha)) :=
  ((iteratedDerivativeHolomorphic f h.toHolomorphic n).atPoint a
    ((higherDerivative_domain f h n a).2 ha)).enclosure.congrDerivative
    (equiv_symm (iteratedDerivative_successor f h.toHolomorphic n a ha))

/-- Taylor coefficients are the factorial-normalized actual higher derivatives. -/
theorem coefficient_derivative_formula (f : Map) (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) (n : Nat) :
    coefficient f h a ha n ≈ scale (factorialRat n)⁻¹
      ((higherDerivative f h n).eval a ((higherDerivative_domain f h n a).2 ha)) :=
  localCauchyMoment_higher_derivative f h.toHolomorphic a ha n

/-- The higher Cauchy formula, on every enclosing rational rectangle. -/
theorem higher_cauchy_formula (f : Map) (h : IsEnclosureHolomorphic f)
    (J : QInterval × QInterval)
    (inside : ∀ z, representedRectangleContains J z → f.domain z)
    (a : Scalar) (ha : RectanglePoleInterior J a) (hfa : f.domain a) (n : Nat) :
    Converges (normalizedFixedRectangleMomentContour f J inside a ha n)
      (scale (factorialRat n)⁻¹ ((higherDerivative f h n).eval a
        ((higherDerivative_domain f h n a).2 hfa))) :=
  normalizedFixedRectangleMomentContour_higher_derivative f h.toHolomorphic J inside a ha hfa n

/-- Continuity of every higher derivative is a derived consequence of its
constructed holomorphic witness. For the first derivative it was required. -/
noncomputable def higherDerivative_continuous (f : Map) (h : IsEnclosureHolomorphic f) (n : Nat) :
    ContinuousOn (higherDerivative f h n).domain (higherDerivative f h n).eval :=
  (iteratedDerivativeHolomorphic f h.toHolomorphic n).continuous

end ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy
