import ComputableAnalysis.RiemannHilbert.BoundaryCauchyAgreement

/-! Genuine boundary-only clients, including the reciprocal with its actual
pole at the excluded center. Complete reciprocal edge data are constructed
for every valid represented center. Reproduction is proved separately when
the actual source is holomorphic on the whole rectangle. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchyExamples
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false

def identityFunction : DomainFunctions.Map := DomainFunctions.affine ⟨zero,ofQComplex_valid _⟩ oneScalar
def identityHolomorphic : Holomorphic identityFunction := DomainFunctions.affine_holomorphic ⟨zero,ofQComplex_valid _⟩ oneScalar

def rectangle (b : Scalar) : QInterval × QInterval := effectiveLocalRectangle identityFunction identityHolomorphic b trivial
theorem center_inside (b : Scalar) : RectanglePoleInterior (rectangle b) b :=
  effectiveLocalRectangle_pole_inside identityFunction identityHolomorphic b trivial

theorem reciprocalDomains (b : Scalar) : RectangleBoundaryDomains (ribbonPoleReciprocal b) (rectangle b) :=
  rectanglePoleReciprocalBoundaryDomains (rectangle b) b (center_inside b)

def reciprocalBound (b : Scalar) : QPos := centeredBoundaryReciprocalBound (effectiveLocalRadius identityFunction identityHolomorphic b trivial)

theorem reciprocalValues (b : Scalar) :
    RectangleBoundaryValueBound (ribbonPoleReciprocal b) (rectangle b) (reciprocalDomains b) (reciprocalBound b) :=
  effectiveLocalRectangle_reciprocal_bound identityFunction identityHolomorphic b trivial (reciprocalDomains b)

def reciprocalDerivativeBound (b : Scalar) : QPos :=
  ⟨2*(reciprocalBound b).val*(reciprocalBound b).val,
    Rat.mul_pos (Rat.mul_pos (by decide +kernel) (reciprocalBound b).property) (reciprocalBound b).property⟩

theorem reciprocalDerivatives (b : Scalar) :
    RectangleBoundaryDerivativeBound (ribbonPoleReciprocal b) (ribbonPoleReciprocal_holomorphic b)
      (rectangle b) (reciprocalDomains b) (reciprocalDerivativeBound b) :=
  ⟨fun z hz => ribbonPoleReciprocal_derivative_bound b z _ _ ((reciprocalValues b).bottom z hz),
    fun z hz => ribbonPoleReciprocal_derivative_bound b z _ _ ((reciprocalValues b).top z hz),
    fun z hz => ribbonPoleReciprocal_derivative_bound b z _ _ ((reciprocalValues b).left z hz),
    fun z hz => ribbonPoleReciprocal_derivative_bound b z _ _ ((reciprocalValues b).right z hz)⟩

def polarData (b : Scalar) : Data where
  source := ribbonPoleReciprocal b
  holomorphic := ribbonPoleReciprocal_holomorphic b
  rectangle := rectangle b
  xOrder := (rectanglePoleInterior_ordered (rectangle b) b (center_inside b)).1
  yOrder := (rectanglePoleInterior_ordered (rectangle b) b (center_inside b)).2
  center := b
  sourceDomains := reciprocalDomains b
  reciprocalDomains := reciprocalDomains b
  valueBound := reciprocalBound b
  derivativeBound := reciprocalDerivativeBound b
  reciprocalBound := reciprocalBound b
  values := reciprocalValues b
  derivatives := reciprocalDerivatives b
  reciprocals := reciprocalValues b

theorem polar_center_excluded (b : Scalar) : ¬(polarData b).source.domain b := by
  intro h
  apply compose_outer_mem h
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((ribbonPoleOffset b).eval b trivial).property) (hright := ofQComplex_valid _)
  change -gridScalarValue b+1*gridScalarValue b=0
  grind only

theorem polar_projection (b z : Scalar) (hz : (BoundaryCauchySeries.function (polarData b)).domain z) :
    (BoundaryCauchySeries.function (polarData b)).eval z hz≈
      moment (BoundaryCauchyNear.data (polarData b) z hz) 0 :=
  BoundaryCauchyReconstruction.projection (polarData b) z hz

def wholeData (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) : Data where
  source := f
  holomorphic := hf
  rectangle := effectiveLocalRectangle f hf b hb
  xOrder := (rectanglePoleInterior_ordered _ b (effectiveLocalRectangle_pole_inside f hf b hb)).1
  yOrder := (rectanglePoleInterior_ordered _ b (effectiveLocalRectangle_pole_inside f hf b hb)).2
  center := b
  sourceDomains := rectangleBoundaryDomains_of_rectangle f _
    (rectanglePoleInterior_ordered _ b (effectiveLocalRectangle_pole_inside f hf b hb)).1
    (rectanglePoleInterior_ordered _ b (effectiveLocalRectangle_pole_inside f hf b hb)).2
    (effectiveLocalRectangle_domain f hf b hb)
  reciprocalDomains := rectanglePoleReciprocalBoundaryDomains _ b (effectiveLocalRectangle_pole_inside f hf b hb)
  valueBound := localHolomorphicValueBound f b hb
  derivativeBound := localHolomorphicDerivativeBound f hf b hb
  reciprocalBound := centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)
  values := effectiveLocalRectangle_value_bound f hf b hb _
  derivatives := effectiveLocalRectangle_derivative_bound f hf b hb _
  reciprocals := effectiveLocalRectangle_reciprocal_bound f hf b hb _

/-- Reproduction needs actual interior source data; boundary-only construction
itself does not. The conclusion compares the actual constructed projection
with the supplied function's actual value. -/
theorem reproduces (d : Data) (hdom : ∀ z, representedRectangleContains d.rectangle z → d.source.domain z)
    (z : Scalar) (hz : (BoundaryCauchySeries.function d).domain z) (hJ : RectanglePoleInterior d.rectangle z) :
    (BoundaryCauchySeries.function d).eval z hz≈d.source.eval z (hdom z (rectanglePoleInterior_mem d.rectangle z hJ)) := by
  apply Setoid.trans (BoundaryCauchyReconstruction.projection d z hz)
  apply converge_unique (momentPrefix (BoundaryCauchyNear.data d z hz) 0) _ _
    (moment_converges (BoundaryCauchyNear.data d z hz) 0)
  apply converge_congr _ _ _ (normalizedFixedRectangleCauchyContour_converges d.source d.holomorphic d.rectangle hdom z hJ)
  intro n
  apply mul_equiv inverseGeometricPeriod.property inverseGeometricPeriod.property
    (fixedRectangleCauchyContour d.source d.rectangle hdom z hJ n).property
    (quadrature (BoundaryCauchyNear.data d z hz) 1 n).property (equiv_refl _ inverseGeometricPeriod.property)
  apply continuousRectangleBoundary_eval_congr (ribbonCauchyKernel d.source z) (ribbonCauchyPowerKernel d.source z 1)
    d.rectangle d.xOrder d.yOrder _ (powerDomains (BoundaryCauchyNear.data d z hz) 1)
  intro w hw he
  exact equiv_symm (ribbonCauchyPowerKernel_one d.source z w he)

theorem whole_center (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    (BoundaryCauchySeries.function (wholeData f hf b hb)).eval b (BoundaryCauchySeries.center_mem _)≈f.eval b hb :=
  reproduces (wholeData f hf b hb) (effectiveLocalRectangle_domain f hf b hb) b (BoundaryCauchySeries.center_mem _)
    (effectiveLocalRectangle_pole_inside f hf b hb)

end ComputableAnalysis.RiemannHilbert.BoundaryCauchyExamples
