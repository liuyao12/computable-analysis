import ComputableAnalysis.RiemannHilbert.ContourDerivativeQuotients

/-! Actual finite first moments are uniformly close to rational pole
quotients of the fixed-boundary Cauchy computations. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

theorem rectanglePoleReciprocalBoundaryDomains (J : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) : RectangleBoundaryDomains (ribbonPoleReciprocal b) J :=
  ribbonOuterDomains _ (selfRectangleRibbon J b hb) (ribbonPoleReciprocal_domain _ b hb)

def rectanglePoleQuotientSample (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (h : QPos) (hc : RectanglePoleInterior J (rationalShift b h))
    (q : QComplex) : Scalar :=
  scale (1/h.val) (gridScalarSub
    (rectangleBoundarySample (ribbonCauchyKernel f (rationalShift b h)) J (rectangleCauchyBoundaryDomains f J hdom _ hc) q)
    (rectangleBoundarySample (ribbonCauchyKernel f b) J (rectangleCauchyBoundaryDomains f J hdom b hb) q))

def fixedRectanglePoleQuotient (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (h : QPos) (hc : RectanglePoleInterior J (rationalShift b h)) (n : Nat) : Scalar :=
  scale (1/h.val) (gridScalarSub (fixedRectangleCauchyContour f J hdom (rationalShift b h) hc n)
    (fixedRectangleCauchyContour f J hdom b hb n))

theorem rectanglePoleQuotientSample_value (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (h : QPos) (hc : RectanglePoleInterior J (rationalShift b h))
    (q : QComplex) (hq : rationalRectangleBoundaryContains J q)
    (ha : (ribbonCauchyKernel f b).domain (rationalRectangleScalar q))
    (hz : (ribbonCauchyKernel f (rationalShift b h)).domain (rationalRectangleScalar q)) :
    rectanglePoleQuotientSample f J hdom b hb h hc q≈ribbonCauchyPoleQuotient f b (rationalRectangleScalar q) h ha hz :=
  scaleRat_equiv (FunctionTheory.sub_congr
    (rectangleBoundarySample_value _ J _ q hq hz) (rectangleBoundarySample_value _ J _ q hq ha))

theorem fixedRectanglePoleQuotient_boundary (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (h : QPos) (hc : RectanglePoleInterior J (rationalShift b h)) (n : Nat) :
    rectangleGridBoundary (rectanglePoleQuotientSample f J hdom b hb h hc) J (2^n)≈
      fixedRectanglePoleQuotient f J hdom b hb h hc n := by
  have ho := rectanglePoleInterior_ordered J b hb
  exact Setoid.trans (b := scale (1/h.val) (gridScalarSub
    (rectangleGridBoundary (rectangleBoundarySample (ribbonCauchyKernel f (rationalShift b h)) J
      (rectangleCauchyBoundaryDomains f J hdom _ hc)) J (2^n))
    (rectangleGridBoundary (rectangleBoundarySample (ribbonCauchyKernel f b) J
      (rectangleCauchyBoundaryDomains f J hdom b hb)) J (2^n))))
    (rectangleGridBoundary_scaled_difference _ _ J (2^n) (1/h.val))
    (scaleRat_equiv (FunctionTheory.sub_congr
      (rectangleBoundarySample_edges _ J ho.1 ho.2 _ n) (rectangleBoundarySample_edges _ J ho.1 ho.2 _ n)))

theorem fixedRectanglePoleQuotient_error (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (h : QPos) (hc : RectanglePoleInterior J (rationalShift b h))
    (F U : Rat) (hF : 0≤F) (hU : 0≤U)
    (hf : ∀ q, rationalRectangleBoundaryContains J q → ∀ hz, Small (f.eval (rationalRectangleScalar q) hz).val F)
    (hu : ∀ q, rationalRectangleBoundaryContains J q → ∀ hz,
      Small ((ribbonPoleReciprocal b).eval (rationalRectangleScalar q) hz).val U)
    (hh : 16*U*h.val≤1) (n : Nat) :
    Small (sub (fixedRectanglePoleQuotient f J hdom b hb h hc n).val
      (fixedRectangleDerivativeContour f J hdom b hb n).val)
      (4*(J.1.width+J.2.width)*(128*F*U*U*U*h.val)) := by
  have ho := rectanglePoleInterior_ordered J b hb
  let s := rectanglePoleQuotientSample f J hdom b hb h hc
  let t := rectangleBoundarySample (ribbonCauchyDerivativeKernel f b) J (rectangleDerivativeBoundaryDomains f J hdom b hb)
  have hE : 0≤128*F*U*U*U*h.val := by
    exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) hF) hU) hU) hU) (Rat.le_of_lt h.property)
  have herr (q : QComplex) (hq : rationalRectangleBoundaryContains J q) : Small (sub (s q).val (t q).val)
      (128*F*U*U*U*h.val) := by
    let a := rectangleBoundaryDomains_rational _ J (rectangleCauchyBoundaryDomains f J hdom b hb) q hq
    let c := rectangleBoundaryDomains_rational _ J (rectangleCauchyBoundaryDomains f J hdom _ hc) q hq
    have hs := ribbonCauchyPoleQuotient_error f b (rationalRectangleScalar q) h a c F U hF hU
      (hf q hq a.1) (hu q hq a.2) hh
    exact Small.congr (sub_valid (ribbonCauchyPoleQuotient f b (rationalRectangleScalar q) h a c).property
      ((ribbonCauchyDerivativeKernel f b).eval _ a).property) (sub_valid (s q).property (t q).property)
      (FunctionTheory.sub_congr (equiv_symm (rectanglePoleQuotientSample_value f J hdom b hb h hc q hq a c))
        (equiv_symm (rectangleBoundarySample_value (ribbonCauchyDerivativeKernel f b) J
          (rectangleDerivativeBoundaryDomains f J hdom b hb) q hq a))) hs
  have hs := rectangleGridBoundary_difference_bound s t J (2^n) ho.1 ho.2 (Nat.two_pow_pos n) _ hE herr
  exact Small.congr (sub_valid (rectangleGridBoundary s J (2^n)).property (rectangleGridBoundary t J (2^n)).property)
    (sub_valid (fixedRectanglePoleQuotient f J hdom b hb h hc n).property
      (fixedRectangleDerivativeContour f J hdom b hb n).property)
    (FunctionTheory.sub_congr (fixedRectanglePoleQuotient_boundary f J hdom b hb h hc n)
      (rectangleBoundarySample_edges (ribbonCauchyDerivativeKernel f b) J ho.1 ho.2
        (rectangleDerivativeBoundaryDomains f J hdom b hb) n)) hs

theorem scaledProduct_difference_right (x y p : Scalar) (r : Rat) :
    scale r (gridScalarSub (scalarProduct x p) (scalarProduct y p))≈
      scalarProduct (scale r (gridScalarSub x y)) p := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scale r (gridScalarSub (scalarProduct x p) (scalarProduct y p))).property)
    (hright := (scalarProduct (scale r (gridScalarSub x y)) p).property)
  let X := gridScalarValue x
  let Y := gridScalarValue y
  let P := gridScalarValue p
  change ComplexRawQuotient.scaleRat r (X*P-Y*P)=ComplexRawQuotient.scaleRat r (X-Y)*P
  rw [←ComplexRawQuotient.scaleRat_mul]
  congr 1
  grind only

theorem fixedRectanglePoleQuotient_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (h : QPos) (hc : RectanglePoleInterior J (rationalShift b h)) :
    Converges (fixedRectanglePoleQuotient f J hdom b hb h hc)
      (scalarProduct (rationalFunctionQuotient f b (hdom _ (rectanglePoleInterior_mem J b hb)) h
        (hdom _ (rectanglePoleInterior_mem J _ hc))) geometricPeriod) :=
  converge_limit_congr _ _ _ (converge_rational_scale (1/h.val) _ _ (converge_difference _ _ _ _
    (fixedRectangleCauchyContour_converges f hf J hdom _ hc)
    (fixedRectangleCauchyContour_converges f hf J hdom b hb)))
    (scaledProduct_difference_right _ _ geometricPeriod (1/h.val))

end ComputableAnalysis.RiemannHilbert.RectangularContour
