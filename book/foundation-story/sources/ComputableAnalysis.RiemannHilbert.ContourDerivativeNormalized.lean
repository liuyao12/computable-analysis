import ComputableAnalysis.RiemannHilbert.ContourDerivativeCauchy
import ComputableAnalysis.RiemannHilbert.ContourFixedRectangleInvariance

/-! Normalization recovers the actual derivative. Both finite first moments
and their supplied limits respect equivalent poles and contour choices. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem normalizedPeriodProduct (d : Scalar) :
    scalarProduct inverseGeometricPeriod (scalarProduct d geometricPeriod)≈d := by
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (scalarProduct inverseGeometricPeriod geometricPeriod).property)
    (hright := oneScalar.property) inverseGeometricPeriod_mul
  change gridScalarValue inverseGeometricPeriod*gridScalarValue geometricPeriod=1 at hp
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct inverseGeometricPeriod (scalarProduct d geometricPeriod)).property)
    (hright := d.property)
  change gridScalarValue inverseGeometricPeriod*(gridScalarValue d*gridScalarValue geometricPeriod)=gridScalarValue d
  grind only

def normalizedFixedRectangleDerivativeContour (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (n : Nat) : Scalar :=
  scalarProduct inverseGeometricPeriod (fixedRectangleDerivativeContour f J hdom b hb n)

theorem normalizedFixedRectangleDerivativeContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) :
    Converges (normalizedFixedRectangleDerivativeContour f J hdom b hb)
      (hf.derivative b (hdom _ (rectanglePoleInterior_mem J b hb))) :=
  converge_limit_congr _ _ _ (converge_product_left inverseGeometricPeriod _ _
    (fixedRectangleDerivativeContour_converges f hf J hdom b hb)) (normalizedPeriodProduct _)

theorem normalizedFixedRectangleDerivativeContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (u : Scalar)
    (hu : Converges (normalizedFixedRectangleDerivativeContour f J hdom b hb) u) :
    u≈hf.derivative b (hdom _ (rectanglePoleInterior_mem J b hb)) :=
  converge_unique _ _ _ hu (normalizedFixedRectangleDerivativeContour_converges f hf J hdom b hb)

theorem ribbonCauchyDerivativeKernel_pole_congr (f : DomainFunctions.Map) (b c z : Scalar) (he : b≈c)
    (hb : (ribbonCauchyDerivativeKernel f b).domain z) (hc : (ribbonCauchyDerivativeKernel f c).domain z) :
    (ribbonCauchyDerivativeKernel f b).eval z hb≈(ribbonCauchyDerivativeKernel f c).eval z hc :=
  mul_equiv ((ribbonCauchyKernel f b).eval z hb).property ((ribbonCauchyKernel f c).eval z hc).property
    ((ribbonPoleReciprocal b).eval z hb.2).property ((ribbonPoleReciprocal c).eval z hc.2).property
    (ribbonCauchyKernel_pole_congr f b c z he hb hc) (ribbonPoleReciprocal_congr b c z he hb.2 hc.2)

theorem fixedRectangleDerivativeContour_pole_congr (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b c : Scalar) (he : b≈c)
    (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior J c) (n : Nat) :
    fixedRectangleDerivativeContour f J hdom b hb n≈fixedRectangleDerivativeContour f J hdom c hc n :=
  continuousRectangleBoundary_eval_congr _ _ J (rectanglePoleInterior_ordered J b hb).1
    (rectanglePoleInterior_ordered J b hb).2 (rectangleDerivativeBoundaryDomains f J hdom b hb)
    (rectangleDerivativeBoundaryDomains f J hdom c hc)
    (fun z hzb hzc => ribbonCauchyDerivativeKernel_pole_congr f b c z he hzb hzc) n

theorem normalizedFixedRectangleDerivativeContour_pole_congr (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b c : Scalar) (he : b≈c)
    (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior J c) (n : Nat) :
    normalizedFixedRectangleDerivativeContour f J hdom b hb n≈normalizedFixedRectangleDerivativeContour f J hdom c hc n :=
  mul_equiv inverseGeometricPeriod.property inverseGeometricPeriod.property
    (fixedRectangleDerivativeContour f J hdom b hb n).property (fixedRectangleDerivativeContour f J hdom c hc n).property
    (equiv_refl _ inverseGeometricPeriod.property) (fixedRectangleDerivativeContour_pole_congr f J hdom b c he hb hc n)

theorem normalizedFixedRectangleDerivative_rectangles_agree (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (J K : QInterval × QInterval)
    (hJ : ∀ z, representedRectangleContains J z → f.domain z)
    (hK : ∀ z, representedRectangleContains K z → f.domain z)
    (b c : Scalar) (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior K c) (he : b≈c)
    (u v : Scalar) (hu : Converges (normalizedFixedRectangleDerivativeContour f J hJ b hb) u)
    (hv : Converges (normalizedFixedRectangleDerivativeContour f K hK c hc) v) : u≈v :=
  Setoid.trans (normalizedFixedRectangleDerivativeContour_limit_identity f hf J hJ b hb u hu)
    (Setoid.trans (hf.derivative_congr b c _ _ he)
      (Setoid.trans (hf.derivative_unique hg c _) (Setoid.symm
        (normalizedFixedRectangleDerivativeContour_limit_identity f hg K hK c hc v hv))))

end ComputableAnalysis.RiemannHilbert.RectangularContour
