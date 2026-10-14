import ComputableAnalysis.RiemannHilbert.ContourFixedRectangleCauchy
import ComputableAnalysis.RiemannHilbert.ContourNormalizedCauchy

/-! Normalize the actual fixed rational boundary using the independently
constructed geometric-period inverse. Supplied limits recover the actual value. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def normalizedFixedRectangleCauchyContour (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (n : Nat) : Scalar :=
  scalarProduct inverseGeometricPeriod (fixedRectangleCauchyContour f J hdom b hb n)

theorem normalizedFixedRectangleCauchyContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) :
    Converges (normalizedFixedRectangleCauchyContour f J hdom b hb)
      (f.eval b (hdom b (rectanglePoleInterior_mem J b hb))) :=
  converge_limit_congr _ _ _
    (converge_product_left inverseGeometricPeriod _ _ (fixedRectangleCauchyContour_converges f hf J hdom b hb))
    (normalizedCauchyValue f b _)

theorem normalizedFixedRectangleCauchyContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (u : Scalar)
    (hu : Converges (normalizedFixedRectangleCauchyContour f J hdom b hb) u) :
    u≈f.eval b (hdom b (rectanglePoleInterior_mem J b hb)) :=
  converge_unique _ _ _ hu (normalizedFixedRectangleCauchyContour_converges f hf J hdom b hb)

theorem normalizedFixedRectangleCauchy_rectangles_agree (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (J K : QInterval × QInterval)
    (hJ : ∀ z, representedRectangleContains J z → f.domain z)
    (hK : ∀ z, representedRectangleContains K z → f.domain z)
    (b c : Scalar) (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior K c) (he : b≈c)
    (u v : Scalar) (hu : Converges (normalizedFixedRectangleCauchyContour f J hJ b hb) u)
    (hv : Converges (normalizedFixedRectangleCauchyContour f K hK c hc) v) : u≈v :=
  Setoid.trans (normalizedFixedRectangleCauchyContour_limit_identity f hf J hJ b hb u hu)
    (Setoid.trans (f.eval_congr b c _ _ he)
      (Setoid.symm (normalizedFixedRectangleCauchyContour_limit_identity f hg K hK c hc v hv)))

theorem normalizedFixedRectangle_centered_limits_agree (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (ha : f.domain b) (u v : Scalar)
    (hu : Converges (normalizedFixedRectangleCauchyContour f J hdom b hb) u)
    (hv : Converges (normalizedLocalCauchyContour f hg b ha) v) : u≈v :=
  Setoid.trans (normalizedFixedRectangleCauchyContour_limit_identity f hf J hdom b hb u hu)
    (Setoid.symm (normalizedLocalCauchyContour_limit_identity f hg b ha v hv))

end ComputableAnalysis.RiemannHilbert.RectangularContour
