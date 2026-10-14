import ComputableAnalysis.RiemannHilbert.ContourEffectiveLocalRectangle
import ComputableAnalysis.RiemannHilbert.ContourDerivativeNormalized

/-! Actual fixed-boundary quadratures for every reciprocal power, with
finite pole invariance and agreement with the established first two kernels. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def fixedRectanglePowerContour (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (m n : Nat) : Scalar :=
  continuousRectangleBoundary (ribbonCauchyPowerKernel f b m) J (ribbonCauchyPowerBoundaryDomains f J hdom b hb m) n

theorem fixedRectanglePowerContour_pole_congr (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b c : Scalar)
    (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior J c) (he : b≈c) (m n : Nat) :
    fixedRectanglePowerContour f J hdom b hb m n≈fixedRectanglePowerContour f J hdom c hc m n :=
  let hord := rectanglePoleInterior_ordered J b hb
  continuousRectangleBoundary_eval_congr _ _ J hord.1 hord.2
    (ribbonCauchyPowerBoundaryDomains f J hdom b hb m) (ribbonCauchyPowerBoundaryDomains f J hdom c hc m)
    (fun z hzb hzc => ribbonCauchyPowerKernel_pole_congr f b c z he hzb hzc m) n

theorem fixedRectanglePowerContour_one (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (n : Nat) :
    fixedRectanglePowerContour f J hdom b hb 1 n≈fixedRectangleCauchyContour f J hdom b hb n :=
  let hord := rectanglePoleInterior_ordered J b hb
  continuousRectangleBoundary_eval_congr _ _ J hord.1 hord.2
    (ribbonCauchyPowerBoundaryDomains f J hdom b hb 1) (rectangleCauchyBoundaryDomains f J hdom b hb)
    (fun z hz _ => ribbonCauchyPowerKernel_one f b z hz) n

theorem fixedRectanglePowerContour_two (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (n : Nat) :
    fixedRectanglePowerContour f J hdom b hb 2 n≈fixedRectangleDerivativeContour f J hdom b hb n :=
  let hord := rectanglePoleInterior_ordered J b hb
  continuousRectangleBoundary_eval_congr _ _ J hord.1 hord.2
    (ribbonCauchyPowerBoundaryDomains f J hdom b hb 2) (rectangleDerivativeBoundaryDomains f J hdom b hb)
    (fun z hz _ => ribbonCauchyPowerKernel_two f b z hz) n

theorem fixedRectanglePowerContour_constructed_pole_congr (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b c : Scalar) (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior J c) (he : b≈c)
    (m : Nat) (B C : QPos)
    (hB : RectangleBoundaryDerivativeBound (ribbonCauchyPowerKernel f b m) (ribbonCauchyPowerKernel_holomorphic f hf b m)
      J (ribbonCauchyPowerBoundaryDomains f J hdom b hb m) B)
    (hC : RectangleBoundaryDerivativeBound (ribbonCauchyPowerKernel f c m) (ribbonCauchyPowerKernel_holomorphic f hf c m)
      J (ribbonCauchyPowerBoundaryDomains f J hdom c hc m) C) :
    let hord := rectanglePoleInterior_ordered J b hb
    effectiveRectangleBoundaryValue _ (ribbonCauchyPowerKernel_holomorphic f hf b m) J hord.1 hord.2
      (ribbonCauchyPowerBoundaryDomains f J hdom b hb m) B hB≈
    effectiveRectangleBoundaryValue _ (ribbonCauchyPowerKernel_holomorphic f hf c m) J hord.1 hord.2
      (ribbonCauchyPowerBoundaryDomains f J hdom c hc m) C hC :=
  let hord := rectanglePoleInterior_ordered J b hb
  effectiveRectangleBoundaryValue_eval_congr _ _ (ribbonCauchyPowerKernel_holomorphic f hf b m)
    (ribbonCauchyPowerKernel_holomorphic f hf c m) J hord.1 hord.2 _ _ B C hB hC
    (fun z hzb hzc => ribbonCauchyPowerKernel_pole_congr f b c z he hzb hzc m)

end ComputableAnalysis.RiemannHilbert.RectangularContour
