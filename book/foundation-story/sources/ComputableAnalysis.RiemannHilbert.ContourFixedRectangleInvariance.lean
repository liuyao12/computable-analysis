import ComputableAnalysis.RiemannHilbert.ContourFixedRectangleNormalized
import ComputableAnalysis.RiemannHilbert.ContourRibbonInvariance

/-! Both the interior geometry and the actual finite fixed-boundary sums
are invariant under replacing a pole by an equivalent valid represented name. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem rectanglePoleInterior_congr (J : QInterval × QInterval) (b c : Scalar) (he : b≈c)
    (hb : RectanglePoleInterior J b) : RectanglePoleInterior J c := by
  obtain ⟨D,hD⟩ := hb
  exact ⟨D,representedRectangle_congr _ b c he hD⟩

theorem fixedRectangleCauchyContour_pole_congr (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b c : Scalar) (he : b≈c)
    (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior J c) (n : Nat) :
    fixedRectangleCauchyContour f J hdom b hb n≈fixedRectangleCauchyContour f J hdom c hc n :=
  continuousRectangleBoundary_eval_congr _ _ J (rectanglePoleInterior_ordered J b hb).1
    (rectanglePoleInterior_ordered J b hb).2 (rectangleCauchyBoundaryDomains f J hdom b hb)
    (rectangleCauchyBoundaryDomains f J hdom c hc)
    (fun z hzb hzc => ribbonCauchyKernel_pole_congr f b c z he hzb hzc) n

theorem normalizedFixedRectangleCauchyContour_pole_congr (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b c : Scalar) (he : b≈c)
    (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior J c) (n : Nat) :
    normalizedFixedRectangleCauchyContour f J hdom b hb n≈normalizedFixedRectangleCauchyContour f J hdom c hc n :=
  mul_equiv inverseGeometricPeriod.property inverseGeometricPeriod.property
    (fixedRectangleCauchyContour f J hdom b hb n).property (fixedRectangleCauchyContour f J hdom c hc n).property
    (equiv_refl _ inverseGeometricPeriod.property) (fixedRectangleCauchyContour_pole_congr f J hdom b c he hb hc n)

theorem fixedRectangleCauchyContour_eval_congr (f g : DomainFunctions.Map) (J : QInterval × QInterval)
    (hf : ∀ z, representedRectangleContains J z → f.domain z)
    (hg : ∀ z, representedRectangleContains J z → g.domain z)
    (he : ∀ z (hfz : f.domain z) (hgz : g.domain z), f.eval z hfz≈g.eval z hgz)
    (b : Scalar) (hb : RectanglePoleInterior J b) (n : Nat) :
    fixedRectangleCauchyContour f J hf b hb n≈fixedRectangleCauchyContour g J hg b hb n := by
  apply continuousRectangleBoundary_eval_congr _ _ J (rectanglePoleInterior_ordered J b hb).1
    (rectanglePoleInterior_ordered J b hb).2
  intro z hzf hzg
  exact mul_equiv (f.eval z hzf.1).property (g.eval z hzg.1).property
    ((ribbonPoleReciprocal b).eval z hzf.2).property ((ribbonPoleReciprocal b).eval z hzg.2).property
    (he z hzf.1 hzg.1) (equiv_refl _ ((ribbonPoleReciprocal b).eval z hzf.2).property)

end ComputableAnalysis.RiemannHilbert.RectangularContour
