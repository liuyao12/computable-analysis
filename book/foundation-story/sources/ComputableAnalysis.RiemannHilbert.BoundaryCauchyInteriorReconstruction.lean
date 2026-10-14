import ComputableAnalysis.RiemannHilbert.BoundaryCauchySequenceAgreement

/-! Actual boundary-only moments recover genuine interior source values
when the full rectangle belongs to the holomorphic source domain. This
semantic bridge is derived from the proved rectangular Cauchy theorem. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchyInteriorReconstruction
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false

theorem moment_zero (d : Data)
    (inside : ∀ z, representedRectangleContains d.rectangle z → d.source.domain z)
    (hc : RectanglePoleInterior d.rectangle d.center) :
    moment d 0≈d.source.eval d.center (inside _ (rectanglePoleInterior_mem _ _ hc)) := by
  apply normalizedFixedRectangleCauchyContour_limit_identity d.source d.holomorphic d.rectangle inside d.center hc
  apply converge_congr _ _ _ (moment_converges d 0)
  intro n
  apply mul_equiv inverseGeometricPeriod.property inverseGeometricPeriod.property
    (quadrature d 1 n).property
    (fixedRectangleCauchyContour d.source d.rectangle inside d.center hc n).property
    (Setoid.refl inverseGeometricPeriod)
  apply continuousRectangleBoundary_eval_congr _ _ d.rectangle d.xOrder d.yOrder
  intro w hd he
  exact ribbonCauchyPowerKernel_one d.source d.center w hd

theorem projection (d : Data)
    (inside : ∀ z, representedRectangleContains d.rectangle z → d.source.domain z)
    (z : Scalar) (hz : (BoundaryCauchySeries.function d).domain z)
    (hi : RectanglePoleInterior d.rectangle z) :
    (BoundaryCauchySeries.function d).eval z hz≈d.source.eval z (inside _ (rectanglePoleInterior_mem _ _ hi)) :=
  Setoid.trans (BoundaryCauchyReconstruction.projection d z hz)
    (moment_zero (BoundaryCauchyNear.data d z hz) inside hi)

end ComputableAnalysis.RiemannHilbert.BoundaryCauchyInteriorReconstruction
