import ComputableAnalysis.RiemannHilbert.BoundaryCauchyReconstruction
import ComputableAnalysis.RiemannHilbert.CenteredSeriesFactorization

/-! Boundary constructions preserve represented values and hide quantitative
choices. Actual source-value comparison, a common rectangle and equivalent
center names imply agreement of moments, projections and their derivatives.
The comparisons are proved from quadratures and series, not record fields. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchyAgreement
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false
variable (d e : Data)

theorem kernel_agreement (hp : d.center≈e.center)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (w : Scalar) (hd : (ribbonCauchyKernel d.source d.center).domain w)
    (he : (ribbonCauchyKernel e.source e.center).domain w) (k : Nat) :
    (ribbonCauchyPowerKernel d.source d.center k).eval w hd≈
      (ribbonCauchyPowerKernel e.source e.center k).eval w he := by
  induction k with
  | zero => exact hf w hd.1 he.1
  | succ k ih =>
    exact mul_equiv (ribbonCauchyPowerValue d.source d.center w hd k).property
      (ribbonCauchyPowerValue e.source e.center w he k).property
      ((ribbonPoleReciprocal d.center).eval w hd.2).property ((ribbonPoleReciprocal e.center).eval w he.2).property
      ih (ribbonPoleReciprocal_congr d.center e.center w hp hd.2 he.2)

theorem rectangle_transport (f : DomainFunctions.Map) (J K : QInterval × QInterval) (h : J=K)
    (hd : RectangleBoundaryDomains f J) (he : RectangleBoundaryDomains f K) (n : Nat) :
    continuousRectangleBoundary f J hd n≈continuousRectangleBoundary f K he n := by
  cases h
  exact equiv_refl _ (continuousRectangleBoundary f J hd n).property

theorem quadrature_agreement (hJ : d.rectangle=e.rectangle) (hp : d.center≈e.center)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (k n : Nat) : quadrature d k n≈quadrature e k n := by
  unfold quadrature
  let hg : RectangleBoundaryDomains (ribbonCauchyPowerKernel e.source e.center k) d.rectangle := hJ.symm ▸ powerDomains e k
  exact Setoid.trans (continuousRectangleBoundary_eval_congr (ribbonCauchyPowerKernel d.source d.center k)
    (ribbonCauchyPowerKernel e.source e.center k) d.rectangle d.xOrder d.yOrder (powerDomains d k) hg
    (fun w hd he => kernel_agreement d e hp hf w hd he k) n)
    (rectangle_transport _ _ _ hJ hg (powerDomains e k) n)

theorem value_agreement (hJ : d.rectangle=e.rectangle) (hp : d.center≈e.center)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (k : Nat) : value d k≈value e k :=
  converge_unique _ _ _ (converges d k) (converge_congr _ _ _ (converges e k)
    (fun n => equiv_symm (quadrature_agreement d e hJ hp hf k n)))

theorem moment_agreement (hJ : d.rectangle=e.rectangle) (hp : d.center≈e.center)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (k : Nat) : moment d k≈moment e k :=
  mul_equiv inverseGeometricPeriod.property inverseGeometricPeriod.property (value d (k+1)).property (value e (k+1)).property
    (equiv_refl _ inverseGeometricPeriod.property) (value_agreement d e hJ hp hf (k+1))

theorem projection_agreement (hJ : d.rectangle=e.rectangle) (hp : d.center≈e.center)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (z w : Scalar) (hz : (BoundaryCauchySeries.function d).domain z) (hw : (BoundaryCauchySeries.function e).domain w)
    (hzw : z≈w) : (BoundaryCauchySeries.function d).eval z hz≈(BoundaryCauchySeries.function e).eval w hw :=
  CenteredSeries.value_agrees d.center (BoundaryCauchySeries.coefficients d) (BoundaryCauchySeries.coefficients_valid d)
    (bound d).val (rate d).val (BoundaryCauchyNear.radius d).val (Rat.le_of_lt (bound d).property)
    (Rat.le_of_lt (rate d).property) (Rat.le_of_lt (BoundaryCauchyNear.radius d).property) (moment_bound d) (BoundaryCauchySeries.budget d)
    e.center (BoundaryCauchySeries.coefficients e) (BoundaryCauchySeries.coefficients_valid e)
    (bound e).val (rate e).val (BoundaryCauchyNear.radius e).val (Rat.le_of_lt (bound e).property)
    (Rat.le_of_lt (rate e).property) (Rat.le_of_lt (BoundaryCauchyNear.radius e).property) (moment_bound e) (BoundaryCauchySeries.budget e)
    hp (moment_agreement d e hJ hp hf) z w hz hw hzw

theorem derivative_agreement (hJ : d.rectangle=e.rectangle) (hp : d.center≈e.center)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (z w : Scalar) (hz : (BoundaryCauchySeries.function d).domain z) (hw : (BoundaryCauchySeries.function e).domain w)
    (hzw : z≈w) : (BoundaryCauchySeries.holomorphic d).derivative z hz≈(BoundaryCauchySeries.holomorphic e).derivative w hw :=
  CenteredSeries.derivative_agrees d.center (BoundaryCauchySeries.coefficients d) (BoundaryCauchySeries.coefficients_valid d)
    (bound d).val (rate d).val (BoundaryCauchyNear.radius d).val (Rat.le_of_lt (bound d).property)
    (Rat.le_of_lt (rate d).property) (Rat.le_of_lt (BoundaryCauchyNear.radius d).property) (moment_bound d) (BoundaryCauchySeries.budget d)
    e.center (BoundaryCauchySeries.coefficients e) (BoundaryCauchySeries.coefficients_valid e)
    (bound e).val (rate e).val (BoundaryCauchyNear.radius e).val (Rat.le_of_lt (bound e).property)
    (Rat.le_of_lt (rate e).property) (Rat.le_of_lt (BoundaryCauchyNear.radius e).property) (moment_bound e) (BoundaryCauchySeries.budget e)
    hp (moment_agreement d e hJ hp hf) z w hz hw hzw

theorem center_value : (BoundaryCauchySeries.function d).eval d.center (BoundaryCauchySeries.center_mem d)≈moment d 0 :=
  CenteredSeries.initial d.center (BoundaryCauchySeries.coefficients d) (BoundaryCauchySeries.coefficients_valid d)
    (bound d).val (rate d).val (BoundaryCauchyNear.radius d).val (Rat.le_of_lt (bound d).property)
    (Rat.le_of_lt (rate d).property) (Rat.le_of_lt (BoundaryCauchyNear.radius d).property) (moment_bound d) (BoundaryCauchySeries.budget d)
    (BoundaryCauchySeries.center_mem d)

theorem center_derivative : (BoundaryCauchySeries.holomorphic d).derivative d.center (BoundaryCauchySeries.center_mem d)≈moment d 1 :=
  CenteredSeries.derivative_initial d.center (BoundaryCauchySeries.coefficients d) (BoundaryCauchySeries.coefficients_valid d)
    (bound d).val (rate d).val (BoundaryCauchyNear.radius d).val (Rat.le_of_lt (bound d).property)
    (Rat.le_of_lt (rate d).property) (Rat.le_of_lt (BoundaryCauchyNear.radius d).property) (moment_bound d) (BoundaryCauchySeries.budget d)
    (BoundaryCauchySeries.center_mem d)

end ComputableAnalysis.RiemannHilbert.BoundaryCauchyAgreement
