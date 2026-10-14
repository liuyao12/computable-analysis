import ComputableAnalysis.RiemannHilbert.RectangularPoleReciprocal
import ComputableAnalysis.RiemannHilbert.BoundaryCauchyOverlap

/-! Actual Cauchy projections on the entire interior and exterior of a
rectangle. Only genuine source data on the four edges are supplied. Pole
bounds and local holomorphic witnesses are constructed at every represented
input; quadrature comparison proves that all internal choices agree. -/
namespace ComputableAnalysis.RiemannHilbert.GlobalBoundaryCauchy
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false

structure BoundaryData where
  source : DomainFunctions.Map
  holomorphic : Holomorphic source
  rectangle : QInterval × QInterval
  xOrder : rectangle.1.lo≤rectangle.1.hi
  yOrder : rectangle.2.lo≤rectangle.2.hi
  sourceDomains : RectangleBoundaryDomains source rectangle
  valueBound : QPos
  derivativeBound : QPos
  values : RectangleBoundaryValueBound source rectangle sourceDomains valueBound
  derivatives : RectangleBoundaryDerivativeBound source holomorphic rectangle sourceDomains derivativeBound

def ofData (d : Data) : BoundaryData where
  source := d.source
  holomorphic := d.holomorphic
  rectangle := d.rectangle
  xOrder := d.xOrder
  yOrder := d.yOrder
  sourceDomains := d.sourceDomains
  valueBound := d.valueBound
  derivativeBound := d.derivativeBound
  values := d.values
  derivatives := d.derivatives

variable (d : BoundaryData) (inside : Bool)

def atPoint (b : Scalar) (hb : RectangularPoleSearch.domain inside d.rectangle b) : Data where
  source := d.source
  holomorphic := d.holomorphic
  rectangle := d.rectangle
  xOrder := d.xOrder
  yOrder := d.yOrder
  center := b
  sourceDomains := d.sourceDomains
  reciprocalDomains := RectangularPoleReciprocal.boundaryDomains inside d.rectangle b hb d.xOrder d.yOrder
  valueBound := d.valueBound
  derivativeBound := d.derivativeBound
  reciprocalBound := RectangularPoleReciprocal.bound inside d.rectangle b hb
  values := d.values
  derivatives := d.derivatives
  reciprocals := RectangularPoleReciprocal.boundary_bound inside d.rectangle b hb d.xOrder d.yOrder _

def value (b : Scalar) (hb : RectangularPoleSearch.domain inside d.rectangle b) : Scalar :=
  moment (atPoint d inside b hb) 0

theorem value_congr (b c : Scalar) (hb : RectangularPoleSearch.domain inside d.rectangle b)
    (hc : RectangularPoleSearch.domain inside d.rectangle c) (he : b≈c) : value d inside b hb≈value d inside c hc :=
  BoundaryCauchyAgreement.moment_agreement (atPoint d inside b hb) (atPoint d inside c hc) rfl he
    (fun w hw _hc => equiv_refl _ (d.source.eval w hw).property) 0

def function : DomainFunctions.Map where
  domain := RectangularPoleSearch.domain inside d.rectangle
  eval := value d inside
  domain_congr := (RectangularPoleSearch.openData inside d.rectangle).invariant
  eval_congr := value_congr d inside

def localDomainData (a : Scalar) (ha : (function d inside).domain a) : ScalarTopology.OpenData
    (fun z => (BoundaryCauchySeries.function (atPoint d inside a ha)).domain z ∧ (function d inside).domain z) :=
  (ScalarTopology.ofDomain _ (BoundaryCauchySeries.holomorphic (atPoint d inside a ha)).openDomain).inter
    (RectangularPoleSearch.openData inside d.rectangle)

def localFunction (a : Scalar) (ha : (function d inside).domain a) : DomainFunctions.Map :=
  onDomain (BoundaryCauchySeries.function (atPoint d inside a ha))
    (localDomainData d inside a ha).invariant (fun _ h => h.1)

def localHolomorphic (a : Scalar) (ha : (function d inside).domain a) : Holomorphic (localFunction d inside a ha) :=
  (BoundaryCauchySeries.holomorphic (atPoint d inside a ha)).onDomain (localDomainData d inside a ha) (fun _ h => h.1)

theorem local_center (a : Scalar) (ha : (function d inside).domain a) : (localFunction d inside a ha).domain a :=
  ⟨BoundaryCauchySeries.center_mem (atPoint d inside a ha),ha⟩

theorem local_agreement (a : Scalar) (ha : (function d inside).domain a) (z : Scalar)
    (hz : (localFunction d inside a ha).domain z) :
    (localFunction d inside a ha).eval z hz≈(function d inside).eval z hz.2 :=
  Setoid.trans (BoundaryCauchyReconstruction.projection (atPoint d inside a ha) z hz.1)
    (BoundaryCauchyAgreement.moment_agreement (BoundaryCauchyNear.data (atPoint d inside a ha) z hz.1)
      (atPoint d inside z hz.2) rfl (equiv_refl _ z.property)
      (fun w hw _he => equiv_refl _ (d.source.eval w hw).property) 0)

/-- Global derivative, derivative continuity and open-domain evidence are
derived from the actual local series and their proved value agreement. -/
def holomorphic : Holomorphic (function d inside) :=
  holomorphic_of_local (function d inside) (localFunction d inside) (localHolomorphic d inside)
    (local_center d inside) (fun _ _ _ hz => hz.2) (local_agreement d inside)

theorem local_series (e : Data) (hJ : e.rectangle=d.rectangle)
    (hf : ∀ w (he : e.source.domain w) (hd : d.source.domain w), e.source.eval w he≈d.source.eval w hd)
    (z : Scalar) (hz : (BoundaryCauchySeries.function e).domain z) (hD : (function d inside).domain z) :
    (BoundaryCauchySeries.function e).eval z hz≈(function d inside).eval z hD :=
  Setoid.trans (BoundaryCauchyReconstruction.projection e z hz)
    (BoundaryCauchyAgreement.moment_agreement (BoundaryCauchyNear.data e z hz) (atPoint d inside z hD)
      hJ (equiv_refl _ z.property) hf 0)

theorem derivative_value (z : Scalar) (hz : (function d inside).domain z) :
    (holomorphic d inside).derivative z hz≈moment (atPoint d inside z hz) 1 :=
  BoundaryCauchyAgreement.center_derivative (atPoint d inside z hz)

theorem agrees (e : BoundaryData) (hJ : d.rectangle=e.rectangle)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (z w : Scalar) (hz : (function d inside).domain z) (hw : (function e inside).domain w) (he : z≈w) :
    (function d inside).eval z hz≈(function e inside).eval w hw :=
  BoundaryCauchyAgreement.moment_agreement (atPoint d inside z hz) (atPoint e inside w hw) hJ he hf 0

theorem derivative_agrees (e : BoundaryData) (hJ : d.rectangle=e.rectangle)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (z w : Scalar) (hz : (function d inside).domain z) (hw : (function e inside).domain w) (he : z≈w) :
    (holomorphic d inside).derivative z hz≈(holomorphic e inside).derivative w hw :=
  Setoid.trans (derivative_value d inside z hz)
    (Setoid.trans (BoundaryCauchyAgreement.moment_agreement (atPoint d inside z hz) (atPoint e inside w hw) hJ he hf 1)
      (equiv_symm (derivative_value e inside w hw)))

theorem reproduces (hdom : ∀ z, representedRectangleContains d.rectangle z → d.source.domain z)
    (z : Scalar) (hz : (function d true).domain z) :
    (function d true).eval z hz≈d.source.eval z (hdom z (rectanglePoleInterior_mem d.rectangle z hz)) :=
  Setoid.trans (equiv_symm (BoundaryCauchyAgreement.center_value (atPoint d true z hz)))
    (BoundaryCauchyExamples.reproduces (atPoint d true z hz) hdom z (BoundaryCauchySeries.center_mem _) hz)

theorem exterior_zero (hdom : ∀ z, representedRectangleContains d.rectangle z → d.source.domain z)
    (z : Scalar) (hz : (function d false).domain z) :
    (function d false).eval z hz≈rationalRectangleScalar QComplex.zero := by
  let a := atPoint d false z hz
  let K := ribbonCauchyPowerKernel d.source z 1
  have hd : ∀ w, representedRectangleContains d.rectangle w → K.domain w :=
    AnnularPoleGeometry.kernel_domain d.source d.rectangle hdom z hz
  have hq : Converges (quadrature a 1) (rationalRectangleScalar QComplex.zero) :=
    converge_zero _ (continuousRectangleBoundary_eventual_zero K
      (ribbonCauchyPowerKernel_holomorphic d.source d.holomorphic z 1) d.rectangle d.xOrder d.yOrder hd (powerDomains a 1))
  have hm := converge_product_left inverseGeometricPeriod _ _ hq
  have he : scalarProduct inverseGeometricPeriod (rationalRectangleScalar QComplex.zero)≈
      rationalRectangleScalar QComplex.zero := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (scalarProduct inverseGeometricPeriod
      (rationalRectangleScalar QComplex.zero)).property) (hright := ofQComplex_valid _)
    change gridScalarValue inverseGeometricPeriod*0=0
    grind only
  exact converge_unique _ _ _ (moment_converges a 0) (converge_limit_congr _ _ _ hm he)

end ComputableAnalysis.RiemannHilbert.GlobalBoundaryCauchy
