import ComputableAnalysis.RiemannHilbert.BoundaryCauchyHomogeneousEstimates

/-! Actual boundary-source errors control constructed Cauchy moments.
The comparison is derived from literal finite quadratures and their proved
convergence, independently of the supplied derivative bounds. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchySourceComparison
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false

theorem product_difference_right (a b r s : Scalar) (hrs : r≈s) :
    (sub (scalarProduct a r).val (scalarProduct b s).val).Equiv
      (mul (sub a.val b.val) r.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scalarProduct a r).property (scalarProduct b s).property)
    (hright := mul_valid (sub_valid a.property b.property) r.property)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := r.property) (hright := s.property) hrs
  change gridScalarValue a*gridScalarValue r-gridScalarValue b*gridScalarValue s=
    (gridScalarValue a-gridScalarValue b)*gridScalarValue r
  change gridScalarValue r=gridScalarValue s at he
  rw [←he]
  grind only

theorem kernel_difference (f g : DomainFunctions.Map) (b c w : Scalar) (hbc : b≈c)
    (hf : (ribbonCauchyKernel f b).domain w) (hg : (ribbonCauchyKernel g c).domain w)
    (E U : Rat) (hE : 0≤E) (hU : 0≤U)
    (he : Small (sub (f.eval w hf.1).val (g.eval w hg.1).val) E)
    (hu : Small ((ribbonPoleReciprocal b).eval w hf.2).val U) (k : Nat) :
    Small (sub (ribbonCauchyPowerValue f b w hf k).val
      (ribbonCauchyPowerValue g c w hg k).val) (E*(2*U)^k) := by
  induction k with
  | zero => simpa only [ribbonCauchyPowerValue,Rat.pow_zero,Rat.mul_one] using he
  | succ k ih =>
    have hs := Small.mul
      (sub_valid (ribbonCauchyPowerValue f b w hf k).property (ribbonCauchyPowerValue g c w hg k).property)
      ((ribbonPoleReciprocal b).eval w hf.2).property
      (Rat.mul_nonneg hE (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hU))) hU ih hu
    have heq : 2*(E*(2*U)^k)*U=E*(2*U)^(k+1) := by rw [Rat.pow_succ]; grind only
    rw [heq] at hs
    exact Small.congr
      (mul_valid (sub_valid (ribbonCauchyPowerValue f b w hf k).property (ribbonCauchyPowerValue g c w hg k).property)
        ((ribbonPoleReciprocal b).eval w hf.2).property)
      (sub_valid (ribbonCauchyPowerValue f b w hf (k+1)).property (ribbonCauchyPowerValue g c w hg (k+1)).property)
      (equiv_symm (product_difference_right _ _ _ _ (ribbonPoleReciprocal_congr b c w hbc hf.2 hg.2))) hs

variable (d e : Data) (hJ : d.rectangle=e.rectangle) (hc : d.center≈e.center)
    (E : Rat) (hE : 0≤E)
    (he : ∀ q, rationalRectangleBoundaryContains d.rectangle q →
      ∀ hd he, Small (sub (d.source.eval (rationalRectangleScalar q) hd).val
        (e.source.eval (rationalRectangleScalar q) he).val) E)

include hJ hc hE he in
theorem quadrature_difference (k n : Nat) :
    Small (sub (quadrature d k n).val (quadrature e k n).val)
      (4*(d.rectangle.1.width+d.rectangle.2.width)*(E*(2*d.reciprocalBound.val)^k)) := by
  let f := ribbonCauchyPowerKernel d.source d.center k
  let g := ribbonCauchyPowerKernel e.source e.center k
  let hg : RectangleBoundaryDomains g d.rectangle := hJ.symm ▸ powerDomains e k
  have hs := rectangleGridBoundary_difference_bound
    (rectangleBoundarySample f d.rectangle (powerDomains d k))
    (rectangleBoundarySample g d.rectangle hg) d.rectangle (2^n)
    d.xOrder d.yOrder (Nat.two_pow_pos n) (E*(2*d.reciprocalBound.val)^k)
    (Rat.mul_nonneg hE (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt d.reciprocalBound.property))))
    (fun q hq => by
      let hdq := rectangleBoundaryDomains_rational f d.rectangle (powerDomains d k) q hq
      let heq := rectangleBoundaryDomains_rational g d.rectangle hg q hq
      have hu := rectangleBoundaryValueBound_rational _ d.rectangle d.reciprocalDomains d.reciprocalBound d.reciprocals q hq hdq.2
      have hb := kernel_difference d.source e.source d.center e.center _ hc hdq heq
        E d.reciprocalBound.val hE (Rat.le_of_lt d.reciprocalBound.property) (he q hq hdq.1 heq.1) hu k
      exact Small.congr
        (sub_valid (f.eval _ hdq).property (g.eval _ heq).property)
        (sub_valid (rectangleBoundarySample f d.rectangle (powerDomains d k) q).property
          (rectangleBoundarySample g d.rectangle hg q).property)
        (equiv_symm (FunctionTheory.sub_congr
          (rectangleBoundarySample_value f d.rectangle (powerDomains d k) q hq hdq)
          (rectangleBoundarySample_value g d.rectangle hg q hq heq))) hb)
  have hright := Setoid.trans (rectangleBoundarySample_edges g d.rectangle d.xOrder d.yOrder hg n)
    (BoundaryCauchyAgreement.rectangle_transport g d.rectangle e.rectangle hJ hg (powerDomains e k) n)
  exact Small.congr
    (sub_valid (rectangleGridBoundary _ d.rectangle (2^n)).property (rectangleGridBoundary _ d.rectangle (2^n)).property)
    (sub_valid (quadrature d k n).property (quadrature e k n).property)
    (FunctionTheory.sub_congr (rectangleBoundarySample_edges f d.rectangle d.xOrder d.yOrder (powerDomains d k) n) hright) hs

include hJ hc hE he in
theorem value_difference (k : Nat) :
    Small (sub (value d k).val (value e k).val)
      (4*(d.rectangle.1.width+d.rectangle.2.width)*(E*(2*d.reciprocalBound.val)^k)) :=
  converge_bounded _ _ (converge_difference _ _ _ _ (converges d k) (converges e k)) _
    (quadrature_difference d e hJ hc E hE he k)

include hJ hc hE he in
theorem moment_difference (k : Nat) :
    Small (sub (moment d k).val (moment e k).val)
      (BoundaryCauchyHomogeneousEstimates.constant d.rectangle d.reciprocalBound.val*E*(2*d.reciprocalBound.val)^k) := by
  have hX : 0≤d.rectangle.1.width := by unfold QInterval.width; have h := d.xOrder; grind only
  have hY : 0≤d.rectangle.2.width := by unfold QInterval.width; have h := d.yOrder; grind only
  have hs := Small.mul inverseGeometricPeriod.property
    (sub_valid (value d (k+1)).property (value e (k+1)).property)
    (Rat.le_of_lt (scalarBound_pos inverseGeometricPeriod))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.add_nonneg hX hY))
      (Rat.mul_nonneg hE (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt d.reciprocalBound.property)))))
    (scalar_small inverseGeometricPeriod) (value_difference d e hJ hc E hE he (k+1))
  have heq : 2*scalarBound inverseGeometricPeriod*
      (4*(d.rectangle.1.width+d.rectangle.2.width)*(E*(2*d.reciprocalBound.val)^(k+1)))=
      BoundaryCauchyHomogeneousEstimates.constant d.rectangle d.reciprocalBound.val*E*(2*d.reciprocalBound.val)^k := by
    unfold BoundaryCauchyHomogeneousEstimates.constant
    rw [Rat.pow_succ]
    grind only
  rw [heq] at hs
  exact Small.congr (mul_valid inverseGeometricPeriod.property
      (sub_valid (value d (k+1)).property (value e (k+1)).property))
    (sub_valid (moment d k).property (moment e k).property)
    (equiv_symm (product_difference_left inverseGeometricPeriod _ _)) hs

end ComputableAnalysis.RiemannHilbert.BoundaryCauchySourceComparison
