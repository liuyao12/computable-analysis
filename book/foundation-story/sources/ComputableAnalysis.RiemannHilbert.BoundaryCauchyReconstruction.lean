import ComputableAnalysis.RiemannHilbert.BoundaryCauchySeries

/-! The constructed holomorphic series is the actual boundary Cauchy
projection. Finite rational quadratures satisfy the geometric kernel identity;
their constructed limits give the exact represented-value identity. No source
value or holomorphic extension inside the boundary is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchyReconstruction
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false
variable (d : Data)

def finiteQuadrature (z : Scalar) (N n : Nat) : Scalar :=
  gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower d.center z k) (quadrature d (k+1) n))

theorem finiteQuadrature_sampler (z : Scalar) (N n : Nat) :
    rectangleGridBoundary (fun q => gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower d.center z k)
      (rectangleBoundarySample (ribbonCauchyPowerKernel d.source d.center (k+1)) d.rectangle (powerDomains d (k+1)) q)))
      d.rectangle (2^n)≈finiteQuadrature d z N n := by
  apply Setoid.trans (rectangleGridBoundary_finite_sum _ d.rectangle (2^n) d.xOrder d.yOrder N)
  apply gridScalarSum_congr_bounded N
  intro k _
  exact Setoid.trans (rectangleGridBoundary_product_left _ _ d.rectangle (2^n) d.xOrder d.yOrder)
    (mul_equiv (taylorDisplacementPower d.center z k).property (taylorDisplacementPower d.center z k).property
      (rectangleGridBoundary _ d.rectangle (2^n)).property (quadrature d (k+1) n).property
      (equiv_refl _ (taylorDisplacementPower d.center z k).property)
      (rectangleBoundarySample_edges _ d.rectangle d.xOrder d.yOrder _ n))

theorem finiteQuadrature_sample_value (z : Scalar) (N : Nat) (q : QComplex)
    (hq : rationalRectangleBoundaryContains d.rectangle q)
    (hw : (ribbonCauchyKernel d.source d.center).domain (rationalRectangleScalar q)) :
    gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower d.center z k)
      (rectangleBoundarySample (ribbonCauchyPowerKernel d.source d.center (k+1)) d.rectangle (powerDomains d (k+1)) q))≈
      cauchyTaylorKernelPrefix d.source d.center z (rationalRectangleScalar q) hw N := by
  unfold cauchyTaylorKernelPrefix
  apply gridScalarSum_congr_bounded N
  intro k _
  let s := rectangleBoundarySample (ribbonCauchyPowerKernel d.source d.center (k+1)) d.rectangle (powerDomains d (k+1)) q
  let v := ribbonCauchyPowerValue d.source d.center (rationalRectangleScalar q) hw (k+1)
  let p := taylorDisplacementPower d.center z k
  have he : s≈v := rectangleBoundarySample_value _ d.rectangle (powerDomains d (k+1)) q hq hw
  have hv : gridScalarValue s=gridScalarValue v :=
    ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := s.property) (hright := v.property) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct p s).property) (hright := (scalarProduct v p).property)
  change gridScalarValue p*gridScalarValue s=gridScalarValue v*gridScalarValue p
  rw [hv]
  exact ComplexRawQuotient.mul_comm _ _

theorem quadrature_remainder (z : Scalar)
    (hz : Centered.domain d.center (BoundaryCauchyNear.radius d).val z) (N n : Nat) :
    Small (sub (quadrature (BoundaryCauchyNear.data d z hz) 1 n).val (finiteQuadrature d z N n).val)
      (128*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val*
        (4*(BoundaryCauchyNear.radius d).val*d.reciprocalBound.val)^N) := by
  let e := BoundaryCauchyNear.data d z hz
  let s := rectangleBoundarySample (ribbonCauchyPowerKernel d.source z 1) d.rectangle (powerDomains e 1)
  let t := fun q => gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower d.center z k)
    (rectangleBoundarySample (ribbonCauchyPowerKernel d.source d.center (k+1)) d.rectangle (powerDomains d (k+1)) q))
  have hbound (q : QComplex) (hq : rationalRectangleBoundaryContains d.rectangle q) :
      Small (sub (s q).val (t q).val)
        (32*d.valueBound.val*d.reciprocalBound.val*(4*(BoundaryCauchyNear.radius d).val*d.reciprocalBound.val)^N) := by
    let hw := rectangleBoundaryDomains_rational _ d.rectangle (powerDomains d 1) q hq
    let hwz := rectangleBoundaryDomains_rational _ d.rectangle (powerDomains e 1) q hq
    have hr := cauchyTaylorKernel_remainder_bound d.source d.center z (rationalRectangleScalar q) hw hwz
      d.valueBound d.reciprocalBound (BoundaryCauchyNear.radius d)
      (rectangleBoundaryValueBound_rational _ d.rectangle d.sourceDomains d.valueBound d.values q hq hw.1)
      (rectangleBoundaryValueBound_rational _ d.rectangle d.reciprocalDomains d.reciprocalBound d.reciprocals q hq hw.2)
      (LocalODE.interior_bound _ _ hz) (BoundaryCauchyNear.radius_budget d) N
    have hs : s q≈(ribbonCauchyKernel d.source z).eval _ hwz := Setoid.trans
      (rectangleBoundarySample_value _ d.rectangle (powerDomains e 1) q hq hwz)
      (ribbonCauchyPowerKernel_one d.source z _ hwz)
    exact Small.congr
      (sub_valid ((ribbonCauchyKernel d.source z).eval _ hwz).property (cauchyTaylorKernelPrefix d.source d.center z _ hw N).property)
      (sub_valid (s q).property (t q).property)
      (equiv_symm (FunctionTheory.sub_congr hs (finiteQuadrature_sample_value d z N q hq hw))) hr
  have he0 : 0≤32*d.valueBound.val*d.reciprocalBound.val*(4*(BoundaryCauchyNear.radius d).val*d.reciprocalBound.val)^N :=
    Rat.le_of_lt (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by decide +kernel) d.valueBound.property) d.reciprocalBound.property)
      (Rat.pow_pos (Rat.mul_pos (Rat.mul_pos (by decide +kernel) (BoundaryCauchyNear.radius d).property) d.reciprocalBound.property)))
  have hs := rectangleGridBoundary_difference_bound s t d.rectangle (2^n) d.xOrder d.yOrder (Nat.two_pow_pos n) _ he0 hbound
  have he : 4*(d.rectangle.1.width+d.rectangle.2.width)*
      (32*d.valueBound.val*d.reciprocalBound.val*(4*(BoundaryCauchyNear.radius d).val*d.reciprocalBound.val)^N)=
      128*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val*
        (4*(BoundaryCauchyNear.radius d).val*d.reciprocalBound.val)^N := by grind only
  rw [he] at hs
  exact Small.congr (sub_valid (rectangleGridBoundary s d.rectangle (2^n)).property (rectangleGridBoundary t d.rectangle (2^n)).property)
    (sub_valid (quadrature e 1 n).property (finiteQuadrature d z N n).property)
    (FunctionTheory.sub_congr (rectangleBoundarySample_edges _ d.rectangle d.xOrder d.yOrder _ n)
      (finiteQuadrature_sampler d z N n)) hs

theorem finiteQuadrature_normalized (z : Scalar) (N n : Nat) :
    scalarProduct inverseGeometricPeriod (finiteQuadrature d z N n)≈
      gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower d.center z k) (momentPrefix d k n)) := by
  apply Setoid.trans (equiv_symm (gridScalarSum_product_left N inverseGeometricPeriod _))
  apply gridScalarSum_congr_bounded N
  intro k _
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct inverseGeometricPeriod (scalarProduct (taylorDisplacementPower d.center z k) (quadrature d (k+1) n))).property)
    (hright := (scalarProduct (taylorDisplacementPower d.center z k) (momentPrefix d k n)).property)
  change gridScalarValue inverseGeometricPeriod*(gridScalarValue (taylorDisplacementPower d.center z k)*gridScalarValue (quadrature d (k+1) n))=
    gridScalarValue (taylorDisplacementPower d.center z k)*(gridScalarValue inverseGeometricPeriod*gridScalarValue (quadrature d (k+1) n))
  grind only

theorem finiteQuadrature_converges (z : Scalar) (N : Nat) :
    Converges (fun n => scalarProduct inverseGeometricPeriod (finiteQuadrature d z N n))
      (BoundaryCauchySeries.finiteSum d z N) := by
  apply converge_congr _ _ _ (converge_finite_sum _ _
    (fun k => converge_product_left (taylorDisplacementPower d.center z k) _ _ (moment_converges d k)) N)
  intro n
  exact equiv_symm (finiteQuadrature_normalized d z N n)

theorem geometric_rate : 4*(BoundaryCauchyNear.radius d).val*d.reciprocalBound.val=(1:Rat)/8 := by
  have h := BoundaryCauchyNear.radius_rate d
  change (2*d.reciprocalBound.val)*(BoundaryCauchyNear.radius d).val=(1:Rat)/16 at h
  calc
    _=2*((2*d.reciprocalBound.val)*(BoundaryCauchyNear.radius d).val) := by grind only
    _=2*((1:Rat)/16) := by rw [h]
    _=(1:Rat)/8 := by decide +kernel

theorem moment_remainder (z : Scalar)
    (hz : Centered.domain d.center (BoundaryCauchyNear.radius d).val z) (N : Nat) :
    Small (sub (moment (BoundaryCauchyNear.data d z hz) 0).val (BoundaryCauchySeries.finiteSum d z N).val)
      (256*scalarBound inverseGeometricPeriod*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val*
        ((1:Rat)/8)^N) := by
  apply converge_bounded _ _ (converge_difference _ _ _ _
    (moment_converges (BoundaryCauchyNear.data d z hz) 0) (finiteQuadrature_converges d z N))
  intro n
  have hs := quadrature_remainder d z hz N n
  rw [geometric_rate] at hs
  have hx : 0≤d.rectangle.1.width := by unfold QInterval.width; have h := d.xOrder; grind only
  have hy : 0≤d.rectangle.2.width := by unfold QInterval.width; have h := d.yOrder; grind only
  have hsize : 0≤128*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val*((1:Rat)/8)^N :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.add_nonneg hx hy))
      (Rat.le_of_lt d.valueBound.property)) (Rat.le_of_lt d.reciprocalBound.property)) (Rat.pow_nonneg (by decide +kernel))
  have hm := Small.mul inverseGeometricPeriod.property
    (sub_valid (quadrature (BoundaryCauchyNear.data d z hz) 1 n).property (finiteQuadrature d z N n).property)
    (Rat.le_of_lt (scalarBound_pos inverseGeometricPeriod)) hsize (scalar_small inverseGeometricPeriod) hs
  have he : 2*scalarBound inverseGeometricPeriod*
      (128*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val*((1:Rat)/8)^N)=
      256*scalarBound inverseGeometricPeriod*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val*((1:Rat)/8)^N := by grind only
  rw [he] at hm
  exact Small.congr
    (mul_valid inverseGeometricPeriod.property (sub_valid (quadrature (BoundaryCauchyNear.data d z hz) 1 n).property (finiteQuadrature d z N n).property))
    (sub_valid (momentPrefix (BoundaryCauchyNear.data d z hz) 0 n).property
      (scalarProduct inverseGeometricPeriod (finiteQuadrature d z N n)).property)
    (equiv_symm (product_difference_left inverseGeometricPeriod _ _)) hm

theorem finiteSum_contour_converges (z : Scalar)
    (hz : Centered.domain d.center (BoundaryCauchyNear.radius d).val z) :
    Converges (BoundaryCauchySeries.finiteSum d z) (moment (BoundaryCauchyNear.data d z hz) 0) := by
  have hx : 0≤d.rectangle.1.width := by unfold QInterval.width; have h := d.xOrder; grind only
  have hy : 0≤d.rectangle.2.width := by unfold QInterval.width; have h := d.yOrder; grind only
  have hb : 0≤64*scalarBound inverseGeometricPeriod*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt (scalarBound_pos inverseGeometricPeriod))) (Rat.add_nonneg hx hy)) (Rat.le_of_lt d.valueBound.property))
      (Rat.le_of_lt d.reciprocalBound.property)
  have he := LocalODE.tail_bound_shrinks _ ((1:Rat)/8) hb (by decide +kernel) (by decide +kernel)
  intro eps
  obtain ⟨N,hN⟩ := he eps
  refine ⟨N,fun n hn => ?_⟩
  apply (RepresentedCauchySum.small_sub_symm _ _ _ (moment_remainder d z hz n)).mono
  have h := hN n hn
  dsimp only at h
  have eq : 4*(64*scalarBound inverseGeometricPeriod*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val)*((1:Rat)/8)^n=
      256*scalarBound inverseGeometricPeriod*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*d.reciprocalBound.val*((1:Rat)/8)^n := by grind only
  rw [eq] at h
  exact h

/-- Exact equality with the constructed boundary Cauchy integral, for every valid
represented input in the computed ball, including inputs outside the source domain. -/
theorem projection (z : Scalar) (hz : (BoundaryCauchySeries.function d).domain z) :
    (BoundaryCauchySeries.function d).eval z hz≈moment (BoundaryCauchyNear.data d z hz) 0 :=
  converge_unique _ _ _ (BoundaryCauchySeries.finiteSum_converges d z hz) (finiteSum_contour_converges d z hz)

end ComputableAnalysis.RiemannHilbert.BoundaryCauchyReconstruction
