import ComputableAnalysis.RiemannHilbert.ContourFiniteSeriesLinearity

/-! Actual finite Taylor contour sums and their proved geometric remainder.
The limit comparison uses the constructed moments and the established
Cauchy formula on a supplied rectangle. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def taylorDisplacementPower (b z : Scalar) (k : Nat) : Scalar :=
  ⟨LocalODE.power (Centered.offset b z).val k,LocalODE.power_valid _ (Centered.offset b z).property k⟩

def cauchyTaylorContourPrefix (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (z : Scalar) (N n : Nat) : Scalar :=
  gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower b z k) (fixedRectanglePowerContour f J hdom b hb (k+1) n))

def cauchyMomentPrefix (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar)
    (hb : f.domain b) (z : Scalar) (N : Nat) : Scalar :=
  gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower b z k) (localCauchyMoment f hf b hb k))

theorem cauchyTaylorContourPrefix_sampler (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (z : Scalar) (N n : Nat) :
    rectangleGridBoundary (fun q => gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower b z k)
      (rectangleBoundarySample (ribbonCauchyPowerKernel f b (k+1)) J (ribbonCauchyPowerBoundaryDomains f J hdom b hb (k+1)) q)))
      J (2^n)≈cauchyTaylorContourPrefix f J hdom b hb z N n := by
  have ho := rectanglePoleInterior_ordered J b hb
  apply Setoid.trans (rectangleGridBoundary_finite_sum _ J (2^n) ho.1 ho.2 N)
  apply gridScalarSum_congr_bounded N
  intro k _
  exact Setoid.trans (rectangleGridBoundary_product_left _ _ J (2^n) ho.1 ho.2)
    (mul_equiv (taylorDisplacementPower b z k).property (taylorDisplacementPower b z k).property
      (rectangleGridBoundary _ J (2^n)).property (fixedRectanglePowerContour f J hdom b hb (k+1) n).property
      (equiv_refl _ (taylorDisplacementPower b z k).property)
      (rectangleBoundarySample_edges _ J ho.1 ho.2 _ n))

theorem cauchyTaylorContourPrefix_sample_value (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (z : Scalar) (N : Nat) (q : QComplex)
    (hq : rationalRectangleBoundaryContains J q) (hw : (ribbonCauchyKernel f b).domain (rationalRectangleScalar q)) :
    gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower b z k)
      (rectangleBoundarySample (ribbonCauchyPowerKernel f b (k+1)) J (ribbonCauchyPowerBoundaryDomains f J hdom b hb (k+1)) q))≈
      cauchyTaylorKernelPrefix f b z (rationalRectangleScalar q) hw N := by
  unfold cauchyTaylorKernelPrefix
  apply gridScalarSum_congr_bounded N
  intro k _
  let s := rectangleBoundarySample (ribbonCauchyPowerKernel f b (k+1)) J
    (ribbonCauchyPowerBoundaryDomains f J hdom b hb (k+1)) q
  let v := ribbonCauchyPowerValue f b (rationalRectangleScalar q) hw (k+1)
  let p := taylorDisplacementPower b z k
  have he : s≈v := rectangleBoundarySample_value (ribbonCauchyPowerKernel f b (k+1)) J
    (ribbonCauchyPowerBoundaryDomains f J hdom b hb (k+1)) q hq hw
  have hv : gridScalarValue s=gridScalarValue v :=
    ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := s.property) (hright := v.property) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct p s).property) (hright := (scalarProduct v p).property)
  change gridScalarValue p*gridScalarValue s=gridScalarValue v*gridScalarValue p
  rw [hv]
  exact ComplexRawQuotient.mul_comm _ _

theorem cauchyTaylorContour_remainder_bound (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b z : Scalar)
    (hb : RectanglePoleInterior J b) (hz : RectanglePoleInterior J z)
    (hdF : RectangleBoundaryDomains f J) (hdR : RectangleBoundaryDomains (ribbonPoleReciprocal b) J)
    (F U H : QPos) (hF : RectangleBoundaryValueBound f J hdF F)
    (hU : RectangleBoundaryValueBound (ribbonPoleReciprocal b) J hdR U)
    (hh : Small (Centered.offset b z).val H.val) (hbudget : 16*U.val*H.val≤1) (N n : Nat) :
    Small (sub (fixedRectangleCauchyContour f J hdom z hz n).val
      (cauchyTaylorContourPrefix f J hdom b hb z N n).val)
      (128*(J.1.width+J.2.width)*F.val*U.val*(4*H.val*U.val)^N) := by
  let s := rectangleBoundarySample (ribbonCauchyKernel f z) J (rectangleCauchyBoundaryDomains f J hdom z hz)
  let t := fun q => gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower b z k)
    (rectangleBoundarySample (ribbonCauchyPowerKernel f b (k+1)) J (ribbonCauchyPowerBoundaryDomains f J hdom b hb (k+1)) q))
  have ho := rectanglePoleInterior_ordered J b hb
  have hbound (q : QComplex) (hq : rationalRectangleBoundaryContains J q) :
      Small (sub (s q).val (t q).val) (32*F.val*U.val*(4*H.val*U.val)^N) := by
    let hw := rectangleBoundaryDomains_rational _ J (rectangleCauchyBoundaryDomains f J hdom b hb) q hq
    let hwz := rectangleBoundaryDomains_rational _ J (rectangleCauchyBoundaryDomains f J hdom z hz) q hq
    have hr := cauchyTaylorKernel_remainder_bound f b z (rationalRectangleScalar q) hw hwz F U H
      (rectangleBoundaryValueBound_rational f J hdF F hF q hq hw.1)
      (rectangleBoundaryValueBound_rational _ J hdR U hU q hq hw.2) hh hbudget N
    exact Small.congr
      (sub_valid ((ribbonCauchyKernel f z).eval _ hwz).property (cauchyTaylorKernelPrefix f b z _ hw N).property)
      (sub_valid (s q).property (t q).property)
      (equiv_symm (FunctionTheory.sub_congr
        (rectangleBoundarySample_value _ J _ q hq hwz)
        (cauchyTaylorContourPrefix_sample_value f J hdom b hb z N q hq hw))) hr
  have he0 : 0≤32*F.val*U.val*(4*H.val*U.val)^N := Rat.le_of_lt
    (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by decide +kernel) F.property) U.property)
      (Rat.pow_pos (Rat.mul_pos (Rat.mul_pos (by decide +kernel) H.property) U.property)))
  have hs := rectangleGridBoundary_difference_bound s t J (2^n) ho.1 ho.2 (Nat.two_pow_pos n) _ he0 hbound
  have he : 4*(J.1.width+J.2.width)*(32*F.val*U.val*(4*H.val*U.val)^N)=
      128*(J.1.width+J.2.width)*F.val*U.val*(4*H.val*U.val)^N := by grind only
  rw [he] at hs
  exact Small.congr (sub_valid (rectangleGridBoundary s J (2^n)).property (rectangleGridBoundary t J (2^n)).property)
    (sub_valid (fixedRectangleCauchyContour f J hdom z hz n).property (cauchyTaylorContourPrefix f J hdom b hb z N n).property)
    (FunctionTheory.sub_congr (rectangleBoundarySample_edges _ J ho.1 ho.2 _ n)
      (cauchyTaylorContourPrefix_sampler f J hdom b hb z N n)) hs

theorem cauchyTaylorContourPrefix_normalized (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (z : Scalar) (N n : Nat) :
    scalarProduct inverseGeometricPeriod (cauchyTaylorContourPrefix f J hdom b hb z N n)≈
      gridScalarSum N (fun k => scalarProduct (taylorDisplacementPower b z k)
        (scalarProduct inverseGeometricPeriod (fixedRectanglePowerContour f J hdom b hb (k+1) n))) := by
  apply Setoid.trans (equiv_symm (gridScalarSum_product_left N inverseGeometricPeriod _))
  apply gridScalarSum_congr_bounded N
  intro k _
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct inverseGeometricPeriod (scalarProduct (taylorDisplacementPower b z k)
      (fixedRectanglePowerContour f J hdom b hb (k+1) n))).property)
    (hright := (scalarProduct (taylorDisplacementPower b z k) (scalarProduct inverseGeometricPeriod
      (fixedRectanglePowerContour f J hdom b hb (k+1) n))).property)
  change gridScalarValue inverseGeometricPeriod*(gridScalarValue (taylorDisplacementPower b z k)*
      gridScalarValue (fixedRectanglePowerContour f J hdom b hb (k+1) n))=
    gridScalarValue (taylorDisplacementPower b z k)*(gridScalarValue inverseGeometricPeriod*
      gridScalarValue (fixedRectanglePowerContour f J hdom b hb (k+1) n))
  grind only

theorem cauchyTaylorContourPrefix_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (ha : f.domain b) (z : Scalar) (N : Nat) :
    Converges (fun n => scalarProduct inverseGeometricPeriod (cauchyTaylorContourPrefix f J hdom b hb z N n))
      (cauchyMomentPrefix f hf b ha z N) := by
  apply converge_congr _ _ _ (converge_finite_sum _ _ (fun k => converge_product_left (taylorDisplacementPower b z k) _ _
    (normalizedFixedRectangleMomentContour_converges f hf J hdom b hb ha k)) N)
  intro n
  exact equiv_symm (cauchyTaylorContourPrefix_normalized f J hdom b hb z N n)

/-- A geometric bound on finite quadratures survives their constructed limits. -/
theorem cauchyMomentPrefix_error (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b z : Scalar) (hb : RectanglePoleInterior J b) (hz : RectanglePoleInterior J z)
    (ha : f.domain b) (hza : f.domain z)
    (hdF : RectangleBoundaryDomains f J) (hdR : RectangleBoundaryDomains (ribbonPoleReciprocal b) J)
    (F U H : QPos) (hF : RectangleBoundaryValueBound f J hdF F)
    (hU : RectangleBoundaryValueBound (ribbonPoleReciprocal b) J hdR U)
    (hh : Small (Centered.offset b z).val H.val) (hbudget : 16*U.val*H.val≤1) (N : Nat) :
    Small (sub (f.eval z hza).val (cauchyMomentPrefix f hf b ha z N).val)
      (256*scalarBound inverseGeometricPeriod*(J.1.width+J.2.width)*F.val*U.val*(4*H.val*U.val)^N) := by
  apply converge_bounded _ _ (converge_difference _ _ _ _
    (normalizedFixedRectangleCauchyContour_converges f hf J hdom z hz)
    (cauchyTaylorContourPrefix_converges f hf J hdom b hb ha z N))
  intro n
  have hs := cauchyTaylorContour_remainder_bound f J hdom b z hb hz hdF hdR F U H hF hU hh hbudget N n
  have hsize : 0≤128*(J.1.width+J.2.width)*F.val*U.val*(4*H.val*U.val)^N := by
    have ho := rectanglePoleInterior_ordered J b hb
    have hx : 0≤J.1.width := by unfold QInterval.width; grind only
    have hy : 0≤J.2.width := by unfold QInterval.width; grind only
    exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
      (by grind only)) (Rat.le_of_lt F.property)) (Rat.le_of_lt U.property))
      (Rat.pow_nonneg (Rat.le_of_lt (Rat.mul_pos (Rat.mul_pos (by decide +kernel) H.property) U.property)))
  have hm := Small.mul inverseGeometricPeriod.property
    (sub_valid (fixedRectangleCauchyContour f J hdom z hz n).property (cauchyTaylorContourPrefix f J hdom b hb z N n).property)
    (Rat.le_of_lt (scalarBound_pos inverseGeometricPeriod)) hsize (scalar_small inverseGeometricPeriod) hs
  have he : 2*scalarBound inverseGeometricPeriod*(128*(J.1.width+J.2.width)*F.val*U.val*(4*H.val*U.val)^N)=
      256*scalarBound inverseGeometricPeriod*(J.1.width+J.2.width)*F.val*U.val*(4*H.val*U.val)^N := by grind only
  rw [he] at hm
  exact Small.congr
    (mul_valid inverseGeometricPeriod.property
      (sub_valid (fixedRectangleCauchyContour f J hdom z hz n).property (cauchyTaylorContourPrefix f J hdom b hb z N n).property))
    (sub_valid (normalizedFixedRectangleCauchyContour f J hdom z hz n).property
      (scalarProduct inverseGeometricPeriod (cauchyTaylorContourPrefix f J hdom b hb z N n)).property)
    (equiv_symm (product_difference_left inverseGeometricPeriod _ _)) hm

end ComputableAnalysis.RiemannHilbert.RectangularContour
