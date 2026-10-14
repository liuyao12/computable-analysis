import ComputableAnalysis.ModularForms.PairedDivisionCoefficientDefect

/-! Quantitative error bounds for extracting the actual quadratic Riccati coefficient. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem double_coefficient : (add pairedCenterQuadraticSum pairedCenterQuadraticSum).Equiv
    (scaleRat 2 pairedCenterQuadraticSum) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid pairedCenterQuadraticSum_valid pairedCenterQuadraticSum_valid)
    (hright := scaleRat_valid pairedCenterQuadraticSum_valid)
  let B := ComplexRawQuotient.ofRaw pairedCenterQuadraticSum pairedCenterQuadraticSum_valid
  change B+B=ComplexRawQuotient.scaleRat 2 B
  have h := ComplexRawQuotient.add_scaleRat 1 1 B
  rw [ComplexRawQuotient.scaleRat_one,show (1:Rat)+1=2 by decide +kernel] at h
  exact h

/-- Actual division-square values have a quadratic center difference bound. -/
theorem pairedRegularDivision_square_center_bound (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (mul (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).val)
      (mul pairedCenterConstantSum pairedCenterConstantSum)) (184320*R*R) := by
  let Q := pairedRegularDivisionMap.eval z hz
  let A : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  have hdiff := pairedRegularDivision_center_difference_bound pairedZeroScalar z pairedZeroScalar_interior hz
    (equiv_refl _ pairedZeroScalar.property) R hR hs
  have hA := pairedRegularDivisionValue_center_constant pairedZeroScalar pairedZeroScalar_interior
    (equiv_refl _ pairedZeroScalar.property)
  have hd : Small (sub Q.val A.val) (4608*R*R) := Small.congr
    (sub_valid Q.property (pairedRegularDivisionMap.eval pairedZeroScalar pairedZeroScalar_interior).property)
    (sub_valid Q.property A.property) (FunctionTheory.sub_congr (equiv_refl Q.val Q.property) hA) hdiff
  have hQ : Small Q.val 16 := by
    have h := inverseSquareSeriesValue_bound _
      (fun n => (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).property) 8
      (pairedRegularDivisionTerm_bound z (LocalODE.interior_bound _ z hz))
    simpa only [Q,pairedRegularDivisionMap,pairedRegularDivisionValue,
      show 2*((8:Nat):Rat)=16 by decide +kernel] using h
  have hC : Small A.val 4 := by
    have h := inverseSquareSeriesValue_bound _ pairedCenterConstantTerm_valid 2 pairedCenterConstantTerm_bound
    simpa only [A,pairedCenterConstantSum,show 2*((2:Nat):Rat)=4 by decide +kernel] using h
  have hsum := LocalODE.small_add hQ hC
  have h := Small.mul (sub_valid Q.property A.property) (add_valid Q.property A.property)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR) (show (0:Rat)≤16+4 by decide +kernel) hd hsum
  have he : (mul (sub Q.val A.val) (add Q.val A.val)).Equiv
      (sub (mul Q.val Q.val) (mul A.val A.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid (sub_valid Q.property A.property) (add_valid Q.property A.property))
      (hright := sub_valid (mul_valid Q.property Q.property) (mul_valid A.property A.property))
    let q := ComplexRawQuotient.ofRaw Q.val Q.property
    let a := ComplexRawQuotient.ofRaw A.val A.property
    change (q-a)*(q+a)=q*q-a*a
    generalize q=x,a=y
    grind only
  have hb := Small.congr (mul_valid (sub_valid Q.property A.property) (add_valid Q.property A.property))
    (sub_valid (mul_valid Q.property Q.property) (mul_valid A.property A.property)) he h
  have hrate : 2*(4608*R*R)*(16+4)=184320*R*R := by grind only
  rw [hrate] at hb
  exact hb

/-- The actual coefficient defect is bounded after multiplication by the
squared input. The derivative modulus supplies the only linear error. -/
theorem pairedDivisionQuadraticCoefficientDefect_scaled_bound (eps H : QPos) (z : Scalar)
    (hz : LocalODE.interior (1/4) z)
    (hH : H.val≤(pairedDivisionCenterDerivativeRadius eps).val) (hs : Small z.val H.val) :
    Small (mul (mul z.val z.val) pairedDivisionQuadraticCoefficientDefect.val)
      (2*eps.val*H.val*H.val+740352*H.val*H.val*H.val*H.val) := by
  let Q := pairedRegularDivisionMap.eval z hz
  let D := pairedRegularDivisionDerivative z hz
  let A : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  let B : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let r := sub (sub Q.val A.val) (mul (mul z.val z.val) B.val)
  have vr : r.Valid := sub_valid (sub_valid Q.property A.property) (mul_valid (mul_valid z.property z.property) B.property)
  have hD := pairedRegularDivisionDerivative_center_linear_bound eps H z hz hH hs
  have hd : Small (sub D.val (mul (add B.val B.val) z.val)) (eps.val*H.val) :=
    Small.congr (sub_valid D.property (mul_valid (scaleRat_valid B.property) z.property))
      (sub_valid D.property (mul_valid (add_valid B.property B.property) z.property))
      (FunctionTheory.sub_congr (equiv_refl D.val D.property)
        (mul_equiv (scaleRat_valid B.property) (add_valid B.property B.property) z.property z.property
          (equiv_symm double_coefficient) (equiv_refl z.val z.property))) hD
  have hzD := Small.mul z.property (sub_valid D.property (mul_valid (add_valid B.property B.property) z.property))
    (Rat.le_of_lt H.property) (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property)) hs hd
  have hr : Small r (1024*H.val*H.val*H.val*H.val) :=
    pairedRegularDivisionValue_quadratic_center_bound z hz H.val (Rat.le_of_lt H.property) hs
  have hr3 := LocalODE.small_add hr (LocalODE.small_add hr hr)
  have hzz := Small.mul z.property z.property (Rat.le_of_lt H.property) (Rat.le_of_lt H.property) hs hs
  have hsq := pairedRegularDivision_square_center_bound z hz H.val (Rat.le_of_lt H.property) hs
  have hlast := Small.mul (mul_valid z.property z.property)
    (sub_valid (mul_valid Q.property Q.property) (mul_valid A.property A.property))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt H.property)) (Rat.le_of_lt H.property))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt H.property)) (Rat.le_of_lt H.property)) hzz hsq
  have h := SeriesLimitLaws.small_neg (LocalODE.small_add hzD (LocalODE.small_add hr3 hlast))
  have hb := Small.congr
    (neg_valid (add_valid
      (mul_valid z.property (sub_valid D.property (mul_valid (add_valid B.property B.property) z.property)))
      (add_valid (add_valid vr (add_valid vr vr))
        (mul_valid (mul_valid z.property z.property) (sub_valid (mul_valid Q.property Q.property) (mul_valid A.property A.property))))))
    (mul_valid (mul_valid z.property z.property) pairedDivisionQuadraticCoefficientDefect.property)
    (equiv_symm (pairedDivisionQuadraticCoefficientDefect_decomposition z hz)) h
  have he : 2*H.val*(eps.val*H.val)+
      ((1024*H.val*H.val*H.val*H.val+(1024*H.val*H.val*H.val*H.val+1024*H.val*H.val*H.val*H.val))+
        2*(2*H.val*H.val)*(184320*H.val*H.val))=
      2*eps.val*H.val*H.val+740352*H.val*H.val*H.val*H.val := by grind only
  rw [he] at hb
  exact hb

end ComputableAnalysis.ModularForms
