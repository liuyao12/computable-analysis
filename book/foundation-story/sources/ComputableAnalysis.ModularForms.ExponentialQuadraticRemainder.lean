import ComputableAnalysis.ModularForms.ExponentialDerivative

/-! Actual quadratic exponential errors, transported from checked factorial charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def exponentialQuadraticConstant (R : QPos) : Rat :=
  16*exponentialBudget (exponentialRatio R)*(exponentialRatio R)^2

theorem exponentialQuadraticConstant_nonnegative (R : QPos) :
    0≤exponentialQuadraticConstant R :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide) (exponentialBudget_nonnegative _ (exponentialRatio_positive R)))
    (Rat.pow_nonneg (Rat.le_of_lt (exponentialRatio_positive R)))

theorem entireExponential_quadratic_remainder (R : QPos) (a z : Scalar)
    (ha : (exponentialChart R).domain a) (hz : (exponentialChart R).domain z)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H) :
    Small (sub (sub (entireExponentialValue z).val (entireExponentialValue a).val)
      (mul (entireExponentialValue a).val (sub z.val a.val)))
      (exponentialQuadraticConstant R*H^2) := by
  have hb := BoundedSeries.sum_remainder_bound exponentialCoefficients a.val z.val
    exponentialCoefficients_valid a.property z.property
    (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val H
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (Rat.le_of_lt (exponentialRatio_positive R)) (Rat.le_of_lt R.property) hH
    (exponentialCoefficients_small _ (exponentialRatio_positive R))
    (LocalODE.interior_bound R.val a ha) (LocalODE.interior_bound R.val z hz) hza
    (exponentialRatio_local R)
  have hdValid := ((exponentialChart_holomorphic R).atPoint a ha).derivative_valid
  have hfz := (exponentialChart R).valid z hz
  have hfa := (exponentialChart R).valid a ha
  have hd := equiv_trans hdValid hfa (entireExponentialValue a).property
    (exponentialChart_derivative_value R a ha) (entireExponential_chart R a ha)
  have he := FunctionTheory.sub_congr
    (FunctionTheory.sub_congr (entireExponential_chart R z hz) (entireExponential_chart R a ha))
    (mul_equiv hdValid (entireExponentialValue a).property
      (sub_valid z.property a.property) (sub_valid z.property a.property) hd
      (equiv_refl _ (sub_valid z.property a.property)))
  exact Small.congr
    (sub_valid (sub_valid hfz hfa) (mul_valid hdValid (sub_valid z.property a.property)))
    (sub_valid (sub_valid (entireExponentialValue z).property (entireExponentialValue a).property)
      (mul_valid (entireExponentialValue a).property (sub_valid z.property a.property))) he hb

theorem entireExponential_linear_error (R : QPos) (z : Scalar)
    (hz : (exponentialChart R).domain z) (H : Rat) (hH : 0≤H) (hzH : Small z.val H) :
    Small (sub (entireExponentialValue z).val (add (ofQComplex QComplex.one) z.val))
      (exponentialQuadraticConstant R*H^2) := by
  let a : Scalar := ⟨ComplexRaw.zero,ofQComplex_valid _⟩
  have ha : (exponentialChart R).domain a := ⟨0,by decide,R.property,Small.zero (by decide)⟩
  have hez : (sub z.val a.val).Equiv z.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid z.property a.property) (hright := z.property)
    change ComplexRawQuotient.ofRaw z.val z.property + -0=ComplexRawQuotient.ofRaw z.val z.property
    grind only
  have hza := Small.congr z.property (sub_valid z.property a.property) (equiv_symm hez) hzH
  have hb := entireExponential_quadratic_remainder R a z ha hz H hH hza
  have h0 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponentialValue a).property) (hright := ofQComplex_valid _) entireExponential_zero
  have he : (sub (sub (entireExponentialValue z).val (entireExponentialValue a).val)
      (mul (entireExponentialValue a).val (sub z.val a.val))).Equiv
      (sub (entireExponentialValue z).val (add (ofQComplex QComplex.one) z.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid (entireExponentialValue z).property (entireExponentialValue a).property)
        (mul_valid (entireExponentialValue a).property (sub_valid z.property a.property)))
      (hright := sub_valid (entireExponentialValue z).property (add_valid (ofQComplex_valid _) z.property))
    let E := ComplexRawQuotient.ofRaw (entireExponentialValue z).val (entireExponentialValue z).property
    let A := ComplexRawQuotient.ofRaw (entireExponentialValue a).val (entireExponentialValue a).property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change A=1 at h0
    change (E + -A) + -(A*(Z + -0))=E + -(1+Z)
    rw [h0]
    grind only
  exact Small.congr
    (sub_valid (sub_valid (entireExponentialValue z).property (entireExponentialValue a).property)
      (mul_valid (entireExponentialValue a).property (sub_valid z.property a.property)))
    (sub_valid (entireExponentialValue z).property (add_valid (ofQComplex_valid _) z.property)) he hb

end ComputableAnalysis.ModularForms
