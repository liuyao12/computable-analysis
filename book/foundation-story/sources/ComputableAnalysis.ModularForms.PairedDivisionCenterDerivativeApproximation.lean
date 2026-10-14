import ComputableAnalysis.ModularForms.PairedDivisionRiccatiEquation

/-! Actual first-derivative approximation at the center in terms of the constructed quadratic coefficient. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedDivisionCenterDerivativeRadius (eps : QPos) : QPos :=
  (pairedDivisionFirstDerivativeMap_holomorphic.atPoint pairedZeroScalar pairedZeroScalar_interior).delta eps

/-- The actual derivative has its linear center approximation with a supplied
analytic modulus, using the proved quadratic coefficient rather than an assumed jet. -/
theorem pairedRegularDivisionDerivative_center_linear_bound (eps H : QPos) (z : Scalar)
    (hz : LocalODE.interior (1/4) z)
    (hH : H.val≤(pairedDivisionCenterDerivativeRadius eps).val) (hs : Small z.val H.val) :
    Small (sub (pairedRegularDivisionDerivative z hz).val
      (mul (scaleRat 2 pairedCenterQuadraticSum) z.val)) (eps.val*H.val) := by
  let hf := pairedDivisionFirstDerivativeMap_holomorphic
  let a := pairedZeroScalar
  let ha := pairedZeroScalar_interior
  have hdiff : (sub z.val a.val).Equiv z.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid z.property a.property) (hright := z.property)
    change ComplexRawQuotient.ofRaw z.val z.property-0=ComplexRawQuotient.ofRaw z.val z.property
    grind only
  have hd : Small (sub z.val a.val) H.val := Small.congr z.property (sub_valid z.property a.property)
    (equiv_symm hdiff) hs
  have h := (hf.atPoint a ha).estimate eps H z hz hH hd
  have hzero := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularDivisionDerivative a ha).property) (hright := ofQComplex_valid _)
    (pairedRegularDivisionDerivative_at_zero a ha (equiv_refl _ a.property))
  have hsecond := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (hf.derivative a ha).property) (hright := scaleRat_valid pairedCenterQuadraticSum_valid)
    (pairedDivisionFirstDerivativeMap_derivative_quadratic_coefficient a ha (equiv_refl _ a.property))
  have he : (DomainFunctions.remainder pairedDivisionFirstDerivativeMap a ha (hf.derivative a ha) z hz).Equiv
      (sub (pairedRegularDivisionDerivative z hz).val (mul (scaleRat 2 pairedCenterQuadraticSum) z.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _)
      (hright := sub_valid (pairedRegularDivisionDerivative z hz).property
        (mul_valid (scaleRat_valid pairedCenterQuadraticSum_valid) z.property))
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let D := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative z hz).val (pairedRegularDivisionDerivative z hz).property
    let A := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative a ha).val (pairedRegularDivisionDerivative a ha).property
    let S := ComplexRawQuotient.ofRaw (hf.derivative a ha).val (hf.derivative a ha).property
    let B := ComplexRawQuotient.ofRaw (scaleRat 2 pairedCenterQuadraticSum) (scaleRat_valid pairedCenterQuadraticSum_valid)
    change A=0 at hzero
    change S=B at hsecond
    change (D-A)-S*(Z-0)=D-B*Z
    generalize Z=z,D=d,A=a,S=s,B=b at hzero hsecond ⊢
    grind only
  exact Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (sub_valid (pairedRegularDivisionDerivative z hz).property
      (mul_valid (scaleRat_valid pairedCenterQuadraticSum_valid) z.property)) he h

end ComputableAnalysis.ModularForms
