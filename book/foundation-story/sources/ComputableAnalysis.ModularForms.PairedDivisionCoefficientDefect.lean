import ComputableAnalysis.ModularForms.PairedDivisionCenterDerivativeApproximation

/-! Exact isolation of the actual quadratic Riccati coefficient and its local defects. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedDivisionQuadraticCoefficientDefect : Scalar :=
  let B : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let A : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  ⟨add B.val (add B.val (add B.val (add B.val (add B.val (mul A.val A.val))))),
    add_valid B.property (add_valid B.property (add_valid B.property
      (add_valid B.property (add_valid B.property (mul_valid A.property A.property)))))⟩

/-- The actual Riccati constant equals three copies of the constructed center coefficient. -/
theorem pairedRiccatiCenterConstant_center_coefficient :
    pairedRiccatiCenterConstant.val.Equiv
      (add pairedCenterConstantSum (add pairedCenterConstantSum pairedCenterConstantSum)) :=
  add_equiv (equiv_symm pairedCenterConstantSum_eq_zeroSquareSum)
    (add_equiv (equiv_symm pairedCenterConstantSum_eq_zeroSquareSum)
      (equiv_symm pairedCenterConstantSum_eq_zeroSquareSum))

private theorem coefficient_algebra (Z Q D A B : ScalarAlgebra.Value)
    (h : Z*D+(Q+(Q+(Q+(Z*Z)*(Q*Q))))=A+(A+A)) :
    (Z*Z)*(B+(B+(B+(B+(B+A*A)))))=
      -(Z*(D-(B+B)*Z)+((((Q-A)-(Z*Z)*B)+
        (((Q-A)-(Z*Z)*B)+((Q-A)-(Z*Z)*B)))+(Z*Z)*((Q*Q)-(A*A)))) := by
  grind only

/-- Exact decomposition of the quadratic coefficient into the actual value,
derivative, and square approximation errors. -/
theorem pairedDivisionQuadraticCoefficientDefect_decomposition (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    (mul (mul z.val z.val) pairedDivisionQuadraticCoefficientDefect.val).Equiv
      (neg (add
        (mul z.val (sub (pairedRegularDivisionDerivative z hz).val
          (mul (add pairedCenterQuadraticSum pairedCenterQuadraticSum) z.val)))
        (add
          (add
            (sub (sub (pairedRegularDivisionMap.eval z hz).val pairedCenterConstantSum)
              (mul (mul z.val z.val) pairedCenterQuadraticSum))
            (add
              (sub (sub (pairedRegularDivisionMap.eval z hz).val pairedCenterConstantSum)
                (mul (mul z.val z.val) pairedCenterQuadraticSum))
              (sub (sub (pairedRegularDivisionMap.eval z hz).val pairedCenterConstantSum)
                (mul (mul z.val z.val) pairedCenterQuadraticSum))))
          (mul (mul z.val z.val)
            (sub (mul (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).val)
              (mul pairedCenterConstantSum pairedCenterConstantSum)))))) := by
  let q := pairedRegularDivisionMap.eval z hz
  let d := pairedRegularDivisionDerivative z hz
  let A : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  let B : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let r := sub (sub q.val A.val) (mul (mul z.val z.val) B.val)
  have vr : r.Valid := sub_valid (sub_valid q.property A.property)
    (mul_valid (mul_valid z.property z.property) B.property)
  have ve := neg_valid (add_valid
    (mul_valid z.property (sub_valid d.property (mul_valid (add_valid B.property B.property) z.property)))
    (add_valid (add_valid vr (add_valid vr vr))
      (mul_valid (mul_valid z.property z.property)
        (sub_valid (mul_valid q.property q.property) (mul_valid A.property A.property)))))
  have he := equiv_trans
    (add_valid (mul_valid z.property d.property)
      (add_valid q.property (add_valid q.property (add_valid q.property
        (mul_valid (mul_valid z.property z.property) (mul_valid q.property q.property))))))
    pairedRiccatiCenterConstant.property (add_valid A.property (add_valid A.property A.property))
    (pairedRegularDivision_riccati_identity z hz) pairedRiccatiCenterConstant_center_coefficient
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := add_valid (mul_valid z.property d.property)
    (add_valid q.property (add_valid q.property (add_valid q.property
      (mul_valid (mul_valid z.property z.property) (mul_valid q.property q.property))))))
    (hright := add_valid A.property (add_valid A.property A.property)) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (mul_valid z.property z.property) pairedDivisionQuadraticCoefficientDefect.property) (hright := ve)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let C := ComplexRawQuotient.ofRaw A.val A.property
  let K := ComplexRawQuotient.ofRaw B.val B.property
  change Z*D+(Q+(Q+(Q+(Z*Z)*(Q*Q))))=C+(C+C) at h
  change (Z*Z)*(K+(K+(K+(K+(K+C*C)))))=
    -(Z*(D-(K+K)*Z)+((((Q-C)-(Z*Z)*K)+
      (((Q-C)-(Z*Z)*K)+((Q-C)-(Z*Z)*K)))+(Z*Z)*((Q*Q)-(C*C))))
  exact coefficient_algebra Z Q D C K h

end ComputableAnalysis.ModularForms
