import ComputableAnalysis.ModularForms.UpperReciprocalDerivative

/-! Exact quadratic remainder of the actual lattice reciprocal map. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert DomainFunctions

 theorem latticeReciprocal_remainder (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) :
    (DomainFunctions.remainder (latticeReciprocalMap u hu) a ha
      ((latticeReciprocalMap_holomorphic u hu).derivative a ha) z hz).Equiv
      (mul (mul (mul (latticeInverse a ha u hu).val (latticeInverse a ha u hu).val)
        (latticeInverse z hz u hu).val)
        (mul (mul (ofQComplex ⟨(u.y:Rat),0⟩) (sub z.val a.val))
          (mul (ofQComplex ⟨(u.y:Rat),0⟩) (sub z.val a.val)))) := by
  have hA := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (latticeVector a u).property (latticeInverse a ha u hu).property)
    (hright := ofQComplex_valid _) (latticeInverse_product a ha u hu)
  have hZ := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (latticeVector z u).property (latticeInverse z hz u hu).property)
    (hright := ofQComplex_valid _) (latticeInverse_product z hz u hu)
  change ComplexRawQuotient.ofRaw (integerAffine u.y u.x a.val) (integerAffine_valid _ _ a.property)*
    ComplexRawQuotient.ofRaw (latticeInverse a ha u hu).val (latticeInverse a ha u hu).property=1 at hA
  change ComplexRawQuotient.ofRaw (integerAffine u.y u.x z.val) (integerAffine_valid _ _ z.property)*
    ComplexRawQuotient.ofRaw (latticeInverse z hz u hu).val (latticeInverse z hz u hu).property=1 at hZ
  rw [integerAffine_class] at hA hZ
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _)
    (hright := mul_valid
      (mul_valid (mul_valid (latticeInverse a ha u hu).property (latticeInverse a ha u hu).property)
        (latticeInverse z hz u hu).property)
      (mul_valid (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property))
        (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property))))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw (latticeInverse a ha u hu).val (latticeInverse a ha u hu).property
  let S := ComplexRawQuotient.ofRaw (latticeInverse z hz u hu).val (latticeInverse z hz u hu).property
  change ((S + -R) + -((-(R*R)*ComplexRawQuotient.ofQComplex ⟨(u.y:Rat),0⟩)*(Z + -A))) =
    ((R*R)*S)*((ComplexRawQuotient.ofQComplex ⟨(u.y:Rat),0⟩*(Z + -A))*
      (ComplexRawQuotient.ofQComplex ⟨(u.y:Rat),0⟩*(Z + -A)))
  rw [integer_constant]
  change ((u.y:ScalarAlgebra.Value)*A+(u.x:ScalarAlgebra.Value))*R=1 at hA
  change ((u.y:ScalarAlgebra.Value)*Z+(u.x:ScalarAlgebra.Value))*S=1 at hZ
  grind only

theorem latticeReciprocal_remainder_bound (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B T H : Rat) (hB : 0≤B) (hT : 0≤T) (hH : 0≤H)
    (hRa : FunctionTheory.Small (latticeInverse a ha u hu).val B)
    (hRz : FunctionTheory.Small (latticeInverse z hz u hu).val B)
    (hTsmall : FunctionTheory.Small (ofQComplex ⟨(u.y:Rat),0⟩) T)
    (hza : FunctionTheory.Small (sub z.val a.val) H) :
    FunctionTheory.Small (DomainFunctions.remainder (latticeReciprocalMap u hu) a ha
      ((latticeReciprocalMap_holomorphic u hu).derivative a ha) z hz)
      (64*B*B*B*T*T*H*H) := by
  have h2 := FunctionTheory.Small.mul (latticeInverse a ha u hu).property
    (latticeInverse a ha u hu).property hB hB hRa hRa
  have h2B : 0≤2*B*B := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hB
  have h3 := FunctionTheory.Small.mul
    (mul_valid (latticeInverse a ha u hu).property (latticeInverse a ha u hu).property)
    (latticeInverse z hz u hu).property h2B hB h2 hRz
  have hd := FunctionTheory.Small.mul (ofQComplex_valid _) (sub_valid z.property a.property)
    hT hH hTsmall hza
  have hdB : 0≤2*T*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hT) hH
  have hdd := FunctionTheory.Small.mul (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property))
    (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property)) hdB hdB hd hd
  have h3B : 0≤2*(2*B*B)*B := Rat.mul_nonneg (Rat.mul_nonneg (by decide) h2B) hB
  have hddB : 0≤2*(2*T*H)*(2*T*H) := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hdB) hdB
  have hb := FunctionTheory.Small.mul
    (mul_valid (mul_valid (latticeInverse a ha u hu).property (latticeInverse a ha u hu).property)
      (latticeInverse z hz u hu).property)
    (mul_valid (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property))
      (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property))) h3B hddB h3 hdd
  have he : 2*(2*(2*B*B)*B)*(2*(2*T*H)*(2*T*H))=64*B*B*B*T*T*H*H := by grind
  rw [he] at hb
  exact FunctionTheory.Small.congr
    (mul_valid
      (mul_valid (mul_valid (latticeInverse a ha u hu).property (latticeInverse a ha u hu).property)
        (latticeInverse z hz u hu).property)
      (mul_valid (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property))
        (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property))))
    (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (latticeReciprocal_remainder u hu a z ha hz)) hb

end ComputableAnalysis.ModularForms
