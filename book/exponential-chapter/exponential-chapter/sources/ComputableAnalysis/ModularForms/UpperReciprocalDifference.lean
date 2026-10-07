import ComputableAnalysis.ModularForms.UpperPowerRemainder

/-! Exact and quantitative first differences of actual lattice reciprocals. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem latticeReciprocal_difference (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) :
    (sub (latticeInverse z hz u hu).val (latticeInverse a ha u hu).val).Equiv
      (neg (mul (mul (latticeInverse a ha u hu).val (latticeInverse z hz u hu).val)
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
    (hleft := sub_valid (latticeInverse z hz u hu).property (latticeInverse a ha u hu).property)
    (hright := neg_valid (mul_valid
      (mul_valid (latticeInverse a ha u hu).property (latticeInverse z hz u hu).property)
      (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property))))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw (latticeInverse a ha u hu).val (latticeInverse a ha u hu).property
  let S := ComplexRawQuotient.ofRaw (latticeInverse z hz u hu).val (latticeInverse z hz u hu).property
  change S + -R = -((R*S)*(ComplexRawQuotient.ofQComplex ⟨(u.y:Rat),0⟩*(Z + -A)))
  rw [integer_constant]
  change ((u.y:ScalarAlgebra.Value)*A+(u.x:ScalarAlgebra.Value))*R=1 at hA
  change ((u.y:ScalarAlgebra.Value)*Z+(u.x:ScalarAlgebra.Value))*S=1 at hZ
  grind only

theorem latticeReciprocal_difference_bound (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B T H : Rat) (hB : 0≤B) (hT : 0≤T) (hH : 0≤H)
    (hRa : Small (latticeInverse a ha u hu).val B)
    (hRz : Small (latticeInverse z hz u hu).val B)
    (hTs : Small (ofQComplex ⟨(u.y:Rat),0⟩) T)
    (hza : Small (sub z.val a.val) H) :
    Small (sub (latticeInverse z hz u hu).val (latticeInverse a ha u hu).val) (8*B*B*T*H) := by
  have hrr := Small.mul (latticeInverse a ha u hu).property (latticeInverse z hz u hu).property
    hB hB hRa hRz
  have hd := Small.mul (ofQComplex_valid _) (sub_valid z.property a.property) hT hH hTs hza
  have hrrB := Rat.mul_nonneg (Rat.mul_nonneg (by decide : (0:Rat)≤2) hB) hB
  have hdB := Rat.mul_nonneg (Rat.mul_nonneg (by decide : (0:Rat)≤2) hT) hH
  have hb := SeriesLimitLaws.small_neg (Small.mul
    (mul_valid (latticeInverse a ha u hu).property (latticeInverse z hz u hu).property)
    (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property)) hrrB hdB hrr hd)
  have he : 2*(2*B*B)*(2*T*H)=8*B*B*T*H := by grind
  rw [he] at hb
  exact Small.congr (neg_valid (mul_valid
    (mul_valid (latticeInverse a ha u hu).property (latticeInverse z hz u hu).property)
    (mul_valid (ofQComplex_valid _) (sub_valid z.property a.property))))
    (sub_valid (latticeInverse z hz u hu).property (latticeInverse a ha u hu).property)
    (equiv_symm (latticeReciprocal_difference u hu a z ha hz)) hb

end ComputableAnalysis.ModularForms
