import ComputableAnalysis.RiemannHilbert.ReciprocalLocalBounds

/-! Exact first differences and derivative remainders for the constructed
reciprocal, at arbitrary valid represented inputs. -/
namespace ComputableAnalysis.RiemannHilbert.ReciprocalDifference
open ComplexRaw FunctionTheory NonzeroBoxSearch RepresentedReciprocal

def derivative (a : Scalar) (ha : Nonzero a) : Scalar :=
  ⟨neg (mul (inverse a ha).val (inverse a ha).val),
    neg_valid (mul_valid (inverse a ha).property (inverse a ha).property)⟩

theorem difference (a z : Scalar) (ha : Nonzero a) (hz : Nonzero z) :
    (sub (inverse z hz).val (inverse a ha).val).Equiv
      (neg (mul (mul (inverse a ha).val (sub z.val a.val)) (inverse z hz).val)) := by
  have hA := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid a.property (inverse a ha).property) (hright := ofQComplex_valid _) (mul_inverse a ha)
  have hZ := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (inverse z hz).property) (hright := ofQComplex_valid _) (mul_inverse z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (inverse z hz).property (inverse a ha).property)
    (hright := neg_valid (mul_valid (mul_valid (inverse a ha).property (sub_valid z.property a.property))
      (inverse z hz).property))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw (inverse a ha).val (inverse a ha).property
  let S := ComplexRawQuotient.ofRaw (inverse z hz).val (inverse z hz).property
  change A*R=1 at hA
  change Z*S=1 at hZ
  change S + -R = -((R*(Z + -A))*S)
  grind

theorem remainder (a z : Scalar) (ha : Nonzero a) (hz : Nonzero z) :
    (sub (sub (inverse z hz).val (inverse a ha).val)
      (mul (derivative a ha).val (sub z.val a.val))).Equiv
      (mul (mul (mul (inverse a ha).val (inverse a ha).val)
        (mul (sub z.val a.val) (sub z.val a.val))) (inverse z hz).val) := by
  have hA := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid a.property (inverse a ha).property) (hright := ofQComplex_valid _) (mul_inverse a ha)
  have hZ := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (inverse z hz).property) (hright := ofQComplex_valid _) (mul_inverse z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (sub_valid (inverse z hz).property (inverse a ha).property)
      (mul_valid (derivative a ha).property (sub_valid z.property a.property)))
    (hright := mul_valid (mul_valid (mul_valid (inverse a ha).property (inverse a ha).property)
      (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property))) (inverse z hz).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw (inverse a ha).val (inverse a ha).property
  let S := ComplexRawQuotient.ofRaw (inverse z hz).val (inverse z hz).property
  change A*R=1 at hA
  change Z*S=1 at hZ
  change (S + -R) + -((-(R*R))*(Z + -A)) = ((R*R)*((Z + -A)*(Z + -A)))*S
  grind

theorem derivative_difference (a z : Scalar) (ha : Nonzero a) (hz : Nonzero z) :
    (sub (derivative z hz).val (derivative a ha).val).Equiv
      (neg (mul (add (inverse z hz).val (inverse a ha).val)
        (sub (inverse z hz).val (inverse a ha).val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (derivative z hz).property (derivative a ha).property)
    (hright := neg_valid (mul_valid (add_valid (inverse z hz).property (inverse a ha).property)
      (sub_valid (inverse z hz).property (inverse a ha).property)))
  let R := ComplexRawQuotient.ofRaw (inverse a ha).val (inverse a ha).property
  let S := ComplexRawQuotient.ofRaw (inverse z hz).val (inverse z hz).property
  change -(S*S) + -(-(R*R)) = -((S+R)*(S + -R))
  grind

theorem derivative_congr (a b : Scalar) (ha : Nonzero a) (hb : Nonzero b)
    (hab : a.val.Equiv b.val) : (derivative a ha).val.Equiv (derivative b hb).val :=
  neg_equiv (mul_equiv (inverse a ha).property (inverse b hb).property
    (inverse a ha).property (inverse b hb).property (inverse_congr a b ha hb hab) (inverse_congr a b ha hb hab))

end ComputableAnalysis.RiemannHilbert.ReciprocalDifference
