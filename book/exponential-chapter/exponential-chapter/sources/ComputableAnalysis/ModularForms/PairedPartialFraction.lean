import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! Exact paired partial-fraction algebra for actual represented reciprocals. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedMinus (z a : Scalar) : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
def pairedPlus (z a : Scalar) : Scalar := ⟨add z.val a.val,add_valid z.property a.property⟩

def pairedReciprocal (z a : Scalar) (hm : NonzeroBoxSearch.Nonzero (pairedMinus z a))
    (hp : NonzeroBoxSearch.Nonzero (pairedPlus z a)) : Scalar :=
  ⟨add (RepresentedReciprocal.inverse (pairedMinus z a) hm).val
    (RepresentedReciprocal.inverse (pairedPlus z a) hp).val,
    add_valid (RepresentedReciprocal.inverse (pairedMinus z a) hm).property
      (RepresentedReciprocal.inverse (pairedPlus z a) hp).property⟩

theorem pairedReciprocal_identity (z a : Scalar)
    (hm : NonzeroBoxSearch.Nonzero (pairedMinus z a))
    (hp : NonzeroBoxSearch.Nonzero (pairedPlus z a)) :
    (mul (sub (mul z.val z.val) (mul a.val a.val)) (pairedReciprocal z a hm hp).val).Equiv
      (add z.val z.val) := by
  let M := RepresentedReciprocal.inverse (pairedMinus z a) hm
  let P := RepresentedReciprocal.inverse (pairedPlus z a) hp
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedMinus z a).property M.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (pairedMinus z a) hm)
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedPlus z a).property P.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (pairedPlus z a) hp)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property))
      (pairedReciprocal z a hm hp).property)
    (hright := add_valid z.property z.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let U := ComplexRawQuotient.ofRaw M.val M.property
  let V := ComplexRawQuotient.ofRaw P.val P.property
  change (Z-A)*U=1 at hi
  change (Z+A)*V=1 at hj
  change (Z*Z-A*A)*(U+V)=Z+Z
  grind only

theorem pairedProduct_nonzero (z a : Scalar)
    (hm : NonzeroBoxSearch.Nonzero (pairedMinus z a))
    (hp : NonzeroBoxSearch.Nonzero (pairedPlus z a)) :
    NonzeroBoxSearch.Nonzero
      ⟨sub (mul z.val z.val) (mul a.val a.val),
        sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)⟩ := by
  let M := RepresentedReciprocal.inverse (pairedMinus z a) hm
  let P := RepresentedReciprocal.inverse (pairedPlus z a) hp
  apply RepresentedReciprocal.nonzero_of_inverse _ ⟨mul M.val P.val,mul_valid M.property P.property⟩
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedMinus z a).property M.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (pairedMinus z a) hm)
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedPlus z a).property P.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (pairedPlus z a) hp)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property))
      (mul_valid M.property P.property)) (hright := ofQComplex_valid _)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let U := ComplexRawQuotient.ofRaw M.val M.property
  let V := ComplexRawQuotient.ofRaw P.val P.property
  change (Z-A)*U=1 at hi
  change (Z+A)*V=1 at hj
  change (Z*Z-A*A)*(U*V)=1
  grind only

end ComputableAnalysis.ModularForms
