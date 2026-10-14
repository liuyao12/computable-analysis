import ComputableAnalysis.ModularForms.PairedPartialFraction

/-! Exact quotient form of the actual paired partial-fraction term. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedProduct (z a : Scalar) : Scalar :=
  ⟨sub (mul z.val z.val) (mul a.val a.val),
    sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)⟩

def pairedQuotient (z a : Scalar) (hm : NonzeroBoxSearch.Nonzero (pairedMinus z a))
    (hp : NonzeroBoxSearch.Nonzero (pairedPlus z a)) : Scalar :=
  ⟨mul (add z.val z.val)
      (RepresentedReciprocal.inverse (pairedProduct z a) (pairedProduct_nonzero z a hm hp)).val,
    mul_valid (add_valid z.property z.property)
      (RepresentedReciprocal.inverse (pairedProduct z a) (pairedProduct_nonzero z a hm hp)).property⟩

theorem pairedReciprocal_quotient (z a : Scalar)
    (hm : NonzeroBoxSearch.Nonzero (pairedMinus z a))
    (hp : NonzeroBoxSearch.Nonzero (pairedPlus z a)) :
    (pairedReciprocal z a hm hp).val.Equiv (pairedQuotient z a hm hp).val := by
  let I := RepresentedReciprocal.inverse (pairedProduct z a) (pairedProduct_nonzero z a hm hp)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedProduct z a).property I.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (pairedProduct z a) (pairedProduct_nonzero z a hm hp))
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedProduct z a).property (pairedReciprocal z a hm hp).property)
    (hright := add_valid z.property z.property) (pairedReciprocal_identity z a hm hp)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedReciprocal z a hm hp).property) (hright := (pairedQuotient z a hm hp).property)
  let D := ComplexRawQuotient.ofRaw (pairedProduct z a).val (pairedProduct z a).property
  let R := ComplexRawQuotient.ofRaw I.val I.property
  let S := ComplexRawQuotient.ofRaw (pairedReciprocal z a hm hp).val (pairedReciprocal z a hm hp).property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change D*R=1 at hi
  change D*S=Z+Z at hs
  change S=(Z+Z)*R
  grind only

theorem pairedReciprocal_congr (z w a b : Scalar)
    (hm : NonzeroBoxSearch.Nonzero (pairedMinus z a))
    (hp : NonzeroBoxSearch.Nonzero (pairedPlus z a))
    (hwm : NonzeroBoxSearch.Nonzero (pairedMinus w b))
    (hwp : NonzeroBoxSearch.Nonzero (pairedPlus w b))
    (hzw : z.val.Equiv w.val) (hab : a.val.Equiv b.val) :
    (pairedReciprocal z a hm hp).val.Equiv (pairedReciprocal w b hwm hwp).val :=
  add_equiv
    (RepresentedReciprocal.inverse_congr (pairedMinus z a) (pairedMinus w b) hm hwm
      (FunctionTheory.sub_congr hzw hab))
    (RepresentedReciprocal.inverse_congr (pairedPlus z a) (pairedPlus w b) hp hwp
      (add_equiv hzw hab))

end ComputableAnalysis.ModularForms
