import ComputableAnalysis.ModularForms.PairedOffPoleTailDerivativeContinuity

/-! Exact first-order remainders for actual rational off-pole tail terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailInverseRemainder (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) : Scalar :=
  let i := pairedOffPoleTailInverse B n a ha
  let j := pairedOffPoleTailInverse B n z hz
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let d : Scalar := ⟨neg (mul (mul i.val i.val) (add a.val a.val)),
    neg_valid (mul_valid (mul_valid i.property i.property) (add_valid a.property a.property))⟩
  ⟨sub (sub j.val i.val) (mul d.val h.val),
    sub_valid (sub_valid j.property i.property) (mul_valid d.property h.property)⟩

def pairedOffPoleTailTermRemainder (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) : Scalar :=
  let i := pairedOffPoleTailInverse B n a ha
  let j := pairedOffPoleTailInverse B n z hz
  let r := pairedOffPoleTailInverseRemainder B n a z ha hz
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  ⟨add (mul (add a.val a.val) r.val) (mul (add h.val h.val) (sub j.val i.val)),
    add_valid (mul_valid (add_valid a.property a.property) r.property)
      (mul_valid (add_valid h.property h.property) (sub_valid j.property i.property))⟩

theorem pairedOffPoleTailTerm_remainder_identity (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) :
    (DomainFunctions.remainder (pairedOffPoleTailTermMap B n) a ha
      (pairedOffPoleTailDerivativeTerm B n a ha) z hz).Equiv
      (pairedOffPoleTailTermRemainder B n a z ha hz).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _)
    (hright := (pairedOffPoleTailTermRemainder B n a z ha hz).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (pairedOffPoleTailInverse B n a ha).val
    (pairedOffPoleTailInverse B n a ha).property
  let J := ComplexRawQuotient.ofRaw (pairedOffPoleTailInverse B n z hz).val
    (pairedOffPoleTailInverse B n z hz).property
  change ((Z+Z)*J-(A+A)*I)-((I+I)-((A+A)*(A+A))*(I*I))*(Z-A)=
    (A+A)*((J-I)-(-(I*I*(A+A)))*(Z-A))+((Z-A)+(Z-A))*(J-I)
  grind only

end ComputableAnalysis.ModularForms
