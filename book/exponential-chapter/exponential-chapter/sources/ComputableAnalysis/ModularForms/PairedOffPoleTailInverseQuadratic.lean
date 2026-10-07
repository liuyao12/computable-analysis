import ComputableAnalysis.ModularForms.PairedOffPoleTailRemainderIdentity

/-! Exact quadratic expression for the actual squared-denominator reciprocal remainder. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailInverseQuadratic (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) : Scalar :=
  let i := pairedOffPoleTailInverse B n a ha
  let j := pairedOffPoleTailInverse B n z hz
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let d : Scalar := ⟨sub (mul z.val z.val) (mul a.val a.val),
    sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)⟩
  ⟨sub (mul (mul (mul i.val i.val) (mul d.val d.val)) j.val)
      (mul (mul i.val i.val) (mul h.val h.val)),
    sub_valid (mul_valid (mul_valid (mul_valid i.property i.property) (mul_valid d.property d.property)) j.property)
      (mul_valid (mul_valid i.property i.property) (mul_valid h.property h.property))⟩

theorem pairedOffPoleTailInverse_remainder_quadratic (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) :
    (pairedOffPoleTailInverseRemainder B n a z ha hz).val.Equiv
      (pairedOffPoleTailInverseQuadratic B n a z ha hz).val := by
  let k := pairedTailShift B n
  let p := pairedLiteralDenominator a (pairedIntegerSquare k)
  let q := pairedLiteralDenominator z (pairedIntegerSquare k)
  have hk : 0<k := by dsimp [k,pairedTailShift]; omega
  let hp := pairedIntegerDenominator_nonzero a (B:Rat) k Rat.natCast_nonneg
    (LocalODE.interior_bound _ a ha) hk (pairedTailShift_large B n)
  let hq := pairedIntegerDenominator_nonzero z (B:Rat) k Rat.natCast_nonneg
    (LocalODE.interior_bound _ z hz) hk (pairedTailShift_large B n)
  let i := RepresentedReciprocal.inverse p hp
  let j := RepresentedReciprocal.inverse q hq
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := sub_valid (sub_valid j.property i.property)
      (mul_valid (ReciprocalDifference.derivative p hp).property (sub_valid q.property p.property)))
    (hright := mul_valid (mul_valid (mul_valid i.property i.property)
      (mul_valid (sub_valid q.property p.property) (sub_valid q.property p.property))) j.property)
    (ReciprocalDifference.remainder p q hp hq)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedOffPoleTailInverseRemainder B n a z ha hz).property)
    (hright := (pairedOffPoleTailInverseQuadratic B n a z ha hz).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw i.val i.property
  let J := ComplexRawQuotient.ofRaw j.val j.property
  let K := ComplexRawQuotient.ofQComplex ⟨pairedIntegerSquare k,0⟩
  change (J-I)-(-(I*I)*((Z*Z-K)-(A*A-K)))=
    ((I*I)*(((Z*Z-K)-(A*A-K))*((Z*Z-K)-(A*A-K))))*J at hr
  change (J-I)-(-(I*I*(A+A)))*(Z-A)=
    ((I*I)*((Z*Z-A*A)*(Z*Z-A*A)))*J-(I*I)*((Z-A)*(Z-A))
  grind only

end ComputableAnalysis.ModularForms
