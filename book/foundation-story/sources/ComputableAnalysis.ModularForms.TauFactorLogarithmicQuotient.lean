import ComputableAnalysis.ModularForms.TauFiniteLogarithmicRule

/-! Explicit base-denominator quotients for actual Euler logarithmic factors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The executable base quotient for the logarithmic derivative of a degree-24 factor. -/
def tauEulerFactorBaseQuotient (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) : Scalar :=
  let B := (tauEulerFactorMap N).eval q trivial
  let I := RepresentedReciprocal.inverse B (tauEulerBaseFactor_nonzero q hq N)
  ⟨scaleRat 24 (mul (neg (scaleRat ((N+1:Nat):Rat) (LocalODE.power q.val N))) I.val),
    scaleRat_valid (mul_valid (neg_valid (scaleRat_valid (LocalODE.power_valid _ q.property N))) I.property)⟩

/-- Cancellation of the factor's 23rd power gives its actual base quotient. -/
theorem tauEulerFactorLogarithmicSlope_quotient (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    (tauEulerFactorLogarithmicSlope q hq N).val.Equiv (tauEulerFactorBaseQuotient q hq N).val := by
  let B := (tauEulerFactorMap N).eval q trivial
  let I := RepresentedReciprocal.inverse B (tauEulerBaseFactor_nonzero q hq N)
  let F := tauEulerFactorValue q N
  let J := RepresentedReciprocal.inverse F (tauEulerFactorValue_nonzero q hq N)
  let D : Scalar := ⟨neg (scaleRat ((N+1:Nat):Rat) (LocalODE.power q.val N)),
    neg_valid (scaleRat_valid (LocalODE.power_valid _ q.property N))⟩
  have hp := LocalODE.power_valid B.val B.property 23
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid B.property I.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse B (tauEulerBaseFactor_nonzero q hq N))
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid F.property J.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse F (tauEulerFactorValue_nonzero q hq N))
  let b := ComplexRawQuotient.ofRaw B.val B.property
  let i := ComplexRawQuotient.ofRaw I.val I.property
  let j := ComplexRawQuotient.ofRaw J.val J.property
  let p := ComplexRawQuotient.ofRaw (LocalODE.power B.val 23) hp
  let d := ComplexRawQuotient.ofRaw D.val D.property
  change b*i=1 at hi
  change (p*b)*j=1 at hj
  have hc : p*j=i := by
    calc p*j = (p*j)*(b*i) := by rw [hi]; grind only
         _ = ((p*b)*j)*i := by grind only
         _ = i := by rw [hj]; grind only
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (tauEulerFactorLogarithmicSlope q hq N).property)
    (hright := (tauEulerFactorBaseQuotient q hq N).property)
  change ComplexRawQuotient.scaleRat 24 (p*d)*j=ComplexRawQuotient.scaleRat 24 (d*i)
  rw [←ComplexRawQuotient.scaleRat_mul]
  have he : (p*d)*j=d*i := by
    calc (p*d)*j = d*(p*j) := by grind only
         _ = d*i := by rw [hc]
  rw [he]

end ComputableAnalysis.ModularForms
