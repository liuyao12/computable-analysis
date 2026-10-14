import ComputableAnalysis.ModularForms.TauFiniteLambertIdentity

/-! Denominator-free finite differential identities for actual Euler products. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Clearing the justified finite reciprocal gives the actual derivative
identity in a form suited to passage through represented limits. -/
theorem finiteDiscriminantEulerSlope_lambert_identity (q : Scalar)
    (hq : tauEulerNomeDomain q) (N : Nat) :
    (mul q.val (finiteDiscriminantEulerSlope q N).val).Equiv
      (neg (scaleRat 24 (mul (finiteDiscriminantEulerProduct q N).val
        (ScalarSeries.block (weightedLambertTerm q (1/1024) 1) 0 N)))) := by
  let P := finiteDiscriminantEulerProduct q N
  let D := finiteDiscriminantEulerSlope q N
  let I := RepresentedReciprocal.inverse P (finiteDiscriminantEulerProduct_nonzero q hq N)
  have ht := weightedLambertTerm_valid q (1/1024) 1 (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq)
  let B : Scalar := ⟨ScalarSeries.block (weightedLambertTerm q (1/1024) 1) 0 N,
    ScalarSeries.block_valid _ ht 0 N⟩
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid P.property I.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse P
      (finiteDiscriminantEulerProduct_nonzero q hq N))
  have hl := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid q.property (finiteDiscriminantEulerLogarithmicSlope q hq N).property)
    (hright := neg_valid (scaleRat_valid B.property))
    (finiteDiscriminantEulerLogarithmicSlope_lambert q hq N)
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let i := ComplexRawQuotient.ofRaw I.val I.property
  let b := ComplexRawQuotient.ofRaw B.val B.property
  change p*i=1 at hi
  change Q*(d*i)= -(ComplexRawQuotient.scaleRat 24 b) at hl
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := mul_valid q.property D.property)
    (hright := neg_valid (scaleRat_valid (mul_valid P.property B.property)))
  change Q*d= -(ComplexRawQuotient.scaleRat 24 (p*b))
  calc Q*d = (Q*(d*i))*p := by
         calc Q*d = (Q*d)*(p*i) := by rw [hi]; grind only
              _ = (Q*(d*i))*p := by grind only
       _ = (-ComplexRawQuotient.scaleRat 24 b)*p := by rw [hl]
       _ = -(ComplexRawQuotient.scaleRat 24 (p*b)) := by
         rw [ComplexRawQuotient.neg_scaleRat,ComplexRawQuotient.neg_scaleRat,
           ←ComplexRawQuotient.scaleRat_mul]
         congr 1
         grind only

end ComputableAnalysis.ModularForms
