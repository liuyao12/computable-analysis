import ComputableAnalysis.ModularForms.TauBaseLambertAgreement
import ComputableAnalysis.ModularForms.LambertWeightBound

/-! Exact weighted Lambert terms for Euler logarithmic factors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem scale_neg (c : Rat) (x : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat c (-x)= -(ComplexRawQuotient.scaleRat c x) := by
  rw [ComplexRawQuotient.neg_eq_scaleRat_neg_one,ComplexRawQuotient.scaleRat_scaleRat,
    ComplexRawQuotient.neg_scaleRat]
  have he : c*(-1)= -c := by grind only
  rw [he]

/-- Multiplication by the nome turns the actual factor slope into the
existing degree-one weighted Lambert term, including the factor at index zero. -/
theorem tauEulerFactorLogarithmicSlope_lambert_term (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    (mul q.val (tauEulerFactorLogarithmicSlope q hq N).val).Equiv
      (neg (scaleRat 24 (weightedLambertTerm q (1/1024) 1 N))) := by
  let I := RepresentedReciprocal.inverse ((tauEulerFactorMap N).eval q trivial)
    (tauEulerBaseFactor_nonzero q hq N)
  have hp := LocalODE.power_valid q.val q.property N
  have hlv := nomeLambertPower_valid q (1/1024) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) N
  have ht := weightedLambertTerm_valid q (1/1024) 1 (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) N
  have hl := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := hlv)
    (hright := mul_valid (LocalODE.power_valid _ q.property (N+1)) I.property)
    (nomeLambertPower_euler_reciprocal q hq N)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (tauEulerFactorLogarithmicSlope q hq N).property)
    (hright := (tauEulerFactorBaseQuotient q hq N).property)
    (tauEulerFactorLogarithmicSlope_quotient q hq N)
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let p := ComplexRawQuotient.ofRaw (LocalODE.power q.val N) hp
  let i := ComplexRawQuotient.ofRaw I.val I.property
  let l := ComplexRawQuotient.ofRaw (nomeLambertPower q (1/1024) N) hlv
  let d := ComplexRawQuotient.ofRaw (tauEulerFactorLogarithmicSlope q hq N).val
    (tauEulerFactorLogarithmicSlope q hq N).property
  change l=(p*Q)*i at hl
  change d=ComplexRawQuotient.scaleRat 24 ((-ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) p)*i) at hd
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid q.property (tauEulerFactorLogarithmicSlope q hq N).property)
    (hright := neg_valid (scaleRat_valid ht))
  change Q*d= -(ComplexRawQuotient.scaleRat 24 (ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^1) l))
  rw [Rat.pow_one,hd,hl,ComplexRawQuotient.mul_scaleRat]
  have he : Q*((-ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) p)*i)=
      -(ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) ((p*Q)*i)) := by
    rw [ComplexRawQuotient.neg_scaleRat,ComplexRawQuotient.neg_scaleRat,
      ←ComplexRawQuotient.scaleRat_mul,ComplexRawQuotient.mul_scaleRat]
    congr 1
    grind only
  rw [he,scale_neg]

end ComputableAnalysis.ModularForms
