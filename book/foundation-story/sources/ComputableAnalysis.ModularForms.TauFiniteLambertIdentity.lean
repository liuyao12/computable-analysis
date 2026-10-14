import ComputableAnalysis.ModularForms.TauLogarithmicLambertTerm
import ComputableAnalysis.ModularForms.WeightedLambertSeries

/-! Exact weighted Lambert prefixes for finite Euler logarithmic derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Summing the actual factor identities gives the existing weighted Lambert prefix. -/
theorem tauEulerFactorLogarithmicSum_lambert (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    (mul q.val (tauEulerFactorLogarithmicSum q hq N).val).Equiv
      (neg (scaleRat 24 (ScalarSeries.block (weightedLambertTerm q (1/1024) 1) 0 N))) := by
  have ht := weightedLambertTerm_valid q (1/1024) 1 (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq)
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid q.property (tauEulerFactorLogarithmicSum q hq 0).property)
      (hright := neg_valid (scaleRat_valid (ScalarSeries.block_valid _ ht 0 0)))
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change Q*0= -(ComplexRawQuotient.scaleRat 24 0)
    have hs := ComplexRawQuotient.scaleRat_zero (24:Rat)
    have hz : Q*0 = -(0:ComplexRawQuotient.Value) := by grind only
    exact Eq.mpr (congrArg (fun x => Q*0 = -x) hs) hz
  | succ N ih =>
    let S := tauEulerFactorLogarithmicSum q hq N
    let F := tauEulerFactorLogarithmicSlope q hq N
    let B : Scalar := ⟨ScalarSeries.block (weightedLambertTerm q (1/1024) 1) 0 N,
      ScalarSeries.block_valid _ ht 0 N⟩
    let T : Scalar := ⟨weightedLambertTerm q (1/1024) 1 N,ht N⟩
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid q.property S.property)
      (hright := neg_valid (scaleRat_valid B.property)) ih
    have hf := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid q.property F.property)
      (hright := neg_valid (scaleRat_valid T.property))
      (tauEulerFactorLogarithmicSlope_lambert_term q hq N)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid q.property (tauEulerFactorLogarithmicSum q hq (N+1)).property)
      (hright := neg_valid (scaleRat_valid (ScalarSeries.block_valid _ ht 0 (N+1))))
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    let s := ComplexRawQuotient.ofRaw S.val S.property
    let f := ComplexRawQuotient.ofRaw F.val F.property
    let b := ComplexRawQuotient.ofRaw B.val B.property
    let t := ComplexRawQuotient.ofRaw T.val T.property
    change Q*s= -(ComplexRawQuotient.scaleRat 24 b) at hi
    change Q*f= -(ComplexRawQuotient.scaleRat 24 t) at hf
    simp only [ScalarSeries.block,Nat.zero_add]
    change Q*(s+f)= -(ComplexRawQuotient.scaleRat 24 (b+t))
    rw [ComplexRawQuotient.scaleRat_add]
    calc Q*(s+f) = Q*s+Q*f := by grind only
         _ = -(ComplexRawQuotient.scaleRat 24 b+ComplexRawQuotient.scaleRat 24 t) := by rw [hi,hf]; grind only

/-- Exact finite Lambert identity for the actual whole-product logarithmic slope. -/
theorem finiteDiscriminantEulerLogarithmicSlope_lambert (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    (mul q.val (finiteDiscriminantEulerLogarithmicSlope q hq N).val).Equiv
      (neg (scaleRat 24 (ScalarSeries.block (weightedLambertTerm q (1/1024) 1) 0 N))) := by
  have ht := weightedLambertTerm_valid q (1/1024) 1 (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq)
  exact equiv_trans
    (mul_valid q.property (finiteDiscriminantEulerLogarithmicSlope q hq N).property)
    (mul_valid q.property (tauEulerFactorLogarithmicSum q hq N).property)
    (neg_valid (scaleRat_valid (ScalarSeries.block_valid _ ht 0 N)))
    (mul_equiv q.property q.property (finiteDiscriminantEulerLogarithmicSlope q hq N).property
      (tauEulerFactorLogarithmicSum q hq N).property (equiv_refl _ q.property)
      (finiteDiscriminantEulerLogarithmicSlope_sum q hq N))
    (tauEulerFactorLogarithmicSum_lambert q hq N)

end ComputableAnalysis.ModularForms
