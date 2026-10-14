import ComputableAnalysis.ModularForms.TauWeightTwoExpansion

/-! Actual cusp derivative of the weight-two nome map. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def tauWeightTwoCuspSlope : Scalar := ⟨scaleRat (-24) one,scaleRat_valid (ofQComplex_valid _)⟩

/-- The expansion proves an actual derivative at every representation of zero. -/
def tauWeightTwoNomeMap_hasDerivativeAt_zero (a : Scalar) (ha : tauEulerNomeDomain a)
    (ha0 : a.val.Equiv zero) : HasDerivativeAt tauWeightTwoNomeMap a ha tauWeightTwoCuspSlope where
  delta eps := minRadius ⟨1/1024,by decide +kernel⟩ (divideRadius eps ⟨3841,by decide +kernel⟩)
  estimate eps H z hz hd hza := by
    have hHmax : H.val≤(1:Rat)/1024 := Rat.le_trans hd (minRadius_left _ _)
    have hHeps := Rat.le_trans hd (minRadius_right ⟨1/1024,by decide +kernel⟩
      (divideRadius eps ⟨3841,by decide +kernel⟩))
    have haQ := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := a.property) (hright := ofQComplex_valid _) ha0
    have hez : (sub z.val a.val).Equiv z.val := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := sub_valid z.property a.property) (hright := z.property)
      let Z := ComplexRawQuotient.ofRaw z.val z.property
      let A := ComplexRawQuotient.ofRaw a.val a.property
      change A=0 at haQ
      change Z-A=Z
      rw [haQ]
      grind only
    have hzH : Small z.val H.val := Small.congr (sub_valid z.property a.property) z.property hez hza
    have hb := tauWeightTwoNomeValue_linear_bound z hz H.val (Rat.le_of_lt H.property) hHmax hzH
    have hEa := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (tauWeightTwoNomeValue a ha).property)
      (hright := ofQComplex_valid _) (tauWeightTwoNomeValue_at_zero a ha ha0)
    have he : (sub (tauWeightTwoNomeValue z hz).val (sub one (scaleRat 24 z.val))).Equiv
        (DomainFunctions.remainder tauWeightTwoNomeMap a ha tauWeightTwoCuspSlope z hz) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid (tauWeightTwoNomeValue z hz).property
          (sub_valid (ofQComplex_valid _) (scaleRat_valid z.property)))
        (hright := DomainFunctions.remainder_valid _ _ _ _ _ _)
      let E := ComplexRawQuotient.ofRaw (tauWeightTwoNomeValue z hz).val (tauWeightTwoNomeValue z hz).property
      let EA := ComplexRawQuotient.ofRaw (tauWeightTwoNomeValue a ha).val (tauWeightTwoNomeValue a ha).property
      let Z := ComplexRawQuotient.ofRaw z.val z.property
      let A := ComplexRawQuotient.ofRaw a.val a.property
      change A=0 at haQ
      change EA=1 at hEa
      change E-(1-ComplexRawQuotient.scaleRat 24 Z)=(E-EA)-(ComplexRawQuotient.scaleRat (-24) 1)*(Z-A)
      rw [haQ,hEa,←ComplexRawQuotient.scaleRat_mul]
      have hs : ComplexRawQuotient.scaleRat (-24) Z= -(ComplexRawQuotient.scaleRat 24 Z) :=
        (ComplexRawQuotient.neg_scaleRat 24 Z).symm
      have h1 : (1:ComplexRawQuotient.Value)*(Z-0)=Z := by grind only
      rw [h1,hs]
      grind only
    have h := Small.congr
      (sub_valid (tauWeightTwoNomeValue z hz).property (sub_valid (ofQComplex_valid _) (scaleRat_valid z.property)))
      (DomainFunctions.remainder_valid _ _ _ _ _ _) he hb
    have hi := divideRadius_identity eps ⟨3841,by decide +kernel⟩
    have hm := Rat.mul_le_mul_of_nonneg_right hHeps (show (0:Rat)≤3841 by decide +kernel)
    have hcoef : 3840*H.val≤eps.val := by have hp := H.property; grind only
    have hf := Rat.mul_le_mul_of_nonneg_right hcoef (Rat.le_of_lt H.property)
    exact h.mono (by grind only)

end ComputableAnalysis.ModularForms
