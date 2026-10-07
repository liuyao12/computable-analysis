import ComputableAnalysis.ModularForms.PairedPoleReciprocal

/-! Exact integer periods of the actual reciprocal series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedUpperClass (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRawQuotient.Value :=
  ComplexRawQuotient.ofRaw (upperPairedPartialFractionValue z hz) (upperPairedPartialFractionValue_valid z hz)

theorem pairedUpperClass_congr (z w : Scalar) (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (he : z.val.Equiv w.val) : pairedUpperClass z hz=pairedUpperClass w hw :=
  ComplexRawQuotient.ofRaw_eq_ofRaw (pairedPartialFractionMap.eval_congr z w hz hw he)

theorem integerShiftScalar_zero (z : Scalar) : (integerShiftScalar z 0).val.Equiv z.val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (integerShiftScalar z 0).property) (hright := z.property)
  change ComplexRawQuotient.ofRaw (integerAffine 1 0 z.val) _ = _
  rw [integerAffine_class]
  grind only

theorem pairedUpperClass_period_nat (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) :
    pairedUpperClass (integerShiftScalar z (n:Int)) (integerShiftScalar_upper z hz _) = pairedUpperClass z hz := by
  induction n with
  | zero => exact pairedUpperClass_congr _ _ _ _ (integerShiftScalar_zero z)
  | succ n ih =>
    have hc := pairedUpperClass_congr _ _
      (integerShiftScalar_upper _ (integerShiftScalar_upper z hz (n:Int)) 1)
      (integerShiftScalar_upper z hz ((n:Int)+1)) (integerShiftScalar_composition z (n:Int) 1)
    have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := upperPairedPartialFractionValue_valid _
        (integerShiftScalar_upper _ (integerShiftScalar_upper z hz (n:Int)) 1))
      (hright := upperPairedPartialFractionValue_valid _ (integerShiftScalar_upper z hz (n:Int)))
      (upperPairedPartialFractionValue_period_one (integerShiftScalar z (n:Int)) (integerShiftScalar_upper z hz _))
    change pairedUpperClass (integerShiftScalar (integerShiftScalar z (n:Int)) 1) _ =
      pairedUpperClass (integerShiftScalar z (n:Int)) _ at hp
    rw [show ((n+1:Nat):Int)=(n:Int)+1 by omega]
    exact hc.symm.trans (hp.trans ih)

theorem pairedUpperClass_period_int (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Int) :
    pairedUpperClass (integerShiftScalar z k) (integerShiftScalar_upper z hz k) = pairedUpperClass z hz := by
  cases k with
  | ofNat n => exact pairedUpperClass_period_nat z hz n
  | negSucc n =>
    let w := integerShiftScalar z (Int.negSucc n)
    let hw := integerShiftScalar_upper z hz (Int.negSucc n)
    have hp := pairedUpperClass_period_nat w hw (n+1)
    have hc := pairedUpperClass_congr _ _ (integerShiftScalar_upper w hw ((n+1:Nat):Int))
      (integerShiftScalar_upper z hz 0) (by
        have h := integerShiftScalar_composition z (Int.negSucc n) ((n+1:Nat):Int)
        simpa only [show Int.negSucc n+((n+1:Nat):Int)=0 by omega] using h)
    have h0 := pairedUpperClass_congr _ z (integerShiftScalar_upper z hz 0) hz (integerShiftScalar_zero z)
    exact hp.symm.trans (hc.trans h0)

theorem upperPairedPartialFractionValue_period_int (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Int) :
    (upperPairedPartialFractionValue (integerShiftScalar z k) (integerShiftScalar_upper z hz k)).Equiv
      (upperPairedPartialFractionValue z hz) :=
  ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := upperPairedPartialFractionValue_valid _ _)
    (hright := upperPairedPartialFractionValue_valid _ _) (pairedUpperClass_period_int z hz k)

end ComputableAnalysis.ModularForms
