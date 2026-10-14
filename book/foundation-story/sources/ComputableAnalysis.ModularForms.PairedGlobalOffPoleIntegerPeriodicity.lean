import ComputableAnalysis.ModularForms.PairedGlobalOffPolePeriodOne

/-! Exact integer periods of the actual reciprocal series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def globalOffPoleClass (z : Scalar) (hz : pairedOffPoleDomain z) : ComplexRawQuotient.Value :=
  ComplexRawQuotient.ofRaw (globalOffPoleValue z hz) (globalOffPoleValue_valid z hz)

theorem globalOffPoleClass_congr (z w : Scalar) (hz : pairedOffPoleDomain z) (hw : pairedOffPoleDomain w)
    (he : z.val.Equiv w.val) : globalOffPoleClass z hz=globalOffPoleClass w hw :=
  ComplexRawQuotient.ofRaw_eq_ofRaw (pairedGlobalOffPoleAssemblyMap.eval_congr z w hz hw he)

theorem globalOffPoleClass_period_nat (z : Scalar) (hz : pairedOffPoleDomain z) (n : Nat) :
    globalOffPoleClass (integerShiftScalar z (n:Int)) (pairedOffPoleDomain_shift z hz _) = globalOffPoleClass z hz := by
  induction n with
  | zero => exact globalOffPoleClass_congr _ _ _ _ (integerShiftScalar_zero_equiv z)
  | succ n ih =>
    have hc := globalOffPoleClass_congr _ _
      (pairedOffPoleDomain_shift _ (pairedOffPoleDomain_shift z hz (n:Int)) 1)
      (pairedOffPoleDomain_shift z hz ((n:Int)+1)) (integerShiftScalar_composition z (n:Int) 1)
    have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := globalOffPoleValue_valid _
        (pairedOffPoleDomain_shift _ (pairedOffPoleDomain_shift z hz (n:Int)) 1))
      (hright := globalOffPoleValue_valid _ (pairedOffPoleDomain_shift z hz (n:Int)))
      (globalOffPoleValue_period_one (integerShiftScalar z (n:Int)) (pairedOffPoleDomain_shift z hz _))
    change globalOffPoleClass (integerShiftScalar (integerShiftScalar z (n:Int)) 1) _ =
      globalOffPoleClass (integerShiftScalar z (n:Int)) _ at hp
    rw [show ((n+1:Nat):Int)=(n:Int)+1 by omega]
    exact hc.symm.trans (hp.trans ih)

theorem globalOffPoleClass_period_int (z : Scalar) (hz : pairedOffPoleDomain z) (k : Int) :
    globalOffPoleClass (integerShiftScalar z k) (pairedOffPoleDomain_shift z hz k) = globalOffPoleClass z hz := by
  cases k with
  | ofNat n => exact globalOffPoleClass_period_nat z hz n
  | negSucc n =>
    let w := integerShiftScalar z (Int.negSucc n)
    let hw := pairedOffPoleDomain_shift z hz (Int.negSucc n)
    have hp := globalOffPoleClass_period_nat w hw (n+1)
    have hc := globalOffPoleClass_congr _ _ (pairedOffPoleDomain_shift w hw ((n+1:Nat):Int))
      (pairedOffPoleDomain_shift z hz 0) (by
        have h := integerShiftScalar_composition z (Int.negSucc n) ((n+1:Nat):Int)
        simpa only [show Int.negSucc n+((n+1:Nat):Int)=0 by omega] using h)
    have h0 := globalOffPoleClass_congr _ z (pairedOffPoleDomain_shift z hz 0) hz (integerShiftScalar_zero_equiv z)
    exact hp.symm.trans (hc.trans h0)

theorem globalOffPoleValue_period_int (z : Scalar) (hz : pairedOffPoleDomain z) (k : Int) :
    (globalOffPoleValue (integerShiftScalar z k) (pairedOffPoleDomain_shift z hz k)).Equiv
      (globalOffPoleValue z hz) :=
  ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := globalOffPoleValue_valid _ _)
    (hright := globalOffPoleValue_valid _ _) (globalOffPoleClass_period_int z hz k)

end ComputableAnalysis.ModularForms
