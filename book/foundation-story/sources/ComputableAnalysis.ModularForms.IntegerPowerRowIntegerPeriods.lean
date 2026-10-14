import ComputableAnalysis.ModularForms.IntegerPowerRowPeriodicity
import ComputableAnalysis.ModularForms.PairedIntegerPeriodicity

/-! All integer periods of actual reciprocal-power row sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def integerPowerRowClass (z : Scalar) (hz : InUpperHalfPlane z.val) (d : Nat) (hd : 2≤d) : ComplexRawQuotient.Value :=
  ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz d hd).val
    (integerReciprocalPowerRowSum z hz d hd).property

theorem integerPowerRowClass_congr (z w : Scalar) (hz : InUpperHalfPlane z.val)
    (hw : InUpperHalfPlane w.val) (d : Nat) (hd : 2≤d) (he : z.val.Equiv w.val) :
    integerPowerRowClass z hz d hd=integerPowerRowClass w hw d hd :=
  ComplexRawQuotient.ofRaw_eq_ofRaw (integerReciprocalPowerRowSum_congr z w hz hw he d hd)

theorem integerPowerRowClass_period_nat (z : Scalar) (hz : InUpperHalfPlane z.val) (d : Nat) (hd : 2≤d) (n : Nat) :
    integerPowerRowClass (integerShiftScalar z (n:Int)) (integerShiftScalar_upper z hz _) d hd = integerPowerRowClass z hz d hd := by
  induction n with
  | zero => exact integerPowerRowClass_congr _ _ _ _ d hd (integerShiftScalar_zero z)
  | succ n ih =>
    have hc := integerPowerRowClass_congr _ _
      (integerShiftScalar_upper _ (integerShiftScalar_upper z hz (n:Int)) 1)
      (integerShiftScalar_upper z hz ((n:Int)+1)) d hd (integerShiftScalar_composition z (n:Int) 1)
    have hp : integerPowerRowClass (integerShiftScalar (integerShiftScalar z (n:Int)) 1)
        (integerShiftScalar_upper _ (integerShiftScalar_upper z hz (n:Int)) 1) d hd =
        integerPowerRowClass (integerShiftScalar z (n:Int)) (integerShiftScalar_upper z hz (n:Int)) d hd :=
      ComplexRawQuotient.ofRaw_eq_ofRaw
      (integerReciprocalPowerRowSum_period_one (integerShiftScalar z (n:Int))
        (integerShiftScalar_upper z hz _) d hd)
    change integerPowerRowClass (integerShiftScalar (integerShiftScalar z (n:Int)) 1) _ d hd =
      integerPowerRowClass (integerShiftScalar z (n:Int)) _ d hd at hp
    rw [show ((n+1:Nat):Int)=(n:Int)+1 by omega]
    exact hc.symm.trans (hp.trans ih)

theorem integerPowerRowClass_period_int (z : Scalar) (hz : InUpperHalfPlane z.val) (d : Nat) (hd : 2≤d) (k : Int) :
    integerPowerRowClass (integerShiftScalar z k) (integerShiftScalar_upper z hz k) d hd = integerPowerRowClass z hz d hd := by
  cases k with
  | ofNat n => exact integerPowerRowClass_period_nat z hz d hd n
  | negSucc n =>
    let w := integerShiftScalar z (Int.negSucc n)
    let hw := integerShiftScalar_upper z hz (Int.negSucc n)
    have hp := integerPowerRowClass_period_nat w hw d hd (n+1)
    have hc := integerPowerRowClass_congr _ _ (integerShiftScalar_upper w hw ((n+1:Nat):Int))
      (integerShiftScalar_upper z hz 0) d hd (by
        have h := integerShiftScalar_composition z (Int.negSucc n) ((n+1:Nat):Int)
        simpa only [show Int.negSucc n+((n+1:Nat):Int)=0 by omega] using h)
    have h0 := integerPowerRowClass_congr _ z (integerShiftScalar_upper z hz 0) hz d hd (integerShiftScalar_zero z)
    exact hp.symm.trans (hc.trans h0)

theorem integerReciprocalPowerRowSum_period_int (z : Scalar) (hz : InUpperHalfPlane z.val)
    (d : Nat) (hd : 2≤d) (k : Int) :
    (integerReciprocalPowerRowSum (integerShiftScalar z k) (integerShiftScalar_upper z hz k) d hd).val.Equiv
      (integerReciprocalPowerRowSum z hz d hd).val :=
  ComplexRawQuotient.equiv_of_ofRaw_eq (integerPowerRowClass_period_int z hz d hd k)

end ComputableAnalysis.ModularForms
