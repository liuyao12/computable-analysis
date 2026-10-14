import ComputableAnalysis.ModularForms.IndexedBoundaryDecay
import ComputableAnalysis.RiemannHilbert.ReciprocalDifference

/-! Summable bounds for the actual derivatives of paired reciprocal terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedDerivative_reciprocalSquare_eq_inverse_product (n : Nat) (hn : 0<n) :
    reciprocalSquare n=(n:Rat)⁻¹*(n:Rat)⁻¹ := by
  have hp : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  have hi := Rat.mul_inv_cancel (n:Rat) (Rat.ne_of_gt hp)
  have hs := Rat.mul_inv_cancel ((n:Rat)*(n:Rat)) (Rat.ne_of_gt (Rat.mul_pos hp hp))
  have ht : ((n:Rat)*(n:Rat))*((n:Rat)⁻¹*(n:Rat)⁻¹)=1 := by
    calc
      _ = ((n:Rat)*(n:Rat)⁻¹)*((n:Rat)*(n:Rat)⁻¹) := by grind only
      _ = 1 := by rw [hi]; decide +kernel
  unfold reciprocalSquare
  calc
    _ = ((n:Rat)*(n:Rat))⁻¹*(((n:Rat)*(n:Rat))*((n:Rat)⁻¹*(n:Rat)⁻¹)) := by rw [ht,Rat.mul_one]
    _ = (((n:Rat)*(n:Rat))*((n:Rat)*(n:Rat))⁻¹)*((n:Rat)⁻¹*(n:Rat)⁻¹) := by grind only
    _ = (n:Rat)⁻¹*(n:Rat)⁻¹ := by rw [hs,Rat.one_mul]

theorem pairedDerivative_reciprocalSquare_antitone (m n : Nat) (hm : 0<m) (hmn : m≤n) :
    reciprocalSquare n≤reciprocalSquare m := by
  have hp : (0:Rat)<(m:Rat) := by exact_mod_cast hm
  have hq : (0:Rat)<(n:Rat) := by exact_mod_cast (show 0<n by omega)
  have hmnR : (m:Rat)≤(n:Rat) := by exact_mod_cast hmn
  have h1 := Rat.mul_le_mul_of_nonneg_right hmnR (Rat.le_of_lt hp)
  have h2 := Rat.mul_le_mul_of_nonneg_left hmnR (Rat.le_of_lt hq)
  have hs : (m:Rat)*(m:Rat)≤(n:Rat)*(n:Rat) := Rat.le_trans h1 h2
  have cm := Rat.mul_inv_cancel ((m:Rat)*(m:Rat)) (Rat.ne_of_gt (Rat.mul_pos hp hp))
  have cn := Rat.mul_inv_cancel ((n:Rat)*(n:Rat)) (Rat.ne_of_gt (Rat.mul_pos hq hq))
  unfold reciprocalSquare
  apply Rat.le_of_mul_le_mul_right (c := ((m:Rat)*(m:Rat))*((n:Rat)*(n:Rat)))
  · calc
      _ = (m:Rat)*(m:Rat) := by grind only
      _ ≤ (n:Rat)*(n:Rat) := hs
      _ = _ := by grind only
  · exact Rat.mul_pos (Rat.mul_pos hp hp) (Rat.mul_pos hq hq)

def upperPairedReciprocalDerivative (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) : Scalar :=
  DomainFunctions.scalarSum
    (ReciprocalDifference.derivative (pairedMinus z (boundaryIntegerScalar n))
      (upperShiftMinus_nonzero z hz (n:Rat)))
    (ReciprocalDifference.derivative (pairedPlus z (boundaryIntegerScalar n))
      (upperShiftPlus_nonzero z hz (n:Rat)))

theorem upperPairedReciprocalDerivative_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) (hRn : R≤(n:Rat)) :
    Small (upperPairedReciprocalDerivative z hz n).val (1024*reciprocalSquare n) := by
  have hm := (integerBoundaryMinus_bound z hz R hR hsmall n hn hlarge).mono
    (integerBoundaryRate_le R n hn hRn)
  have hp := (integerBoundaryPlus_bound z hz R hR hsmall n hn hlarge).mono
    (integerBoundaryRate_le R n hn hRn)
  have hM : 0≤16*(1/(n:Rat)) := by
    have hnR : (0:Rat)<(n:Rat) := by exact_mod_cast hn
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hnR))
  let I := RepresentedReciprocal.inverse (pairedMinus z (boundaryIntegerScalar n))
    (upperShiftMinus_nonzero z hz (n:Rat))
  let J := RepresentedReciprocal.inverse (pairedPlus z (boundaryIntegerScalar n))
    (upperShiftPlus_nonzero z hz (n:Rat))
  have h := LocalODE.small_add
    (SeriesLimitLaws.small_neg (Small.mul I.property I.property hM hM hm hm))
    (SeriesLimitLaws.small_neg (Small.mul J.property J.property hM hM hp hp))
  have he : (2:Rat)*(16*(1/(n:Rat)))*(16*(1/(n:Rat))) +
      2*(16*(1/(n:Rat)))*(16*(1/(n:Rat)))=1024*reciprocalSquare n := by
    rw [pairedDerivative_reciprocalSquare_eq_inverse_product n hn,Rat.div_def,Rat.one_mul]
    grind only
  rw [he] at h
  exact h

def pairedDerivativeTailTerm (z : Scalar) (hz : InUpperHalfPlane z.val) (B n : Nat) : Scalar :=
  upperPairedReciprocalDerivative z hz (pairedTailShift B n)

theorem pairedDerivativeTailTerm_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (n : Nat) :
    Small (pairedDerivativeTailTerm z hz B n).val (((1024:Nat):Rat)*reciprocalSquare (n+1)) := by
  have hk : 0<pairedTailShift B n := by unfold pairedTailShift; omega
  have hBk : (B:Rat)≤((pairedTailShift B n):Rat) := by
    exact_mod_cast (show B≤pairedTailShift B n by unfold pairedTailShift; omega)
  have h := upperPairedReciprocalDerivative_bound z hz (B:Rat) Rat.natCast_nonneg hB
    (pairedTailShift B n) hk (pairedTailShift_large B n) hBk
  exact h.mono (by
    have hi := pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B n) (by omega)
      (by unfold pairedTailShift; omega)
    have hc := Rat.mul_le_mul_of_nonneg_left hi (show (0:Rat)≤1024 by decide)
    simpa only [show ((1024:Nat):Rat)=1024 by decide +kernel] using hc)

theorem upperPairedReciprocalDerivative_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (he : z.val.Equiv w.val) (n : Nat) :
    (upperPairedReciprocalDerivative z hz n).val.Equiv
      (upperPairedReciprocalDerivative w hw n).val :=
  add_equiv
    (ReciprocalDifference.derivative_congr _ _ (upperShiftMinus_nonzero z hz (n:Rat))
      (upperShiftMinus_nonzero w hw (n:Rat))
      (FunctionTheory.sub_congr he (equiv_refl _ (boundaryIntegerScalar n).property)))
    (ReciprocalDifference.derivative_congr _ _ (upperShiftPlus_nonzero z hz (n:Rat))
      (upperShiftPlus_nonzero w hw (n:Rat))
      (add_equiv he (equiv_refl _ (boundaryIntegerScalar n).property)))

def pairedDerivativeTailValue (z : Scalar) (hz : InUpperHalfPlane z.val) (B : Nat) : ComplexRaw :=
  inverseSquareSeriesValue (fun n => (pairedDerivativeTailTerm z hz B n).val)
    (fun n => (pairedDerivativeTailTerm z hz B n).property) 1024

theorem pairedDerivativeTailValue_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) : (pairedDerivativeTailValue z hz B).Valid :=
  inverseSquareSeriesValue_valid _ _ 1024 (pairedDerivativeTailTerm_bound z hz B hB)

theorem pairedDerivativeTailValue_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedDerivativeTailValue z hz B)
      (ScalarSeries.block (fun n => (pairedDerivativeTailTerm z hz B n).val) 0 (N+1)))
      (((1024:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) :=
  inverseSquareSeriesValue_close _ _ 1024 (pairedDerivativeTailTerm_bound z hz B hB) N

theorem pairedDerivativeTailValue_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (B : Nat)
    (hB : Small z.val (B:Rat)) (hBw : Small w.val (B:Rat)) (he : z.val.Equiv w.val) :
    (pairedDerivativeTailValue z hz B).Equiv (pairedDerivativeTailValue w hw B) :=
  inverseSquareSeriesValue_congr _ _ _ _ 1024
    (pairedDerivativeTailTerm_bound z hz B hB) (pairedDerivativeTailTerm_bound w hw B hBw)
    (fun n => upperPairedReciprocalDerivative_congr z w hz hw he (pairedTailShift B n))

end ComputableAnalysis.ModularForms
