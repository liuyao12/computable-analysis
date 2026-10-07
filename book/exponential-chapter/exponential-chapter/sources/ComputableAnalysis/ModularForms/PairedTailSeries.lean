import ComputableAnalysis.ModularForms.PairedIntegerBound
import ComputableAnalysis.ModularForms.InverseSquareSeries

/-! Actual convergent paired quotient tails beyond an explicit integer cutoff. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedTailShift (B n : Nat) : Nat := 4*B+n+1

theorem pairedTailShift_large (B n : Nat) :
    16*(B:Rat)*(B:Rat)≤pairedIntegerSquare (pairedTailShift B n) := by
  have hn : 4*B≤pairedTailShift B n := by unfold pairedTailShift; omega
  have h : (4:Rat)*(B:Rat)≤((pairedTailShift B n):Rat) := by exact_mod_cast hn
  have hb : (0:Rat)≤(B:Rat) := Rat.natCast_nonneg
  have hs : (0:Rat)≤((pairedTailShift B n):Rat) := Rat.natCast_nonneg
  have h1 := Rat.mul_le_mul_of_nonneg_right h (Rat.mul_nonneg (show (0:Rat)≤4 by decide) hb)
  have h2 := Rat.mul_le_mul_of_nonneg_left h hs
  unfold pairedIntegerSquare
  grind only

def pairedTailTerm (z : Scalar) (B : Nat) (hz : Small z.val (B:Rat)) (n : Nat) : Scalar :=
  let k := pairedTailShift B n
  let hd := pairedIntegerDenominator_nonzero z (B:Rat) k Rat.natCast_nonneg hz
    (by unfold k pairedTailShift; omega) (pairedTailShift_large B n)
  ⟨mul (add z.val z.val) (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare k)) hd).val,
    mul_valid (add_valid z.property z.property)
      (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare k)) hd).property⟩

theorem pairedTailTerm_bound (z : Scalar) (B : Nat) (hz : Small z.val (B:Rat)) (n : Nat) :
    Small (pairedTailTerm z B hz n).val (((16*B:Nat):Rat)*reciprocalSquare (n+1)) := by
  let k := pairedTailShift B n
  have hk : 0<k := by unfold k pairedTailShift; omega
  have hd := pairedIntegerDenominator_nonzero z (B:Rat) k Rat.natCast_nonneg hz hk (pairedTailShift_large B n)
  have h := pairedIntegerQuotient_bound z (B:Rat) k Rat.natCast_nonneg hz hk
    (pairedTailShift_large B n) hd
  apply h.mono
  have hn : n+1≤k := by unfold k pairedTailShift; omega
  have hnr : ((n+1:Nat):Rat)≤(k:Rat) := by exact_mod_cast hn
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hkp : (0:Rat)<(k:Rat) := by exact_mod_cast hk
  have h1 := Rat.mul_le_mul_of_nonneg_right hnr (Rat.le_of_lt hp)
  have h2 := Rat.mul_le_mul_of_nonneg_left hnr (Rat.le_of_lt hkp)
  have hs : ((n+1:Nat):Rat)*((n+1:Nat):Rat)≤(k:Rat)*(k:Rat) := Rat.le_trans h1 h2
  have ca := Rat.mul_inv_cancel (((n+1:Nat):Rat)*((n+1:Nat):Rat))
    (Rat.ne_of_gt (Rat.mul_pos hp hp))
  have cb := Rat.mul_inv_cancel ((k:Rat)*(k:Rat)) (Rat.ne_of_gt (Rat.mul_pos hkp hkp))
  have hi : ((k:Rat)*(k:Rat))⁻¹≤(((n+1:Nat):Rat)*((n+1:Nat):Rat))⁻¹ := by
    apply Rat.le_of_mul_le_mul_right
      (c := (((n+1:Nat):Rat)*((n+1:Nat):Rat))*((k:Rat)*(k:Rat)))
    · calc
        _ = ((n+1:Nat):Rat)*((n+1:Nat):Rat) := by grind
        _ ≤ (k:Rat)*(k:Rat) := hs
        _ = _ := by grind
    · exact Rat.mul_pos (Rat.mul_pos hp hp) (Rat.mul_pos hkp hkp)
  have hm := Rat.mul_le_mul_of_nonneg_left hi
    (Rat.mul_nonneg (show (0:Rat)≤16 by decide) (show (0:Rat)≤(B:Rat) from Rat.natCast_nonneg))
  simpa only [pairedIntegerSquare,reciprocalSquare,Rat.div_def,Rat.one_mul,Rat.natCast_mul,show ((16:Nat):Rat)=16 by decide +kernel] using hm

def pairedTailValue (z : Scalar) (B : Nat) (hz : Small z.val (B:Rat)) : ComplexRaw :=
  inverseSquareSeriesValue (fun n => (pairedTailTerm z B hz n).val)
    (fun n => (pairedTailTerm z B hz n).property) (16*B)

theorem pairedTailValue_valid (z : Scalar) (B : Nat) (hz : Small z.val (B:Rat)) :
    (pairedTailValue z B hz).Valid :=
  inverseSquareSeriesValue_valid _ _ (16*B) (pairedTailTerm_bound z B hz)

theorem pairedTailValue_close (z : Scalar) (B : Nat) (hz : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedTailValue z B hz)
      (ScalarSeries.block (fun n => (pairedTailTerm z B hz n).val) 0 (N+1)))
      (((16*B:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) :=
  inverseSquareSeriesValue_close _ _ (16*B) (pairedTailTerm_bound z B hz) N

theorem pairedTailTerm_congr (z w : Scalar) (B : Nat)
    (hz : Small z.val (B:Rat)) (hw : Small w.val (B:Rat)) (he : z.val.Equiv w.val) (n : Nat) :
    (pairedTailTerm z B hz n).val.Equiv (pairedTailTerm w B hw n).val := by
  let k := pairedTailShift B n
  have hk : 0<k := by unfold k pairedTailShift; omega
  let hd := pairedIntegerDenominator_nonzero z (B:Rat) k Rat.natCast_nonneg hz hk (pairedTailShift_large B n)
  let hdw := pairedIntegerDenominator_nonzero w (B:Rat) k Rat.natCast_nonneg hw hk (pairedTailShift_large B n)
  have hi := RepresentedReciprocal.inverse_congr (pairedLiteralDenominator z (pairedIntegerSquare k))
    (pairedLiteralDenominator w (pairedIntegerSquare k)) hd hdw
    (FunctionTheory.sub_congr (mul_equiv z.property w.property z.property w.property he he)
      (equiv_refl _ (ofQComplex_valid _)))
  exact mul_equiv (add_valid z.property z.property) (add_valid w.property w.property)
    (RepresentedReciprocal.inverse _ hd).property (RepresentedReciprocal.inverse _ hdw).property
    (add_equiv he he) hi

theorem pairedTailValue_congr (z w : Scalar) (B : Nat)
    (hz : Small z.val (B:Rat)) (hw : Small w.val (B:Rat)) (he : z.val.Equiv w.val) :
    (pairedTailValue z B hz).Equiv (pairedTailValue w B hw) :=
  inverseSquareSeriesValue_congr _ _ _ _ (16*B) (pairedTailTerm_bound z B hz)
    (pairedTailTerm_bound w B hw) (pairedTailTerm_congr z w B hz hw he)

end ComputableAnalysis.ModularForms
