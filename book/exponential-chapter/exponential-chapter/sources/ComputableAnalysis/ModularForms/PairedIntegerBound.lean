import ComputableAnalysis.ModularForms.PairedInverseBound

/-! Inverse-square bounds at positive integer shifts for the paired lattice route. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedIntegerSquare (n : Nat) : Rat := (n:Rat)*(n:Rat)

theorem pairedIntegerSquare_pos (n : Nat) (hn : 0<n) : 0<pairedIntegerSquare n := by
  have hp : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  exact Rat.mul_pos hp hp

theorem pairedInteger_normalization (R : Rat) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) :
    (1/pairedIntegerSquare n)*(2*R*R)≤(1:Rat)/8 := by
  have hp := pairedIntegerSquare_pos n hn
  have hi : 0≤(pairedIntegerSquare n)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).mpr hp)
  have hm := Rat.mul_le_mul_of_nonneg_right hlarge hi
  have he := Rat.mul_inv_cancel (pairedIntegerSquare n) (Rat.ne_of_gt hp)
  rw [he] at hm
  rw [Rat.div_def]
  grind only

theorem pairedIntegerDenominator_nonzero (z : Scalar) (R : Rat) (n : Nat)
    (hR : 0≤R) (hz : Small z.val R) (hn : 0<n) (hlarge : 16*R*R≤pairedIntegerSquare n) :
    NonzeroBoxSearch.Nonzero (pairedLiteralDenominator z (pairedIntegerSquare n)) := by
  have hp := pairedIntegerSquare_pos n hn
  have hc : 0≤1/pairedIntegerSquare n := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt ((Rat.inv_pos).mpr hp))
  have he : pairedIntegerSquare n*(1/pairedIntegerSquare n)=1 := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hp)
  exact pairedLiteralDenominator_nonzero z R (1/pairedIntegerSquare n) (pairedIntegerSquare n)
    hR hc hz (pairedInteger_normalization R n hn hlarge) he

theorem pairedIntegerQuotient_bound (z : Scalar) (R : Rat) (n : Nat)
    (hR : 0≤R) (hz : Small z.val R) (hn : 0<n) (hlarge : 16*R*R≤pairedIntegerSquare n)
    (hd : NonzeroBoxSearch.Nonzero (pairedLiteralDenominator z (pairedIntegerSquare n))) :
    Small (mul (add z.val z.val)
      (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare n)) hd).val)
      (16*R*(1/pairedIntegerSquare n)) := by
  have hp := pairedIntegerSquare_pos n hn
  have hc : 0≤1/pairedIntegerSquare n := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt ((Rat.inv_pos).mpr hp))
  have he : pairedIntegerSquare n*(1/pairedIntegerSquare n)=1 := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hp)
  exact pairedLiteralQuotient_bound z R (1/pairedIntegerSquare n) (pairedIntegerSquare n)
    hR hc hz (pairedInteger_normalization R n hn hlarge) he hd

end ComputableAnalysis.ModularForms
