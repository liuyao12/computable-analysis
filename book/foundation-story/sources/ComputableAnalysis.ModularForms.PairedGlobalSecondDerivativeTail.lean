import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeTerms

/-! Constructed global second-derivative tails with explicit inverse-square error. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedGlobalSecondDerivativeTailTerm (z : Scalar) (hz : InUpperHalfPlane z.val) (B n : Nat) : Scalar :=
  pairedGlobalSecondDerivativeTerm (4*B+n) z hz

theorem pairedGlobalSecondDerivativeTailTerm_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (n : Nat) :
    Small (pairedGlobalSecondDerivativeTailTerm z hz B n).val (65536*reciprocalSquare (n+1)) := by
  let k := 4*B+n+1
  have hk : 0<k := by dsimp [k]; omega
  have hp : (0:Rat)<(k:Rat) := by exact_mod_cast hk
  have h1 : (1:Rat)≤(k:Rat) := by exact_mod_cast (show 1≤k by omega)
  have hi : 0≤(k:Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hi1 : (k:Rat)⁻¹≤1 := by
    apply Rat.le_of_mul_le_mul_right (c := (k:Rat))
    · rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt hp),Rat.one_mul]
      exact h1
    · exact hp
  have hlarge : 16*(B:Rat)*(B:Rat)≤pairedIntegerSquare k := pairedTailShift_large B n
  have hBk : (B:Rat)≤(k:Rat) := by exact_mod_cast (show B≤k by dsimp [k]; omega)
  have hb := pairedGlobalSecondDerivativeTerm_regional_bound (4*B+n) z hz
    (B:Rat) Rat.natCast_nonneg hB hlarge hBk
  apply hb.mono
  have hcube := Rat.mul_le_mul_of_nonneg_left hi1 (Rat.mul_nonneg hi hi)
  have hsquare := pairedDerivative_reciprocalSquare_antitone (n+1) k (by omega)
    (by dsimp [k]; omega)
  rw [pairedDerivative_reciprocalSquare_eq_inverse_product k hk] at hsquare
  rw [Rat.div_def,Rat.one_mul]
  have hc := Rat.mul_le_mul_of_nonneg_left hcube (show (0:Rat)≤65536 by decide)
  have hs := Rat.mul_le_mul_of_nonneg_left hsquare (show (0:Rat)≤65536 by decide)
  change 65536*(k:Rat)⁻¹*(k:Rat)⁻¹*(k:Rat)⁻¹≤65536*reciprocalSquare (n+1)
  grind only

def pairedGlobalSecondDerivativeTailValue (z : Scalar) (hz : InUpperHalfPlane z.val) (B : Nat) : ComplexRaw :=
  inverseSquareSeriesValue (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).val)
    (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).property) 65536

theorem pairedGlobalSecondDerivativeTailValue_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) : (pairedGlobalSecondDerivativeTailValue z hz B).Valid :=
  inverseSquareSeriesValue_valid _ _ 65536 (pairedGlobalSecondDerivativeTailTerm_bound z hz B hB)

theorem pairedGlobalSecondDerivativeTailValue_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedGlobalSecondDerivativeTailValue z hz B)
      (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).val) 0 (N+1)))
      (65536*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ _ 65536 (pairedGlobalSecondDerivativeTailTerm_bound z hz B hB) N

end ComputableAnalysis.ModularForms
