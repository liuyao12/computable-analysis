import ComputableAnalysis.ModularForms.PairedOffPoleTailDerivativeTerms
import ComputableAnalysis.ModularForms.InverseSquareSeriesBound

/-! Constructed derivative-tail sums on the full interior cutoff disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailDerivativeConstant (B : Nat) : Nat := 8+512*B*B

theorem pairedOffPoleTailInverse_bound (B n : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    Small (pairedOffPoleTailInverse B n z hz).val (4*reciprocalSquare (pairedTailShift B n)) := by
  let k := pairedTailShift B n
  have hk : 0<k := by dsimp [k,pairedTailShift]; omega
  have hpos := pairedIntegerSquare_pos k hk
  have hc : 0≤1/pairedIntegerSquare k := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr hpos)
  have hct : pairedIntegerSquare k*(1/pairedIntegerSquare k)=1 := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hpos)
  have hb := pairedLiteralInverse_bound z (B:Rat) (1/pairedIntegerSquare k) (pairedIntegerSquare k)
    Rat.natCast_nonneg hc (LocalODE.interior_bound _ z hz)
    (pairedInteger_normalization (B:Rat) k hk (pairedTailShift_large B n)) hct
    (pairedIntegerDenominator_nonzero z (B:Rat) k Rat.natCast_nonneg
      (LocalODE.interior_bound _ z hz) hk (pairedTailShift_large B n))
  simpa only [pairedOffPoleTailInverse,reciprocalSquare,pairedIntegerSquare,Rat.div_def,Rat.one_mul] using hb

theorem pairedOffPoleTailDerivativeTerm_bound (B n : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    Small (pairedOffPoleTailDerivativeTerm B n z hz).val
      ((pairedOffPoleTailDerivativeConstant B:Rat)*reciprocalSquare (n+1)) := by
  let r := reciprocalSquare (pairedTailShift B n)
  have hr : 0≤r := by
    unfold r reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos
      (by exact_mod_cast (show 0<pairedTailShift B n by unfold pairedTailShift; omega))
      (by exact_mod_cast (show 0<pairedTailShift B n by unfold pairedTailShift; omega))))
  have hsmall := LocalODE.interior_bound _ z hz
  have hi := pairedOffPoleTailInverse_bound B n z hz
  let i := pairedOffPoleTailInverse B n z hz
  have hM : 0≤4*r := Rat.mul_nonneg (by decide +kernel) hr
  have hz2 := LocalODE.small_add hsmall hsmall
  have hzz := Small.mul (add_valid z.property z.property) (add_valid z.property z.property)
    (Rat.add_nonneg Rat.natCast_nonneg Rat.natCast_nonneg)
    (Rat.add_nonneg Rat.natCast_nonneg Rat.natCast_nonneg) hz2 hz2
  have hii := Small.mul i.property i.property hM hM hi hi
  have hp := Small.mul (mul_valid (add_valid z.property z.property) (add_valid z.property z.property))
    (mul_valid i.property i.property)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.add_nonneg Rat.natCast_nonneg Rat.natCast_nonneg))
      (Rat.add_nonneg Rat.natCast_nonneg Rat.natCast_nonneg))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hM) hM) hzz hii
  have hs := SeriesLimitLaws.small_sub (LocalODE.small_add hi hi) hp
  apply hs.mono
  have hri := pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B n)
    (by omega) (by unfold pairedTailShift; omega)
  have hr1 := pairedDerivative_reciprocalSquare_antitone 1 (pairedTailShift B n)
    (by omega) (by unfold pairedTailShift; omega)
  rw [show reciprocalSquare 1=1 by decide +kernel] at hr1
  have hrr := Rat.mul_le_mul_of_nonneg_left hr1 hr
  have hbb : 0≤(B:Rat)*(B:Rat) := Rat.mul_nonneg Rat.natCast_nonneg Rat.natCast_nonneg
  have hh := Rat.mul_le_mul_of_nonneg_left hrr (Rat.mul_nonneg (show (0:Rat)≤512 by decide) hbb)
  have hmajor := Rat.mul_le_mul_of_nonneg_left hri
    (show 0≤8+512*(B:Rat)*(B:Rat) by grind only)
  simp only [pairedOffPoleTailDerivativeConstant,Rat.natCast_add,Rat.natCast_mul,
    show ((8:Nat):Rat)=8 by decide +kernel,show ((512:Nat):Rat)=512 by decide +kernel]
  dsimp only [r] at hr hh
  grind only

def pairedOffPoleTailDerivativeValue (B : Nat) (z : Scalar) (hz : LocalODE.interior (B:Rat) z) : Scalar :=
  ⟨inverseSquareSeriesValue (fun n => (pairedOffPoleTailDerivativeTerm B n z hz).val)
    (fun n => (pairedOffPoleTailDerivativeTerm B n z hz).property) (pairedOffPoleTailDerivativeConstant B),
    inverseSquareSeriesValue_valid _ _ _ (fun n => pairedOffPoleTailDerivativeTerm_bound B n z hz)⟩

theorem pairedOffPoleTailDerivativeValue_close (B : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) (N : Nat) :
    Small (sub (pairedOffPoleTailDerivativeValue B z hz).val
      (ScalarSeries.block (fun n => (pairedOffPoleTailDerivativeTerm B n z hz).val) 0 (N+1)))
      ((pairedOffPoleTailDerivativeConstant B:Rat)*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close (fun n => (pairedOffPoleTailDerivativeTerm B n z hz).val)
    (fun n => (pairedOffPoleTailDerivativeTerm B n z hz).property) _
    (fun n => pairedOffPoleTailDerivativeTerm_bound B n z hz) N

end ComputableAnalysis.ModularForms
