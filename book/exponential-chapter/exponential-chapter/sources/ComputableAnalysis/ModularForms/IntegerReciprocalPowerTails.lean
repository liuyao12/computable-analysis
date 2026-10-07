import ComputableAnalysis.ModularForms.IntegerReciprocalPowers
import ComputableAnalysis.ModularForms.PairedDerivativeTail

/-! Explicit summable majorants for actual paired integer reciprocal powers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem reciprocal_integer_power_le_square (n k : Nat) (hn : 0<n) (hk : 2≤k) :
    ((n:Rat)⁻¹)^k≤reciprocalSquare n := by
  have hp : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  have hi0 : 0≤(n:Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hi := Rat.mul_inv_cancel (n:Rat) (Rat.ne_of_gt hp)
  have hn1 : (1:Rat)≤(n:Rat) := by exact_mod_cast (show 1≤n by omega)
  have hm := Rat.mul_le_mul_of_nonneg_right hn1 hi0
  rw [Rat.one_mul,hi] at hm
  have h (j : Nat) : ((n:Rat)⁻¹)^(j+2)≤((n:Rat)⁻¹)^2 := by
    induction j with
    | zero => exact Rat.le_refl
    | succ j ih =>
      rw [show j+1+2=(j+2)+1 by omega,Rat.pow_succ]
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih hi0)
        (by have hh := Rat.mul_le_mul_of_nonneg_left hm (Rat.pow_nonneg (n := 2) hi0); simpa only [Rat.mul_one] using hh)
  have hh := h (k-2)
  rw [show k-2+2=k by omega] at hh
  rw [pairedDerivative_reciprocalSquare_eq_inverse_product n hn]
  simpa only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] using hh

def upperPairedIntegerPower (z : Scalar) (hz : InUpperHalfPlane z.val) (k n : Nat) : Scalar :=
  DomainFunctions.scalarSum
    ((integerReciprocalPowerMap (-((n:Nat):Int)) k).eval z hz)
    ((integerReciprocalPowerMap ((n:Nat):Int) k).eval z hz)

theorem upperPairedIntegerPower_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (k n : Nat) (hk : 2≤k) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) (hRn : R≤(n:Rat)) :
    Small (upperPairedIntegerPower z hz k n).val (2*(32:Rat)^k*reciprocalSquare n) := by
  have hm := upperIntegerReciprocal_minus_bound z hz R hR hsmall n hn hlarge hRn
  have hp := upperIntegerReciprocal_plus_bound z hz R hR hsmall n hn hlarge hRn
  have hnR : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  have hM : 0≤16*(1/(n:Rat)) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hnR))
  have h := LocalODE.small_add
    (LocalODE.power_small _ ((integerReciprocalMap (-((n:Nat):Int))).eval z hz).property _ hM hm k)
    (LocalODE.power_small _ ((integerReciprocalMap ((n:Nat):Int)).eval z hz).property _ hM hp k)
  apply h.mono
  have he : 2*(16*(1/(n:Rat)))=32*(n:Rat)⁻¹ := by
    rw [Rat.div_def,Rat.one_mul]; grind only
  rw [he,LocalODE.rational_mul_pow]
  have hb := Rat.mul_le_mul_of_nonneg_left (reciprocal_integer_power_le_square n k hn hk)
    (Rat.pow_nonneg (a := (32:Rat)) (n := k) (by decide))
  grind only

def pairedIntegerPowerTailTerm (z : Scalar) (hz : InUpperHalfPlane z.val) (k B n : Nat) : Scalar :=
  upperPairedIntegerPower z hz k (pairedTailShift B n)

theorem pairedIntegerPowerTailTerm_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) (n : Nat) :
    Small (pairedIntegerPowerTailTerm z hz k B n).val
      (((2*32^k:Nat):Rat)*reciprocalSquare (n+1)) := by
  have hn : 0<pairedTailShift B n := by unfold pairedTailShift; omega
  have hBn : (B:Rat)≤((pairedTailShift B n):Rat) := by
    exact_mod_cast (show B≤pairedTailShift B n by unfold pairedTailShift; omega)
  have h := upperPairedIntegerPower_bound z hz (B:Rat) Rat.natCast_nonneg hB k
    (pairedTailShift B n) hk hn (pairedTailShift_large B n) hBn
  have hc : ((2*32^k:Nat):Rat)=2*(32:Rat)^k := by
    simp only [Rat.natCast_mul,Rat.natCast_pow,
      show ((2:Nat):Rat)=2 by decide +kernel,show ((32:Nat):Rat)=32 by decide +kernel]
  rw [hc]
  exact h.mono (Rat.mul_le_mul_of_nonneg_left
    (pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B n) (by omega)
      (by unfold pairedTailShift; omega))
    (Rat.mul_nonneg (by decide) (Rat.pow_nonneg (a := (32:Rat)) (n := k) (by decide))))

def pairedIntegerPowerTailValue (z : Scalar) (hz : InUpperHalfPlane z.val) (k B : Nat) : ComplexRaw :=
  inverseSquareSeriesValue (fun n => (pairedIntegerPowerTailTerm z hz k B n).val)
    (fun n => (pairedIntegerPowerTailTerm z hz k B n).property) (2*32^k)

theorem pairedIntegerPowerTailValue_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) :
    (pairedIntegerPowerTailValue z hz k B).Valid :=
  inverseSquareSeriesValue_valid _ _ (2*32^k) (pairedIntegerPowerTailTerm_bound z hz k B hk hB)

theorem pairedIntegerPowerTailValue_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedIntegerPowerTailValue z hz k B)
      (ScalarSeries.block (fun n => (pairedIntegerPowerTailTerm z hz k B n).val) 0 (N+1)))
      (((2*32^k:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) :=
  inverseSquareSeriesValue_close _ _ (2*32^k) (pairedIntegerPowerTailTerm_bound z hz k B hk hB) N

end ComputableAnalysis.ModularForms
