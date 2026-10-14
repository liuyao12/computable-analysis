import ComputableAnalysis.ModularForms.PairedGlobalDerivativeRemainderPrefixes

/-! Constructed global second-derivative tails with explicit inverse-square error. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedGlobalDerivativeRemainderTailTerm (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (B n : Nat) : Scalar :=
  pairedGlobalDerivativeRemainder (4*B+n) a z ha hz

theorem pairedGlobalDerivativeRemainderTailTerm_bound (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hBa : Small a.val (B:Rat)) (hBz : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (pairedGlobalDerivativeRemainderTailTerm a z ha hz B n).val (12582912*reciprocalSquare (n+1)*H*H) := by
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
  have hb := pairedGlobalDerivativeRemainder_regional_bound (4*B+n) a z ha hz
    (B:Rat) H Rat.natCast_nonneg hH hBa hBz hd hlarge hBk
  apply hb.mono
  have hcube := Rat.mul_le_mul_of_nonneg_left hi1 (Rat.mul_nonneg hi hi)
  have hfourth := Rat.mul_le_mul_of_nonneg_left hi1
    (Rat.mul_nonneg (Rat.mul_nonneg hi hi) hi)
  have hsquare := pairedDerivative_reciprocalSquare_antitone (n+1) k (by omega)
    (by dsimp [k]; omega)
  rw [pairedDerivative_reciprocalSquare_eq_inverse_product k hk] at hsquare
  rw [Rat.div_def,Rat.one_mul]
  have hC : 0≤12582912*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hc := Rat.mul_le_mul_of_nonneg_left hcube hC
  have hf := Rat.mul_le_mul_of_nonneg_left hfourth hC
  have hs := Rat.mul_le_mul_of_nonneg_left hsquare hC
  change 12582912*(k:Rat)⁻¹*(k:Rat)⁻¹*(k:Rat)⁻¹*(k:Rat)⁻¹*H*H≤12582912*reciprocalSquare (n+1)*H*H
  grind only

theorem pairedGlobalDerivativeRemainderTail_block_bound (N K : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hBa : Small a.val (B:Rat)) (hBz : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => (pairedGlobalDerivativeRemainderTailTerm a z ha hz B n).val) N K)
      (12582912*reciprocalSquareBlock N K*H*H) := by
  induction K with
  | zero => exact Small.zero (by simp only [reciprocalSquareBlock,Rat.mul_zero,Rat.zero_mul]; decide +kernel)
  | succ K ih =>
    have h := LocalODE.small_add ih
      (pairedGlobalDerivativeRemainderTailTerm_bound a z ha hz B hBa hBz H hH hd (N+K))
    apply h.mono
    change 12582912*reciprocalSquareBlock N K*H*H+
      12582912*reciprocalSquare (N+K+1)*H*H≤12582912*reciprocalSquareBlock N (K+1)*H*H
    rw [reciprocalSquareBlock]
    grind only

theorem pairedGlobalDerivativeRemainderTail_block_tail (N K : Nat) (hN : 0<N) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hBa : Small a.val (B:Rat)) (hBz : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => (pairedGlobalDerivativeRemainderTailTerm a z ha hz B n).val) N K)
      (12582912*(N:Rat)⁻¹*H*H) := by
  apply (pairedGlobalDerivativeRemainderTail_block_bound N K a z ha hz B hBa hBz H hH hd).mono
  have hC : 0≤(12582912:Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hm := Rat.mul_le_mul_of_nonneg_left (reciprocalSquareBlock_tail N K hN) hC
  grind only

end ComputableAnalysis.ModularForms
