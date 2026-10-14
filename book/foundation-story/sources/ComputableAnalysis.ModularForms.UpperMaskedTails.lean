import ComputableAnalysis.ModularForms.UpperMaskedShells

/-! Uniform tail bounds for arbitrary selected lattice terms. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def upperMaskedWeightFourTailBlock (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | k+1 => ComplexRaw.add (upperMaskedWeightFourTailBlock z hz keep N k)
      (upperMaskedShellSum z hz (N+k+1) (by omega) 4 (keep (N+k+1)))

theorem upperMaskedWeightFourTailBlock_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat) : (upperMaskedWeightFourTailBlock z hz keep N k).Valid := by
  induction k with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ k ih => exact ComplexRaw.add_valid ih (upperMaskedShellSum_valid z hz _ _ _ _)

theorem upperMaskedWeightFourTailBlock_small (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat) (hN : 0<N) :
    Small (upperMaskedWeightFourTailBlock z hz keep N k)
      (upperWeightFourTailConstant z hz*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤upperWeightFourTailConstant z hz := by
    unfold upperWeightFourTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  induction k with
  | zero =>
    have he : upperWeightFourTailConstant z hz*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := upperMaskedWeightFourShell_small z hz (N+k+1) (by omega) (keep (N+k+1))
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    have hsum := LocalODE.small_add ih hs
    apply hsum.mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem upperMaskedWeightFourTailBlock_uniform_small (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat) (hN : 0<N) :
    Small (upperMaskedWeightFourTailBlock z hz keep N k) (upperWeightFourTailConstant z hz*reciprocalSquare N) := by
  apply (upperMaskedWeightFourTailBlock_small z hz keep N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤upperWeightFourTailConstant z hz := by
    unfold upperWeightFourTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  have hm := Rat.mul_nonneg hC hi
  change 0≤upperWeightFourTailConstant z hz*reciprocalSquare (N+k) at hm
  grind

def upperMaskedWeightSixTailBlock (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | k+1 => ComplexRaw.add (upperMaskedWeightSixTailBlock z hz keep N k) (upperMaskedShellSum z hz (N+k+1) (by omega) 6 (keep (N+k+1)))

theorem upperMaskedWeightSixTailBlock_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat) : (upperMaskedWeightSixTailBlock z hz keep N k).Valid := by
  induction k with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ k ih => exact ComplexRaw.add_valid ih (upperMaskedShellSum_valid z hz _ _ _ _)

theorem upperMaskedWeightSixTailBlock_small (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat) (hN : 0<N) :
    Small (upperMaskedWeightSixTailBlock z hz keep N k)
      (upperWeightSixTailConstant z hz*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤upperWeightSixTailConstant z hz := by
    unfold upperWeightSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  induction k with
  | zero =>
    have he : upperWeightSixTailConstant z hz*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := upperMaskedWeightSixShell_small z hz (N+k+1) (by omega) (keep (N+k+1))
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    apply (LocalODE.small_add ih hs).mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem upperMaskedWeightSixTailBlock_uniform_small (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat) (hN : 0<N) :
    Small (upperMaskedWeightSixTailBlock z hz keep N k) (upperWeightSixTailConstant z hz*reciprocalSquare N) := by
  apply (upperMaskedWeightSixTailBlock_small z hz keep N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤upperWeightSixTailConstant z hz := by
    unfold upperWeightSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  have hm := Rat.mul_nonneg hC hi
  change 0≤upperWeightSixTailConstant z hz*reciprocalSquare (N+k) at hm
  grind

end ComputableAnalysis.ModularForms
