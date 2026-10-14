import ComputableAnalysis.ModularForms.CMMaskedShell163

/-! Uniform tail bounds for arbitrary selected lattice terms. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def maskedWeightFourTailBlock (keep : Nat → Nat → Bool) (N : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | k+1 => ComplexRaw.add (maskedWeightFourTailBlock keep N k)
      (maskedShellSum (N+k+1) (by omega) 4 (keep (N+k+1)))

theorem maskedWeightFourTailBlock_valid (keep : Nat → Nat → Bool) (N k : Nat) : (maskedWeightFourTailBlock keep N k).Valid := by
  induction k with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ k ih => exact ComplexRaw.add_valid ih (maskedShellSum_valid _ _ _ _)

theorem maskedWeightFourTailBlock_small (keep : Nat → Nat → Bool) (N k : Nat) (hN : 0<N) :
    Small (maskedWeightFourTailBlock keep N k)
      (weightFourTailConstant*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤weightFourTailConstant := by unfold weightFourTailConstant; decide +kernel
  induction k with
  | zero =>
    have he : weightFourTailConstant*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := maskedWeightFourShell_small (N+k+1) (by omega) (keep (N+k+1))
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    have hsum := LocalODE.small_add ih hs
    apply hsum.mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem maskedWeightFourTailBlock_uniform_small (keep : Nat → Nat → Bool) (N k : Nat) (hN : 0<N) :
    Small (maskedWeightFourTailBlock keep N k) (weightFourTailConstant*reciprocalSquare N) := by
  apply (maskedWeightFourTailBlock_small keep N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤weightFourTailConstant := by unfold weightFourTailConstant; decide +kernel
  have hm := Rat.mul_nonneg hC hi
  change 0≤weightFourTailConstant*reciprocalSquare (N+k) at hm
  grind

def maskedWeightSixTailBlock (keep : Nat → Nat → Bool) (N : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | k+1 => ComplexRaw.add (maskedWeightSixTailBlock keep N k) (maskedShellSum (N+k+1) (by omega) 6 (keep (N+k+1)))

theorem maskedWeightSixTailBlock_valid (keep : Nat → Nat → Bool) (N k : Nat) : (maskedWeightSixTailBlock keep N k).Valid := by
  induction k with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ k ih => exact ComplexRaw.add_valid ih (maskedShellSum_valid _ _ _ _)

theorem maskedWeightSixTailBlock_small (keep : Nat → Nat → Bool) (N k : Nat) (hN : 0<N) :
    Small (maskedWeightSixTailBlock keep N k)
      (weightSixTailConstant*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤weightSixTailConstant := by unfold weightSixTailConstant; decide +kernel
  induction k with
  | zero =>
    have he : weightSixTailConstant*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := maskedWeightSixShell_small (N+k+1) (by omega) (keep (N+k+1))
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    apply (LocalODE.small_add ih hs).mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem maskedWeightSixTailBlock_uniform_small (keep : Nat → Nat → Bool) (N k : Nat) (hN : 0<N) :
    Small (maskedWeightSixTailBlock keep N k) (weightSixTailConstant*reciprocalSquare N) := by
  apply (maskedWeightSixTailBlock_small keep N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤weightSixTailConstant := by unfold weightSixTailConstant; decide +kernel
  have hm := Rat.mul_nonneg hC hi
  change 0≤weightSixTailConstant*reciprocalSquare (N+k) at hm
  grind

end ComputableAnalysis.ModularForms
