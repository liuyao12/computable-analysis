import ComputableAnalysis.ModularForms.ReciprocalCubeTail

/-! Quantitative finite tails of actual weight-four CM lattice sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def weightFourTailConstant : Rat := 8*(656:Rat)^4

theorem weightFourShell_small (r : Nat) (hr : 0<r) :
    Small (shellSum r hr 4) (weightFourTailConstant*reciprocalCube r) := by
  have h := shellSum_small r hr 4
  have hp : (0:Rat)<(r:Rat) := by exact_mod_cast hr
  have hc := Rat.mul_inv_cancel (r:Rat) (Rat.ne_of_gt hp)
  have hp3 : (r:Rat)*(r:Rat)*(r:Rat)≠0 :=
    Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hp hp) hp)
  have hc3 := Rat.mul_inv_cancel _ hp3
  have he : (((8*r:Nat):Rat)*shellTermBound r 4)=weightFourTailConstant*reciprocalCube r := by
    unfold shellTermBound weightFourTailConstant reciprocalCube
    rw [Rat.natCast_mul]
    simp only [Rat.pow_succ,Rat.pow_zero]
    grind [Rat.div_def]
  rw [he] at h
  exact h

def weightFourTailBlock (N : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | k+1 => ComplexRaw.add (weightFourTailBlock N k)
      (shellSum (N+k+1) (by omega) 4)

theorem weightFourTailBlock_valid (N k : Nat) : (weightFourTailBlock N k).Valid := by
  induction k with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ k ih => exact ComplexRaw.add_valid ih (shellSum_valid _ _ _)

theorem weightFourTailBlock_small (N k : Nat) (hN : 0<N) :
    Small (weightFourTailBlock N k)
      (weightFourTailConstant*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤weightFourTailConstant := by unfold weightFourTailConstant; decide +kernel
  induction k with
  | zero =>
    have he : weightFourTailConstant*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := weightFourShell_small (N+k+1) (by omega)
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    have hsum := LocalODE.small_add ih hs
    apply hsum.mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem weightFourTailBlock_uniform_small (N k : Nat) (hN : 0<N) :
    Small (weightFourTailBlock N k) (weightFourTailConstant*reciprocalSquare N) := by
  apply (weightFourTailBlock_small N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤weightFourTailConstant := by unfold weightFourTailConstant; decide +kernel
  have hm := Rat.mul_nonneg hC hi
  change 0≤weightFourTailConstant*reciprocalSquare (N+k) at hm
  grind

end ComputableAnalysis.ModularForms
