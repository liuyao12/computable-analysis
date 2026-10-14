import ComputableAnalysis.ModularForms.CMWeightFourSum163

/-! Summable quantitative bounds for actual weight-six CM lattice shells. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def weightSixTailConstant : Rat := 8*(656:Rat)^6

theorem weightSixShell_small (r : Nat) (hr : 0<r) :
    Small (shellSum r hr 6) (weightSixTailConstant*reciprocalCube r) := by
  have h := shellSum_small r hr 6
  apply h.mono
  let a : Rat := r
  have hp : 0<a := by dsimp [a]; exact_mod_cast hr
  have h1 : (1:Rat)≤a := by dsimp [a]; exact_mod_cast hr
  have hc := Rat.mul_inv_cancel a (Rat.ne_of_gt hp)
  have hc3 := Rat.mul_inv_cancel (a*a*a)
    (Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hp hp) hp))
  have h2 : 1≤a*a := by
    have hm := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt hp)
    grind
  have h3 : a≤a*a*a := by
    have hm := Rat.mul_le_mul_of_nonneg_left h2 (Rat.le_of_lt hp)
    grind
  unfold shellTermBound weightSixTailConstant reciprocalCube
  rw [Rat.natCast_mul]
  apply Rat.le_of_mul_le_mul_right (c := a*a*a*a*a*a)
  · calc
      _ = 8*(656:Rat)^6*a := by
        simp only [Rat.pow_succ,Rat.pow_zero]
        grind [Rat.div_def]
      _ ≤ 8*(656:Rat)^6*(a*a*a) := by
        exact Rat.mul_le_mul_of_nonneg_left h3 (by decide +kernel)
      _ = _ := by
        simp only [Rat.pow_succ,Rat.pow_zero]
        grind
  · exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos hp hp) hp) hp) hp) hp

def weightSixTailBlock (N : Nat) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | k+1 => ComplexRaw.add (weightSixTailBlock N k) (shellSum (N+k+1) (by omega) 6)

theorem weightSixTailBlock_valid (N k : Nat) : (weightSixTailBlock N k).Valid := by
  induction k with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ k ih => exact ComplexRaw.add_valid ih (shellSum_valid _ _ _)

theorem weightSixTailBlock_small (N k : Nat) (hN : 0<N) :
    Small (weightSixTailBlock N k)
      (weightSixTailConstant*(reciprocalSquare N-reciprocalSquare (N+k))) := by
  have hC : 0≤weightSixTailConstant := by unfold weightSixTailConstant; decide +kernel
  induction k with
  | zero =>
    have he : weightSixTailConstant*(reciprocalSquare N-reciprocalSquare (N+0))=0 := by grind
    rw [he]
    exact Small.zero (by decide)
  | succ k ih =>
    have hs := weightSixShell_small (N+k+1) (by omega)
    have ht := reciprocalCube_step (N+k) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left ht hC
    apply (LocalODE.small_add ih hs).mono
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

theorem weightSixTailBlock_uniform_small (N k : Nat) (hN : 0<N) :
    Small (weightSixTailBlock N k) (weightSixTailConstant*reciprocalSquare N) := by
  apply (weightSixTailBlock_small N k hN).mono
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr (Rat.mul_pos hp hp))
  have hC : 0≤weightSixTailConstant := by unfold weightSixTailConstant; decide +kernel
  have hm := Rat.mul_nonneg hC hi
  change 0≤weightSixTailConstant*reciprocalSquare (N+k) at hm
  grind

end ComputableAnalysis.ModularForms
