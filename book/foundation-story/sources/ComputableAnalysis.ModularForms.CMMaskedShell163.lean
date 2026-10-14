import ComputableAnalysis.ModularForms.CMWeightSixShell163

/-! Bounds for arbitrary executable subsets of CM lattice shells. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def maskedShellPrefix (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) : Nat → ComplexRaw
  | 0 => ComplexRaw.zero
  | n+1 => ComplexRaw.add (maskedShellPrefix r hr k keep n)
      (if keep n then shellTerm r hr k n else ComplexRaw.zero)

theorem maskedShellPrefix_valid (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool)
    (n : Nat) : (maskedShellPrefix r hr k keep n).Valid := by
  induction n with
  | zero => exact ComplexRaw.ofQComplex_valid _
  | succ n ih =>
    apply ComplexRaw.add_valid ih
    split
    · exact shellTerm_valid r hr k n
    · exact ComplexRaw.ofQComplex_valid _

theorem maskedShellPrefix_small (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool)
    (n : Nat) : Small (maskedShellPrefix r hr k keep n) ((n:Rat)*shellTermBound r k) := by
  induction n with
  | zero =>
    change Small ComplexRaw.zero ((0:Rat)*shellTermBound r k)
    rw [Rat.zero_mul]
    exact Small.zero (by decide)
  | succ n ih =>
    have ht : Small (if keep n then shellTerm r hr k n else ComplexRaw.zero)
        (shellTermBound r k) := by
      split
      · exact shellTerm_small r hr k n
      · exact Small.zero (shellTermBound_nonnegative r k)
    have hs := LocalODE.small_add ih ht
    have he : (n:Rat)*shellTermBound r k+shellTermBound r k=
        ((n+1:Nat):Rat)*shellTermBound r k := by
      rw [Rat.natCast_add]
      grind
    rw [he] at hs
    exact hs

def maskedShellSum (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) : ComplexRaw :=
  maskedShellPrefix r hr k keep (8*r)

theorem maskedShellSum_valid (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) :
    (maskedShellSum r hr k keep).Valid := maskedShellPrefix_valid r hr k keep _

theorem maskedShellSum_small (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) :
    Small (maskedShellSum r hr k keep) (((8*r:Nat):Rat)*shellTermBound r k) :=
  maskedShellPrefix_small r hr k keep _

theorem maskedWeightFourShell_small (r : Nat) (hr : 0<r) (keep : Nat → Bool) :
    Small (maskedShellSum r hr 4 keep) (weightFourTailConstant*reciprocalCube r) := by
  have h := maskedShellSum_small r hr 4 keep
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

theorem maskedWeightSixShell_small (r : Nat) (hr : 0<r) (keep : Nat → Bool) :
    Small (maskedShellSum r hr 6 keep) (weightSixTailConstant*reciprocalCube r) := by
  have h := maskedShellSum_small r hr 6 keep
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

end ComputableAnalysis.ModularForms
