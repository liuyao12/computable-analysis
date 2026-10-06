import ComputableAnalysis.ModularForms.CMWeightFourTail163

/-! A proved shrinking rational error rate for the actual weight-four lattice tails. -/
namespace ComputableAnalysis.ModularForms

def weightFourTailRate (n : Nat) : Rat := weightFourTailConstant*reciprocalSquare (n+1)

theorem reciprocalSquare_le_reciprocal (n : Nat) (hn : 0<n) :
    reciprocalSquare n≤1/(n:Rat) := by
  let a : Rat := n
  have hp : 0<a := by dsimp [a]; exact_mod_cast hn
  have h1 : (1:Rat)≤a := by dsimp [a]; exact_mod_cast hn
  have hc := Rat.mul_inv_cancel a (Rat.ne_of_gt hp)
  have hc2 := Rat.mul_inv_cancel (a*a) (Rat.ne_of_gt (Rat.mul_pos hp hp))
  change (a*a)⁻¹≤1/a
  apply Rat.le_of_mul_le_mul_right (c := a*a)
  · calc
      _ = 1 := by grind
      _ ≤ a := h1
      _ = _ := by grind [Rat.div_def]
  · exact Rat.mul_pos hp hp

theorem weightFourTailRate_shrinks : ShrinksToZero weightFourTailRate := by
  apply shrinksToZero_of_natOverSuccBound (C := 8*656^4)
  intro n
  have hs := reciprocalSquare_le_reciprocal (n+1) (by omega)
  have hC : 0≤weightFourTailConstant := by unfold weightFourTailConstant; decide +kernel
  have hc : weightFourTailConstant=((8*656^4:Nat):Rat) := by
    unfold weightFourTailConstant
    decide +kernel
  have hm := Rat.mul_le_mul_of_nonneg_left hs hC
  unfold weightFourTailRate
  calc
    _ ≤ weightFourTailConstant*(1/((n+1:Nat):Rat)) := hm
    _ = _ := by rw [hc]; grind [Rat.div_def]

end ComputableAnalysis.ModularForms
