import ComputableAnalysis.ModularForms.CMWeightSixShell163

/-! A proved shrinking rational error rate for the actual weight-six lattice tails. -/
namespace ComputableAnalysis.ModularForms

def weightSixTailRate (n : Nat) : Rat := weightSixTailConstant*reciprocalSquare (n+1)

theorem weightSixTailRate_shrinks : ShrinksToZero weightSixTailRate := by
  apply shrinksToZero_of_natOverSuccBound (C := 8*656^6)
  intro n
  have hs := reciprocalSquare_le_reciprocal (n+1) (by omega)
  have hC : 0≤weightSixTailConstant := by unfold weightSixTailConstant; decide +kernel
  have hc : weightSixTailConstant=((8*656^6:Nat):Rat) := by
    unfold weightSixTailConstant
    decide +kernel
  have hm := Rat.mul_le_mul_of_nonneg_left hs hC
  unfold weightSixTailRate
  calc
    _ ≤ weightSixTailConstant*(1/((n+1:Nat):Rat)) := hm
    _ = _ := by rw [hc]; grind [Rat.div_def]

end ComputableAnalysis.ModularForms
