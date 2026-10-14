import ComputableAnalysis.ModularForms.CMWeightFourTailRate163

/-! A uniform rational bound for shell majorants, including the first shell. -/
namespace ComputableAnalysis.ModularForms
open QuadraticOrder163

def reciprocalCubePrefix : Nat → Rat
  | 0 => 0
  | n+1 => reciprocalCubePrefix n+reciprocalCube (n+1)

theorem reciprocalCubePrefix_nonnegative (n : Nat) : 0≤reciprocalCubePrefix n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos n
    have hi := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos (Rat.mul_pos hp hp) hp))
    exact Rat.add_nonneg ih hi

theorem reciprocalCubePrefix_telescope (n : Nat) (hn : 0<n) :
    reciprocalCubePrefix n≤2-reciprocalSquare n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h0 : n=0
    · subst n
      change (0:Rat)+(1*1*1)⁻¹≤2-(1*1)⁻¹
      decide +kernel
    · have hpos : 0<n := by omega
      have hprev := ih hpos
      have hstep := reciprocalCube_step n hpos
      change reciprocalCubePrefix n+reciprocalCube (n+1)≤2-reciprocalSquare (n+1)
      grind

theorem reciprocalCubePrefix_le_two (n : Nat) : reciprocalCubePrefix n≤2 := by
  by_cases hn : n=0
  · subst n; change (0:Rat)≤2; decide
  · have hp : (0:Rat)<(n:Rat) := by exact_mod_cast (show 0<n by omega)
    have hi := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
    have ht := reciprocalCubePrefix_telescope n (by omega)
    change 0≤reciprocalSquare n at hi
    grind

end ComputableAnalysis.ModularForms
