import ComputableAnalysis.ModularForms.CMLatticeShellSum163

/-! Explicit rational telescoping tails for weight-four lattice shell majorants. -/
namespace ComputableAnalysis.ModularForms

def reciprocalSquare (n : Nat) : Rat := ((n:Rat)*(n:Rat))⁻¹
def reciprocalCube (n : Nat) : Rat := ((n:Rat)*(n:Rat)*(n:Rat))⁻¹

theorem reciprocalCube_step (n : Nat) (hn : 0<n) :
    reciprocalCube (n+1)≤reciprocalSquare n-reciprocalSquare (n+1) := by
  let a : Rat := n
  let b : Rat := ((n+1:Nat):Rat)
  have ha : 0<a := by dsimp [a]; exact_mod_cast hn
  have hb : 0<b := by dsimp [b]; exact_mod_cast (show 0<n+1 by omega)
  have hab : b=a+1 := by dsimp [a,b]; rw [Rat.natCast_add]; rfl
  have hA : a*a≠0 := Rat.ne_of_gt (Rat.mul_pos ha ha)
  have hB : b*b≠0 := Rat.ne_of_gt (Rat.mul_pos hb hb)
  have hC : b*b*b≠0 := Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hb hb) hb)
  have ca := Rat.mul_inv_cancel (a*a) hA
  have cb := Rat.mul_inv_cancel (b*b) hB
  have cc := Rat.mul_inv_cancel (b*b*b) hC
  change (b*b*b)⁻¹≤(a*a)⁻¹-(b*b)⁻¹
  apply Rat.le_of_mul_le_mul_right (c := (a*a)*(b*b*b))
  · calc
      _ = a*a := by grind
      _ ≤ (2*a+1)*b := by have hp := Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt ha); grind
      _ = _ := by grind
  · exact Rat.mul_pos (Rat.mul_pos ha ha) (Rat.mul_pos (Rat.mul_pos hb hb) hb)

def reciprocalCubeBlock (N : Nat) : Nat → Rat
  | 0 => 0
  | k+1 => reciprocalCubeBlock N k+reciprocalCube (N+k+1)

theorem reciprocalCubeBlock_bound (N k : Nat) (hN : 0<N) :
    reciprocalCubeBlock N k≤reciprocalSquare N-reciprocalSquare (N+k) := by
  induction k with
  | zero => simp only [reciprocalCubeBlock,Nat.add_zero]; grind
  | succ k ih =>
    have hs := reciprocalCube_step (N+k) (by omega)
    change reciprocalCubeBlock N k+reciprocalCube (N+k+1)≤_
    have he : N+(k+1)=N+k+1 := by omega
    rw [he]
    grind

end ComputableAnalysis.ModularForms
