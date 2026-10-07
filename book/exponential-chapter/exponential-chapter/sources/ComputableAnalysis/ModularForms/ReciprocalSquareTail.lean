import ComputableAnalysis.ModularForms.ReciprocalCubeTail

/-! Rational telescoping tails for the paired inverse-square majorant. -/
namespace ComputableAnalysis.ModularForms

theorem reciprocalSquare_step (n : Nat) (hn : 0<n) :
    reciprocalSquare (n+1)≤(n:Rat)⁻¹-(((n+1:Nat):Rat))⁻¹ := by
  let a : Rat := n
  let b : Rat := ((n+1:Nat):Rat)
  have ha : 0<a := by dsimp [a]; exact_mod_cast hn
  have hb : 0<b := by dsimp [b]; exact_mod_cast (show 0<n+1 by omega)
  have hab : b=a+1 := by dsimp [a,b]; rw [Rat.natCast_add]; rfl
  have ca := Rat.mul_inv_cancel a (Rat.ne_of_gt ha)
  have cb := Rat.mul_inv_cancel b (Rat.ne_of_gt hb)
  have cc := Rat.mul_inv_cancel (b*b) (Rat.ne_of_gt (Rat.mul_pos hb hb))
  change (b*b)⁻¹≤a⁻¹-b⁻¹
  apply Rat.le_of_mul_le_mul_right (c := a*(b*b))
  · calc
      _ = a := by grind
      _ ≤ b := by grind
      _ = _ := by grind
  · exact Rat.mul_pos ha (Rat.mul_pos hb hb)

def reciprocalSquareBlock (N : Nat) : Nat → Rat
  | 0 => 0
  | k+1 => reciprocalSquareBlock N k+reciprocalSquare (N+k+1)

theorem reciprocalSquareBlock_bound (N k : Nat) (hN : 0<N) :
    reciprocalSquareBlock N k≤(N:Rat)⁻¹-(((N+k:Nat):Rat))⁻¹ := by
  induction k with
  | zero => simp only [reciprocalSquareBlock,Nat.add_zero]; grind
  | succ k ih =>
    have hs := reciprocalSquare_step (N+k) (by omega)
    change reciprocalSquareBlock N k+reciprocalSquare (N+k+1)≤_
    rw [show N+(k+1)=N+k+1 by omega]
    grind

theorem reciprocalSquareBlock_tail (N k : Nat) (hN : 0<N) :
    reciprocalSquareBlock N k≤(N:Rat)⁻¹ := by
  have h := reciprocalSquareBlock_bound N k hN
  have hp : (0:Rat)<((N+k:Nat):Rat) := by exact_mod_cast (show 0<N+k by omega)
  have hi := Rat.le_of_lt ((Rat.inv_pos).mpr hp)
  grind only

theorem pairedReciprocalTail_shrinks (C : Nat) :
    ShrinksToZero (fun n => (C:Rat)*(((n+1:Nat):Rat))⁻¹) := by
  apply shrinksToZero_of_natOverSuccBound (C := C)
  intro n
  rw [Rat.div_def]
  exact Rat.le_refl

end ComputableAnalysis.ModularForms
