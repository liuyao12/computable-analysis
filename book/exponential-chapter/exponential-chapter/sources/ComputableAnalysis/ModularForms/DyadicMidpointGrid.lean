import ComputableAnalysis.ModularForms.DyadicMidpointAffine

/-! Identification of the recursive sampler with the indexed rational grid. -/
namespace ComputableAnalysis.ModularForms

theorem midpointGrid_left (D j : Rat) (hD : 0<D) :
    ((j+1/2)/D)/2=(j+1/2)/(D+D) := by
  have hp : 0<D+D := by grind only
  have h1 := Rat.mul_inv_cancel D (Rat.ne_of_gt hD)
  have h2 := Rat.mul_inv_cancel (D+D) (Rat.ne_of_gt hp)
  rw [Rat.div_def,Rat.div_def,Rat.div_def]
  grind only

theorem midpointGrid_right (D j : Rat) (hD : 0<D) :
    (1+(j+1/2)/D)/2=(D+j+1/2)/(D+D) := by
  have hp : 0<D+D := by grind only
  have h1 := Rat.mul_inv_cancel D (Rat.ne_of_gt hD)
  have h2 := Rat.mul_inv_cancel (D+D) (Rat.ne_of_gt hp)
  rw [Rat.div_def,Rat.div_def,Rat.div_def]
  grind only

theorem dyadicMidpoints_indexed (n : Nat) :
    dyadicMidpoints ⟨0,1⟩ n =
      (List.range (2^n)).map (fun j : Nat => ((j:Rat)+1/2)/((2^n:Nat):Rat)) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    have hD : 0<((2^n:Nat):Rat) := Rat.natCast_pos.mpr (Nat.pow_pos (by omega))
    have hcount : 2^(n+1)=2^n+2^n := by rw [Nat.pow_succ]; omega
    rw [unitDyadicMidpoints_subdivision,ih,hcount,List.range_add,List.map_append,
      List.map_map,List.map_map,List.map_map]
    congr 1
    · apply List.map_congr_left
      intro j hj
      change (((j:Rat)+1/2)/((2^n:Nat):Rat))/2=
        ((j:Rat)+1/2)/((2^n+2^n:Nat):Rat)
      rw [Rat.natCast_add]
      exact midpointGrid_left _ _ hD
    · apply List.map_congr_left
      intro j hj
      change (1+((j:Rat)+1/2)/((2^n:Nat):Rat))/2=
        (((2^n+j:Nat):Rat)+1/2)/((2^n+2^n:Nat):Rat)
      rw [Rat.natCast_add,Rat.natCast_add]
      exact midpointGrid_right _ _ hD

end ComputableAnalysis.ModularForms
