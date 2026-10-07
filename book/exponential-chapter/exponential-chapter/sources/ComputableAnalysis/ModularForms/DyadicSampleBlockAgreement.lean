import ComputableAnalysis.ModularForms.DyadicMidpointGrid

/-! Indexed sample-list sums agree with the existing finite block evaluator. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem sampleListSum_range_block (f : Rat → Scalar) (grid : Nat → Rat) (N : Nat) :
    (sampleListSum f ((List.range N).map grid)).val.Equiv
      (ScalarSeries.block (fun j => (f (grid j)).val) 0 N) := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (sampleListSum f ((List.range (N+1)).map grid)).property)
      (hright := ScalarSeries.block_valid _ (fun j => (f (grid j)).property) 0 (N+1))
    have hp := sampleListSum_append f ((List.range N).map grid) [grid N]
    have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (sampleListSum f (((List.range N).map grid)++[grid N])).property)
      (hright := add_valid (sampleListSum f ((List.range N).map grid)).property
        (sampleListSum f [grid N]).property) hp
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (sampleListSum f ((List.range N).map grid)).property)
      (hright := ScalarSeries.block_valid _ (fun j => (f (grid j)).property) 0 N) ih
    let S := ComplexRawQuotient.ofRaw (sampleListSum f ((List.range N).map grid)).val
      (sampleListSum f ((List.range N).map grid)).property
    let B := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun j => (f (grid j)).val) 0 N)
      (ScalarSeries.block_valid _ (fun j => (f (grid j)).property) 0 N)
    let X := ComplexRawQuotient.ofRaw (f (grid N)).val (f (grid N)).property
    rw [List.range_succ,List.map_append]
    simp only [List.map_cons,List.map_nil,ScalarSeries.block,Nat.zero_add]
    change ComplexRawQuotient.ofRaw
      (sampleListSum f (((List.range N).map grid)++[grid N])).val _=B+X
    change ComplexRawQuotient.ofRaw
      (sampleListSum f (((List.range N).map grid)++[grid N])).val _=S+(X+0) at hs
    change S=B at hi
    rw [hs,hi]
    grind only

theorem dyadicSampleAverage_block (f : Rat → Scalar) (n : Nat) :
    (dyadicSampleAverage f ⟨0,1⟩ n).val.Equiv
      (scaleRat (((2^n:Nat):Rat)⁻¹) (ScalarSeries.block
        (fun j => (f (((j:Rat)+1/2)/((2^n:Nat):Rat))).val) 0 (2^n))) := by
  have hf := dyadicSampleAverage_flatten f ⟨0,1⟩ n
  rw [dyadicMidpoints_indexed] at hf
  have hs := sampleListSum_range_block f
    (fun j : Nat => ((j:Rat)+1/2)/((2^n:Nat):Rat)) (2^n)
  have hc : ((1:Rat)/2)^n=((2^n:Nat):Rat)⁻¹ := by
    rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow,Rat.div_def,Rat.one_mul]
  rw [hc] at hf
  exact equiv_trans (dyadicSampleAverage f ⟨0,1⟩ n).property
    (scaleRat_valid (sampleListSum f ((List.range (2^n)).map
      (fun j : Nat => ((j:Rat)+1/2)/((2^n:Nat):Rat)))).property)
    (scaleRat_valid (ScalarSeries.block_valid _ (fun j => (f _).property) 0 (2^n))) hf
    (ComplexRaw.scaleRat_equiv_of_nonneg
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (Nat.pow_pos (by omega))))) hs)

end ComputableAnalysis.ModularForms
