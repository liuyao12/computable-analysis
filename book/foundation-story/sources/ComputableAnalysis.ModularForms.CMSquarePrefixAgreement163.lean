import ComputableAnalysis.ModularForms.CMFiniteConjugationComparison163
import ComputableAnalysis.ModularForms.RepresentedSumAppend
import ComputableAnalysis.ModularForms.CMWeightSixSum163

/-! Exact agreement of square point sums with constructed lattice-sum prefixes. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert

private theorem pointList_valid (w : Nat) (us : List QuadraticOrder163) :
    ∀ z ∈ us.map (pointPower w), z.Valid := by
  intro z hz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
  exact pointPower_valid w u

theorem squareWeightFour_tailBlock_equiv (N : Nat) :
    (LocalODE.sum ((squarePoints N).map (pointPower 4))).Equiv (weightFourTailBlock 0 N) := by
  induction N with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ N ih =>
    rw [squarePoints_succ,List.map_append]
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (by
        intro z hz
        rcases List.mem_append.mp hz with h|h
        · exact pointList_valid 4 _ z h
        · exact pointList_valid 4 _ z h))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (pointList_valid 4 _))
        (LocalODE.sum_valid _ (pointList_valid 4 _)))
      (weightFourTailBlock_valid 0 (N+1))
      (representedSum_append ((squarePoints N).map (pointPower 4))
        ((shellPoints (N+1)).map (pointPower 4))
        (pointList_valid 4 (squarePoints N)) (pointList_valid 4 (shellPoints (N+1))))
      (by
        change (ComplexRaw.add (LocalODE.sum ((squarePoints N).map (pointPower 4)))
          (LocalODE.sum ((shellPoints (N+1)).map (pointPower 4)))).Equiv
          (ComplexRaw.add (weightFourTailBlock 0 N) (shellSum (0+N+1) (by omega) 4))
        simp only [Nat.zero_add]
        exact ComplexRaw.add_equiv ih
          (ComplexRaw.equiv_symm (shellSum_point_list_equiv 4 (N+1) (by omega))))

theorem squareWeightFour_prefix_equiv (n : Nat) :
    (LocalODE.sum ((squarePoints (n+1)).map (pointPower 4))).Equiv (weightFourPrefix n) :=
  squareWeightFour_tailBlock_equiv (n+1)

theorem squareWeightSix_tailBlock_equiv (N : Nat) :
    (LocalODE.sum ((squarePoints N).map (pointPower 6))).Equiv (weightSixTailBlock 0 N) := by
  induction N with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ N ih =>
    rw [squarePoints_succ,List.map_append]
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (by
        intro z hz
        rcases List.mem_append.mp hz with h|h
        · exact pointList_valid 6 _ z h
        · exact pointList_valid 6 _ z h))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (pointList_valid 6 _))
        (LocalODE.sum_valid _ (pointList_valid 6 _)))
      (weightSixTailBlock_valid 0 (N+1))
      (representedSum_append ((squarePoints N).map (pointPower 6))
        ((shellPoints (N+1)).map (pointPower 6))
        (pointList_valid 6 (squarePoints N)) (pointList_valid 6 (shellPoints (N+1))))
      (by
        change (ComplexRaw.add (LocalODE.sum ((squarePoints N).map (pointPower 6)))
          (LocalODE.sum ((shellPoints (N+1)).map (pointPower 6)))).Equiv
          (ComplexRaw.add (weightSixTailBlock 0 N) (shellSum (0+N+1) (by omega) 6))
        simp only [Nat.zero_add]
        exact ComplexRaw.add_equiv ih
          (ComplexRaw.equiv_symm (shellSum_point_list_equiv 6 (N+1) (by omega))))

theorem squareWeightSix_prefix_equiv (n : Nat) :
    (LocalODE.sum ((squarePoints (n+1)).map (pointPower 6))).Equiv (weightSixPrefix n) :=
  squareWeightSix_tailBlock_equiv (n+1)

end ComputableAnalysis.ModularForms.QuadraticOrder163
