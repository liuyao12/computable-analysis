import ComputableAnalysis.ModularForms.UpperLatticePointTerms
import ComputableAnalysis.ModularForms.RepresentedSumAppend
import ComputableAnalysis.ModularForms.UpperWeightFourSum
import ComputableAnalysis.ModularForms.UpperWeightSixSum

/-! Exact agreement of square point sums with constructed lattice-sum prefixes. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

private theorem upperPointList_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (w : Nat) (us : List QuadraticOrder163) :
    ∀ zz ∈ us.map (upperPointPower z hz w), zz.Valid := by
  intro zz hzz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
  exact upperPointPower_valid z hz w u

theorem upperSquareWeightFour_tailBlock_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    (LocalODE.sum ((squarePoints N).map (upperPointPower z hz 4))).Equiv (upperWeightFourTailBlock z hz 0 N) := by
  induction N with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ N ih =>
    rw [squarePoints_succ,List.map_append]
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (by
        intro zz hzz
        rcases List.mem_append.mp hzz with h|h
        · exact upperPointList_valid z hz 4 _ zz h
        · exact upperPointList_valid z hz 4 _ zz h))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (upperPointList_valid z hz 4 _))
        (LocalODE.sum_valid _ (upperPointList_valid z hz 4 _)))
      (upperWeightFourTailBlock_valid z hz 0 (N+1))
      (representedSum_append ((squarePoints N).map (upperPointPower z hz 4))
        ((shellPoints (N+1)).map (upperPointPower z hz 4))
        (upperPointList_valid z hz 4 (squarePoints N)) (upperPointList_valid z hz 4 (shellPoints (N+1))))
      (by
        change (ComplexRaw.add (LocalODE.sum ((squarePoints N).map (upperPointPower z hz 4)))
          (LocalODE.sum ((shellPoints (N+1)).map (upperPointPower z hz 4)))).Equiv
          (ComplexRaw.add (upperWeightFourTailBlock z hz 0 N) (upperShellSum z hz (0+N+1) (by omega) 4))
        simp only [Nat.zero_add]
        exact ComplexRaw.add_equiv ih
          (ComplexRaw.equiv_symm (upperShellSum_point_list_equiv z hz 4 (N+1) (by omega))))

theorem upperSquareWeightFour_prefix_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) :
    (LocalODE.sum ((squarePoints (n+1)).map (upperPointPower z hz 4))).Equiv (upperWeightFourPrefix z hz n) :=
  upperSquareWeightFour_tailBlock_equiv z hz (n+1)

theorem upperSquareWeightSix_tailBlock_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    (LocalODE.sum ((squarePoints N).map (upperPointPower z hz 6))).Equiv (upperWeightSixTailBlock z hz 0 N) := by
  induction N with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ N ih =>
    rw [squarePoints_succ,List.map_append]
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (by
        intro zz hzz
        rcases List.mem_append.mp hzz with h|h
        · exact upperPointList_valid z hz 6 _ zz h
        · exact upperPointList_valid z hz 6 _ zz h))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (upperPointList_valid z hz 6 _))
        (LocalODE.sum_valid _ (upperPointList_valid z hz 6 _)))
      (upperWeightSixTailBlock_valid z hz 0 (N+1))
      (representedSum_append ((squarePoints N).map (upperPointPower z hz 6))
        ((shellPoints (N+1)).map (upperPointPower z hz 6))
        (upperPointList_valid z hz 6 (squarePoints N)) (upperPointList_valid z hz 6 (shellPoints (N+1))))
      (by
        change (ComplexRaw.add (LocalODE.sum ((squarePoints N).map (upperPointPower z hz 6)))
          (LocalODE.sum ((shellPoints (N+1)).map (upperPointPower z hz 6)))).Equiv
          (ComplexRaw.add (upperWeightSixTailBlock z hz 0 N) (upperShellSum z hz (0+N+1) (by omega) 6))
        simp only [Nat.zero_add]
        exact ComplexRaw.add_equiv ih
          (ComplexRaw.equiv_symm (upperShellSum_point_list_equiv z hz 6 (N+1) (by omega))))

theorem upperSquareWeightSix_prefix_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) :
    (LocalODE.sum ((squarePoints (n+1)).map (upperPointPower z hz 6))).Equiv (upperWeightSixPrefix z hz n) :=
  upperSquareWeightSix_tailBlock_equiv z hz (n+1)

end ComputableAnalysis.ModularForms
