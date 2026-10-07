import ComputableAnalysis.ModularForms.UpperDerivativeShellAgreement
import ComputableAnalysis.ModularForms.RepresentedSumAppend
import ComputableAnalysis.ModularForms.UpperDerivativeFourTails
import ComputableAnalysis.ModularForms.UpperDerivativeSixTails

/-! Exact agreement of square point sums with constructed lattice-sum prefixes. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

private theorem derivativePointList_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (w : Nat) (us : List QuadraticOrder163) :
    ∀ zz ∈ us.map (upperPointDerivative z hz w), zz.Valid := by
  intro zz hzz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
  exact upperPointDerivative_valid z hz w u

private theorem derivativeShellSum_point_list_equiv (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k r : Nat) (hr : 0<r) :
    (derivativeShellSum z hz r hr k).Equiv
      (LocalODE.sum ((shellPoints r).map (upperPointDerivative z hz k))) := by
  rw [derivativeShellPoints_term_list z hz k r hr]
  exact derivativeShellSum_list_equiv z hz r hr k

theorem derivativeSquareWeightFour_tailBlock_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    (LocalODE.sum ((squarePoints N).map (upperPointDerivative z hz 4))).Equiv (derivativeWeightFourTailBlock z hz 0 N) := by
  induction N with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ N ih =>
    rw [squarePoints_succ,List.map_append]
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (by
        intro zz hzz
        rcases List.mem_append.mp hzz with h|h
        · exact derivativePointList_valid z hz 4 _ zz h
        · exact derivativePointList_valid z hz 4 _ zz h))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (derivativePointList_valid z hz 4 _))
        (LocalODE.sum_valid _ (derivativePointList_valid z hz 4 _)))
      (derivativeWeightFourTailBlock_valid z hz 0 (N+1))
      (representedSum_append ((squarePoints N).map (upperPointDerivative z hz 4))
        ((shellPoints (N+1)).map (upperPointDerivative z hz 4))
        (derivativePointList_valid z hz 4 (squarePoints N)) (derivativePointList_valid z hz 4 (shellPoints (N+1))))
      (by
        change (ComplexRaw.add (LocalODE.sum ((squarePoints N).map (upperPointDerivative z hz 4)))
          (LocalODE.sum ((shellPoints (N+1)).map (upperPointDerivative z hz 4)))).Equiv
          (ComplexRaw.add (derivativeWeightFourTailBlock z hz 0 N) (derivativeShellSum z hz (0+N+1) (by omega) 4))
        simp only [Nat.zero_add]
        exact ComplexRaw.add_equiv ih
          (ComplexRaw.equiv_symm (derivativeShellSum_point_list_equiv z hz 4 (N+1) (by omega))))

theorem derivativeSquareWeightSix_tailBlock_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    (LocalODE.sum ((squarePoints N).map (upperPointDerivative z hz 6))).Equiv (derivativeWeightSixTailBlock z hz 0 N) := by
  induction N with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ N ih =>
    rw [squarePoints_succ,List.map_append]
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (by
        intro zz hzz
        rcases List.mem_append.mp hzz with h|h
        · exact derivativePointList_valid z hz 6 _ zz h
        · exact derivativePointList_valid z hz 6 _ zz h))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (derivativePointList_valid z hz 6 _))
        (LocalODE.sum_valid _ (derivativePointList_valid z hz 6 _)))
      (derivativeWeightSixTailBlock_valid z hz 0 (N+1))
      (representedSum_append ((squarePoints N).map (upperPointDerivative z hz 6))
        ((shellPoints (N+1)).map (upperPointDerivative z hz 6))
        (derivativePointList_valid z hz 6 (squarePoints N)) (derivativePointList_valid z hz 6 (shellPoints (N+1))))
      (by
        change (ComplexRaw.add (LocalODE.sum ((squarePoints N).map (upperPointDerivative z hz 6)))
          (LocalODE.sum ((shellPoints (N+1)).map (upperPointDerivative z hz 6)))).Equiv
          (ComplexRaw.add (derivativeWeightSixTailBlock z hz 0 N) (derivativeShellSum z hz (0+N+1) (by omega) 6))
        simp only [Nat.zero_add]
        exact ComplexRaw.add_equiv ih
          (ComplexRaw.equiv_symm (derivativeShellSum_point_list_equiv z hz 6 (N+1) (by omega))))

theorem upperSquareWeightFour_derivative_tailBlock (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) :
    ((upperFiniteMap_holomorphic 4 (squarePoints N)).derivative z hz).val.Equiv
      (derivativeWeightFourTailBlock z hz 0 N) := by
  rw [upperFiniteMap_derivative]
  exact derivativeSquareWeightFour_tailBlock_equiv z hz N

theorem upperSquareWeightSix_derivative_tailBlock (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) :
    ((upperFiniteMap_holomorphic 6 (squarePoints N)).derivative z hz).val.Equiv
      (derivativeWeightSixTailBlock z hz 0 N) := by
  rw [upperFiniteMap_derivative]
  exact derivativeSquareWeightSix_tailBlock_equiv z hz N

end ComputableAnalysis.ModularForms
