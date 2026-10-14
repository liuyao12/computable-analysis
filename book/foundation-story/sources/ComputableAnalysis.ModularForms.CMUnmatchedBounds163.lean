import ComputableAnalysis.ModularForms.CMFilteredPointTerms163

/-! Quantitative bounds for the actual unmatched square/conjugate-square terms. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert FunctionTheory

private theorem subset_bounds_of_annulus_perm (N k : Nat) (us : List QuadraticOrder163)
    (h : us.Perm ((annulusPoints N k).filter (fun u => decide (u ∈ us)))) :
    ∀ u ∈ us, u≠zero ∧ N<shellRadius u ∧ shellRadius u≤N+k := by
  intro u hu
  have hf := h.mem_iff.mp hu
  exact (mem_annulusPoints u N k).mp (List.mem_filter.mp hf).1

theorem squareUnmatchedWeightFour_small (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((squareUnmatched N).map (pointPower 4)))
      (weightFourTailConstant*reciprocalSquare N) :=
  finiteSubsetWeightFour_small N (3*N) hN (squareUnmatched N)
    (List.Nodup.sublist List.filter_sublist (squarePoints_nodup (2*N)))
    (subset_bounds_of_annulus_perm N (3*N) _ (squareUnmatched_annulus_perm N))

theorem conjugateUnmatchedWeightFour_small (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((conjugateUnmatched N).map (pointPower 4)))
      (weightFourTailConstant*reciprocalSquare N) :=
  finiteSubsetWeightFour_small N (3*N) hN (conjugateUnmatched N)
    (List.Nodup.sublist List.filter_sublist (conjugate_squarePoints_nodup (2*N)))
    (subset_bounds_of_annulus_perm N (3*N) _ (conjugateUnmatched_annulus_perm N))

theorem squareUnmatchedWeightSix_small (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((squareUnmatched N).map (pointPower 6)))
      (weightSixTailConstant*reciprocalSquare N) :=
  finiteSubsetWeightSix_small N (3*N) hN (squareUnmatched N)
    (List.Nodup.sublist List.filter_sublist (squarePoints_nodup (2*N)))
    (subset_bounds_of_annulus_perm N (3*N) _ (squareUnmatched_annulus_perm N))

theorem conjugateUnmatchedWeightSix_small (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((conjugateUnmatched N).map (pointPower 6)))
      (weightSixTailConstant*reciprocalSquare N) :=
  finiteSubsetWeightSix_small N (3*N) hN (conjugateUnmatched N)
    (List.Nodup.sublist List.filter_sublist (conjugate_squarePoints_nodup (2*N)))
    (subset_bounds_of_annulus_perm N (3*N) _ (conjugateUnmatched_annulus_perm N))

end ComputableAnalysis.ModularForms.QuadraticOrder163
