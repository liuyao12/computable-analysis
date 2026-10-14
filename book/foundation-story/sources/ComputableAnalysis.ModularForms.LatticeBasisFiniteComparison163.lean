import ComputableAnalysis.ModularForms.LatticeBasisSquares163
import ComputableAnalysis.ModularForms.CMFilteredPointTerms163
import ComputableAnalysis.ModularForms.FiniteSumDifference
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws

/-! Finite quantitative reindexing comparison for every integral lattice basis change. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert FunctionTheory

def basisSquareUnmatched (g : SL2Z) (N : Nat) : List QuadraticOrder163 :=
  (squarePoints (basisComparisonFactor g*N)).filter
    (fun u => !decide (u ∈ (squarePoints (basisComparisonFactor g*N)).map (basisIndex g)))

def basisImageUnmatched (g : SL2Z) (N : Nat) : List QuadraticOrder163 :=
  ((squarePoints (basisComparisonFactor g*N)).map (basisIndex g)).filter
    (fun u => !decide (u ∈ squarePoints (basisComparisonFactor g*N)))

private theorem unmatched_bounds (g : SL2Z) (N : Nat) (u : QuadraticOrder163)
    (h : u ∈ basisSquareUnmatched g N ∨ u ∈ basisImageUnmatched g N) :
    u≠zero ∧ N<shellRadius u ∧
      shellRadius u≤N+basisComparisonFactor g*(basisComparisonFactor g*N) := by
  have hm : (u ∈ squarePoints (basisComparisonFactor g*N) ∧
      u ∉ (squarePoints (basisComparisonFactor g*N)).map (basisIndex g)) ∨
      (u ∈ (squarePoints (basisComparisonFactor g*N)).map (basisIndex g) ∧
        u ∉ squarePoints (basisComparisonFactor g*N)) := by
    rcases h with h|h
    · exact Or.inl (by simpa [basisSquareUnmatched] using h)
    · exact Or.inr (by simpa [basisImageUnmatched] using h)
  have hr := basis_square_unmatched_radius g N u hm
  have hb := basis_square_union_radius g N u (by
    rcases hm with h|h
    · exact Or.inl h.1
    · exact Or.inr h.1)
  exact ⟨hb.1,hr,by omega⟩

theorem basisSquareUnmatchedWeightFour_small (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((basisSquareUnmatched g N).map (pointPower 4)))
      (weightFourTailConstant*reciprocalSquare N) :=
  finiteSubsetWeightFour_small N (basisComparisonFactor g*(basisComparisonFactor g*N)) hN _
    (List.Nodup.sublist List.filter_sublist (squarePoints_nodup (basisComparisonFactor g*N)))
    (fun u hu => unmatched_bounds g N u (Or.inl hu))

theorem basisImageUnmatchedWeightFour_small (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((basisImageUnmatched g N).map (pointPower 4)))
      (weightFourTailConstant*reciprocalSquare N) :=
  finiteSubsetWeightFour_small N (basisComparisonFactor g*(basisComparisonFactor g*N)) hN _
    (List.Nodup.sublist List.filter_sublist (basisIndex_square_nodup g (basisComparisonFactor g*N)))
    (fun u hu => unmatched_bounds g N u (Or.inr hu))

theorem basisWeightFour_finite_comparison (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (ComplexRaw.sub
      (LocalODE.sum ((squarePoints (basisComparisonFactor g*N)).map (pointPower 4)))
      (LocalODE.sum (((squarePoints (basisComparisonFactor g*N)).map (basisIndex g)).map (pointPower 4))))
      (weightFourTailConstant*reciprocalSquare N+weightFourTailConstant*reciprocalSquare N) := by
  have hv (us : List QuadraticOrder163) : (LocalODE.sum (us.map (pointPower 4))).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact pointPower_valid 4 u
  have he := representedSum_difference (pointPower 4) (pointPower_valid 4)
    (squarePoints (basisComparisonFactor g*N))
    ((squarePoints (basisComparisonFactor g*N)).map (basisIndex g))
    (squarePoints_nodup _) (basisIndex_square_nodup g _)
  exact Small.congr
    (ComplexRaw.sub_valid (hv (basisSquareUnmatched g N)) (hv (basisImageUnmatched g N)))
    (ComplexRaw.sub_valid (hv _) (hv _)) (ComplexRaw.equiv_symm he)
    (SeriesLimitLaws.small_sub (basisSquareUnmatchedWeightFour_small g N hN)
      (basisImageUnmatchedWeightFour_small g N hN))

theorem basisSquareUnmatchedWeightSix_small (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((basisSquareUnmatched g N).map (pointPower 6)))
      (weightSixTailConstant*reciprocalSquare N) :=
  finiteSubsetWeightSix_small N (basisComparisonFactor g*(basisComparisonFactor g*N)) hN _
    (List.Nodup.sublist List.filter_sublist (squarePoints_nodup (basisComparisonFactor g*N)))
    (fun u hu => unmatched_bounds g N u (Or.inl hu))

theorem basisImageUnmatchedWeightSix_small (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((basisImageUnmatched g N).map (pointPower 6)))
      (weightSixTailConstant*reciprocalSquare N) :=
  finiteSubsetWeightSix_small N (basisComparisonFactor g*(basisComparisonFactor g*N)) hN _
    (List.Nodup.sublist List.filter_sublist (basisIndex_square_nodup g (basisComparisonFactor g*N)))
    (fun u hu => unmatched_bounds g N u (Or.inr hu))

theorem basisWeightSix_finite_comparison (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (ComplexRaw.sub
      (LocalODE.sum ((squarePoints (basisComparisonFactor g*N)).map (pointPower 6)))
      (LocalODE.sum (((squarePoints (basisComparisonFactor g*N)).map (basisIndex g)).map (pointPower 6))))
      (weightSixTailConstant*reciprocalSquare N+weightSixTailConstant*reciprocalSquare N) := by
  have hv (us : List QuadraticOrder163) : (LocalODE.sum (us.map (pointPower 6))).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact pointPower_valid 6 u
  have he := representedSum_difference (pointPower 6) (pointPower_valid 6)
    (squarePoints (basisComparisonFactor g*N))
    ((squarePoints (basisComparisonFactor g*N)).map (basisIndex g))
    (squarePoints_nodup _) (basisIndex_square_nodup g _)
  exact Small.congr
    (ComplexRaw.sub_valid (hv (basisSquareUnmatched g N)) (hv (basisImageUnmatched g N)))
    (ComplexRaw.sub_valid (hv _) (hv _)) (ComplexRaw.equiv_symm he)
    (SeriesLimitLaws.small_sub (basisSquareUnmatchedWeightSix_small g N hN)
      (basisImageUnmatchedWeightSix_small g N hN))

end ComputableAnalysis.ModularForms.QuadraticOrder163
