import ComputableAnalysis.ModularForms.LatticeBasisSquares163
import ComputableAnalysis.ModularForms.UpperFilteredPointBounds
import ComputableAnalysis.ModularForms.LatticeBasisFiniteComparison163
import ComputableAnalysis.ModularForms.FiniteSumDifference
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws

/-! Finite quantitative reindexing comparison for every integral lattice basis change. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

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

theorem upperBasisSquareUnmatchedWeightFour_small (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((basisSquareUnmatched g N).map (upperPointPower z hz 4)))
      (upperWeightFourTailConstant z hz*reciprocalSquare N) :=
  upperFiniteSubsetWeightFour_small z hz N (basisComparisonFactor g*(basisComparisonFactor g*N)) hN _
    (List.Nodup.sublist List.filter_sublist (squarePoints_nodup (basisComparisonFactor g*N)))
    (fun u hu => unmatched_bounds g N u (Or.inl hu))

theorem upperBasisImageUnmatchedWeightFour_small (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((basisImageUnmatched g N).map (upperPointPower z hz 4)))
      (upperWeightFourTailConstant z hz*reciprocalSquare N) :=
  upperFiniteSubsetWeightFour_small z hz N (basisComparisonFactor g*(basisComparisonFactor g*N)) hN _
    (List.Nodup.sublist List.filter_sublist (basisIndex_square_nodup g (basisComparisonFactor g*N)))
    (fun u hu => unmatched_bounds g N u (Or.inr hu))

theorem upperBasisWeightFour_finite_comparison (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (ComplexRaw.sub
      (LocalODE.sum ((squarePoints (basisComparisonFactor g*N)).map (upperPointPower z hz 4)))
      (LocalODE.sum (((squarePoints (basisComparisonFactor g*N)).map (basisIndex g)).map (upperPointPower z hz 4))))
      (upperWeightFourTailConstant z hz*reciprocalSquare N+upperWeightFourTailConstant z hz*reciprocalSquare N) := by
  have hv (us : List QuadraticOrder163) : (LocalODE.sum (us.map (upperPointPower z hz 4))).Valid := by
    apply LocalODE.sum_valid
    intro zz hzz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
    exact upperPointPower_valid z hz 4 u
  have he := representedSum_difference (upperPointPower z hz 4) (upperPointPower_valid z hz 4)
    (squarePoints (basisComparisonFactor g*N))
    ((squarePoints (basisComparisonFactor g*N)).map (basisIndex g))
    (squarePoints_nodup _) (basisIndex_square_nodup g _)
  exact Small.congr
    (ComplexRaw.sub_valid (hv (basisSquareUnmatched g N)) (hv (basisImageUnmatched g N)))
    (ComplexRaw.sub_valid (hv _) (hv _)) (ComplexRaw.equiv_symm he)
    (SeriesLimitLaws.small_sub (upperBasisSquareUnmatchedWeightFour_small z hz g N hN)
      (upperBasisImageUnmatchedWeightFour_small z hz g N hN))

theorem upperBasisSquareUnmatchedWeightSix_small (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((basisSquareUnmatched g N).map (upperPointPower z hz 6)))
      (upperWeightSixTailConstant z hz*reciprocalSquare N) :=
  upperFiniteSubsetWeightSix_small z hz N (basisComparisonFactor g*(basisComparisonFactor g*N)) hN _
    (List.Nodup.sublist List.filter_sublist (squarePoints_nodup (basisComparisonFactor g*N)))
    (fun u hu => unmatched_bounds g N u (Or.inl hu))

theorem upperBasisImageUnmatchedWeightSix_small (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (LocalODE.sum ((basisImageUnmatched g N).map (upperPointPower z hz 6)))
      (upperWeightSixTailConstant z hz*reciprocalSquare N) :=
  upperFiniteSubsetWeightSix_small z hz N (basisComparisonFactor g*(basisComparisonFactor g*N)) hN _
    (List.Nodup.sublist List.filter_sublist (basisIndex_square_nodup g (basisComparisonFactor g*N)))
    (fun u hu => unmatched_bounds g N u (Or.inr hu))

theorem upperBasisWeightSix_finite_comparison (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (N : Nat) (hN : 0<N) :
    Small (ComplexRaw.sub
      (LocalODE.sum ((squarePoints (basisComparisonFactor g*N)).map (upperPointPower z hz 6)))
      (LocalODE.sum (((squarePoints (basisComparisonFactor g*N)).map (basisIndex g)).map (upperPointPower z hz 6))))
      (upperWeightSixTailConstant z hz*reciprocalSquare N+upperWeightSixTailConstant z hz*reciprocalSquare N) := by
  have hv (us : List QuadraticOrder163) : (LocalODE.sum (us.map (upperPointPower z hz 6))).Valid := by
    apply LocalODE.sum_valid
    intro zz hzz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
    exact upperPointPower_valid z hz 6 u
  have he := representedSum_difference (upperPointPower z hz 6) (upperPointPower_valid z hz 6)
    (squarePoints (basisComparisonFactor g*N))
    ((squarePoints (basisComparisonFactor g*N)).map (basisIndex g))
    (squarePoints_nodup _) (basisIndex_square_nodup g _)
  exact Small.congr
    (ComplexRaw.sub_valid (hv (basisSquareUnmatched g N)) (hv (basisImageUnmatched g N)))
    (ComplexRaw.sub_valid (hv _) (hv _)) (ComplexRaw.equiv_symm he)
    (SeriesLimitLaws.small_sub (upperBasisSquareUnmatchedWeightSix_small z hz g N hN)
      (upperBasisImageUnmatchedWeightSix_small z hz g N hN))

end ComputableAnalysis.ModularForms
