import ComputableAnalysis.ModularForms.CMUnmatchedBounds163
import ComputableAnalysis.ModularForms.FiniteSumDifference
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws

/-! Shrinking bounds for the concrete finite conjugation reindexing comparison. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert FunctionTheory

theorem squareWeightFour_conjugate_enumeration_small (N : Nat) (hN : 0<N) :
    Small (ComplexRaw.sub
      (LocalODE.sum ((squarePoints (2*N)).map (pointPower 4)))
      (LocalODE.sum (((squarePoints (2*N)).map conjugate).map (pointPower 4))))
      (weightFourTailConstant*reciprocalSquare N+weightFourTailConstant*reciprocalSquare N) := by
  have hv (us : List QuadraticOrder163) : (LocalODE.sum (us.map (pointPower 4))).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact pointPower_valid 4 u
  have he := representedSum_difference (pointPower 4) (pointPower_valid 4)
    (squarePoints (2*N)) ((squarePoints (2*N)).map conjugate)
    (squarePoints_nodup (2*N)) (conjugate_squarePoints_nodup (2*N))
  exact Small.congr (ComplexRaw.sub_valid (hv (squareUnmatched N)) (hv (conjugateUnmatched N)))
    (ComplexRaw.sub_valid (hv _) (hv _)) (ComplexRaw.equiv_symm he)
    (SeriesLimitLaws.small_sub (squareUnmatchedWeightFour_small N hN)
      (conjugateUnmatchedWeightFour_small N hN))

theorem squareWeightSix_conjugate_enumeration_small (N : Nat) (hN : 0<N) :
    Small (ComplexRaw.sub
      (LocalODE.sum ((squarePoints (2*N)).map (pointPower 6)))
      (LocalODE.sum (((squarePoints (2*N)).map conjugate).map (pointPower 6))))
      (weightSixTailConstant*reciprocalSquare N+weightSixTailConstant*reciprocalSquare N) := by
  have hv (us : List QuadraticOrder163) : (LocalODE.sum (us.map (pointPower 6))).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact pointPower_valid 6 u
  have he := representedSum_difference (pointPower 6) (pointPower_valid 6)
    (squarePoints (2*N)) ((squarePoints (2*N)).map conjugate)
    (squarePoints_nodup (2*N)) (conjugate_squarePoints_nodup (2*N))
  exact Small.congr (ComplexRaw.sub_valid (hv (squareUnmatched N)) (hv (conjugateUnmatched N)))
    (ComplexRaw.sub_valid (hv _) (hv _)) (ComplexRaw.equiv_symm he)
    (SeriesLimitLaws.small_sub (squareUnmatchedWeightSix_small N hN)
      (conjugateUnmatchedWeightSix_small N hN))

end ComputableAnalysis.ModularForms.QuadraticOrder163
