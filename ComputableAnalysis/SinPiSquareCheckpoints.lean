import ComputableAnalysis.SinPiSquareFTC

/-!
# Executable nested-radical square checkpoints

These small regression theorems are kept outside the main sine-square module:
the exact rational search is computationally expensive, while the underlying
interval transport remains in `SinPiSquareFTC`.
-/

namespace ComputableAnalysis
namespace SinPiIntegral

/-! Separate grid membership from the arithmetic admissibility proof.  This
adapter lets a client certify a candidate with small local lemmas instead of
repeating the full nested-radical expression in the search-completeness
theorem. -/
theorem rationalTangentSquareWitnessSearch_complete_of_candidate
    {U S C : QInterval} {m : Nat} {u : Rat}
    (hmem : u ∈ rationalTangentWitnessBoxGrid U m)
    (hadm : rationalTangentSquareWitnessAdmissibleBool U S C u = true) :
    ∃ v, rationalTangentSquareWitnessSearch U S C m = some v := by
  exact rationalTangentSquareWitnessSearchList_complete hmem hadm

theorem rationalTangentSquareWitnessSearch_stage_two_right_demo :
    rationalTangentSquareWitnessSearch
      ({ lo := 1, hi := 2 } : QInterval)
      (dyadicNestedRadicalStageSinAt 2 3)
      (dyadicNestedRadicalStageTable 2 3).2 8 =
        some ((379 : Rat) / 256) := by
  native_decide

theorem dyadicNestedRadicalStage_two_right_square_complement_overlap :
    QInterval.Overlaps
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt 2 3))
      (rationalOneMinusSquareIntervalSigned
        (dyadicNestedRadicalStageTable 2 3).2) := by
  have hsearch := rationalTangentSquareWitnessSearch_stage_two_right_demo
  have hS : subintervalOf (dyadicNestedRadicalStageSinAt 2 3) 0 1 := by
    unfold subintervalOf
    constructor
    · native_decide
    constructor <;> native_decide
  have hC : subintervalOf (dyadicNestedRadicalStageTable 2 3).2 (-1) 1 := by
    unfold subintervalOf
    constructor
    · native_decide
    constructor <;> native_decide
  exact signed_square_overlap_of_rationalTangentSquareWitnessSearch hsearch hS hC

end SinPiIntegral
end ComputableAnalysis
