import ComputableAnalysis.ModularForms.UpperCommonRegion
import ComputableAnalysis.ModularForms.UpperDerivativeFourTails
import ComputableAnalysis.ModularForms.UpperDerivativeSixTails

/-! Local uniform derivative-tail estimates for both constructed lattice sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory ComplexRaw

def localDerivativeWeightFourTailRate (a : Scalar) (ha : InUpperHalfPlane a.val) (n : Nat) : Rat :=
  regionalDerivativeFourTailConstant (neighborhoodRegionWidth a ha) (neighborhoodRegionWidth a ha)
    (neighborhoodRegionMargin a ha)*reciprocalSquare (n+1)

theorem localDerivativeWeightFourTailRate_shrinks (a : Scalar) (ha : InUpperHalfPlane a.val) :
    ShrinksToZero (localDerivativeWeightFourTailRate a ha) := by
  have he : ShrinksToZero (fun n => reciprocalSquare (n+1)) := by
    apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    change reciprocalSquare (n+1)≤1/((n+1:Nat):Rat)
    exact reciprocalSquare_le_reciprocal (n+1) (by omega)
  have hC : 0≤regionalDerivativeFourTailConstant (neighborhoodRegionWidth a ha)
      (neighborhoodRegionWidth a ha) (neighborhoodRegionMargin a ha) := by
    unfold regionalDerivativeFourTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg (Rat.mul_nonneg (by decide)
      (latticeRegionReciprocalConstant_nonnegative _ _ _
        (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
        (neighborhoodRegionMargin_positive a ha))))
  exact SeriesLimitLaws.shrinks_scale _ he _ hC

/-- A common rate bounds every finite derivative tail in the neighborhood. -/
theorem derivativeWeightFourTailBlock_local_small (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) (n k : Nat) :
    Small (derivativeWeightFourTailBlock z hz (n+1) k)
      (localDerivativeWeightFourTailRate a ha n) := by
  obtain ⟨S,hregion,hheight⟩ := upperCommonRegion a ha z hs
  exact derivativeWeightFourTailBlock_uniform_small z hz _ _ _ S
    (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
    (neighborhoodRegionMargin_positive a ha) hregion hheight (n+1) k (by omega)

def localDerivativeWeightSixTailRate (a : Scalar) (ha : InUpperHalfPlane a.val) (n : Nat) : Rat :=
  regionalDerivativeSixTailConstant (neighborhoodRegionWidth a ha) (neighborhoodRegionWidth a ha)
    (neighborhoodRegionMargin a ha)*reciprocalSquare (n+1)

theorem localDerivativeWeightSixTailRate_shrinks (a : Scalar) (ha : InUpperHalfPlane a.val) :
    ShrinksToZero (localDerivativeWeightSixTailRate a ha) := by
  have he : ShrinksToZero (fun n => reciprocalSquare (n+1)) := by
    apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    change reciprocalSquare (n+1)≤1/((n+1:Nat):Rat)
    exact reciprocalSquare_le_reciprocal (n+1) (by omega)
  have hC : 0≤regionalDerivativeSixTailConstant (neighborhoodRegionWidth a ha)
      (neighborhoodRegionWidth a ha) (neighborhoodRegionMargin a ha) := by
    unfold regionalDerivativeSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg (Rat.mul_nonneg (by decide)
      (latticeRegionReciprocalConstant_nonnegative _ _ _
        (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
        (neighborhoodRegionMargin_positive a ha))))
  exact SeriesLimitLaws.shrinks_scale _ he _ hC

/-- A common rate bounds every finite derivative tail in the neighborhood. -/
theorem derivativeWeightSixTailBlock_local_small (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) (n k : Nat) :
    Small (derivativeWeightSixTailBlock z hz (n+1) k)
      (localDerivativeWeightSixTailRate a ha n) := by
  obtain ⟨S,hregion,hheight⟩ := upperCommonRegion a ha z hs
  exact derivativeWeightSixTailBlock_uniform_small z hz _ _ _ S
    (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
    (neighborhoodRegionMargin_positive a ha) hregion hheight (n+1) k (by omega)

end ComputableAnalysis.ModularForms
