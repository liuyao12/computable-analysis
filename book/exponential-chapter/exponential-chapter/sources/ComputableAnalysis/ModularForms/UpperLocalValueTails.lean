import ComputableAnalysis.ModularForms.UpperCommonRegion
import ComputableAnalysis.ModularForms.UpperRegionalSumRemainder

/-! Local uniform value-tail estimates for both constructed lattice sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory ComplexRaw

def localWeightFourTailRate (a : Scalar) (ha : InUpperHalfPlane a.val) (n : Nat) : Rat :=
  regionalWeightFourTailConstant (neighborhoodRegionWidth a ha) (neighborhoodRegionWidth a ha)
    (neighborhoodRegionMargin a ha)*reciprocalSquare (n+1)

theorem localWeightFourTailRate_shrinks (a : Scalar) (ha : InUpperHalfPlane a.val) :
    ShrinksToZero (localWeightFourTailRate a ha) := by
  have he : ShrinksToZero (fun n => reciprocalSquare (n+1)) := by
    apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    change reciprocalSquare (n+1)≤1/((n+1:Nat):Rat)
    exact reciprocalSquare_le_reciprocal (n+1) (by omega)
  have hC : 0≤regionalWeightFourTailConstant (neighborhoodRegionWidth a ha)
      (neighborhoodRegionWidth a ha) (neighborhoodRegionMargin a ha) := by
    unfold regionalWeightFourTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg (Rat.mul_nonneg (by decide)
      (latticeRegionReciprocalConstant_nonnegative _ _ _
        (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
        (neighborhoodRegionMargin_positive a ha))))
  exact SeriesLimitLaws.shrinks_scale _ he _ hC

/-- One center-dependent rate bounds every actual value remainder in the neighborhood. -/
theorem upperWeightFourLatticeSum_local_close_prefix (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (sub (upperWeightFourLatticeSum z hz) (upperWeightFourPrefix z hz n))
      (localWeightFourTailRate a ha n) := by
  obtain ⟨S,hregion,hheight⟩ := upperCommonRegion a ha z hs
  exact upperWeightFourLatticeSum_region_close_prefix z hz _ _ _ S
    (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
    (neighborhoodRegionMargin_positive a ha) hregion hheight n

def localWeightSixTailRate (a : Scalar) (ha : InUpperHalfPlane a.val) (n : Nat) : Rat :=
  regionalWeightSixTailConstant (neighborhoodRegionWidth a ha) (neighborhoodRegionWidth a ha)
    (neighborhoodRegionMargin a ha)*reciprocalSquare (n+1)

theorem localWeightSixTailRate_shrinks (a : Scalar) (ha : InUpperHalfPlane a.val) :
    ShrinksToZero (localWeightSixTailRate a ha) := by
  have he : ShrinksToZero (fun n => reciprocalSquare (n+1)) := by
    apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    change reciprocalSquare (n+1)≤1/((n+1:Nat):Rat)
    exact reciprocalSquare_le_reciprocal (n+1) (by omega)
  have hC : 0≤regionalWeightSixTailConstant (neighborhoodRegionWidth a ha)
      (neighborhoodRegionWidth a ha) (neighborhoodRegionMargin a ha) := by
    unfold regionalWeightSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg (Rat.mul_nonneg (by decide)
      (latticeRegionReciprocalConstant_nonnegative _ _ _
        (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
        (neighborhoodRegionMargin_positive a ha))))
  exact SeriesLimitLaws.shrinks_scale _ he _ hC

/-- One center-dependent rate bounds every actual value remainder in the neighborhood. -/
theorem upperWeightSixLatticeSum_local_close_prefix (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (sub (upperWeightSixLatticeSum z hz) (upperWeightSixPrefix z hz n))
      (localWeightSixTailRate a ha n) := by
  obtain ⟨S,hregion,hheight⟩ := upperCommonRegion a ha z hs
  exact upperWeightSixLatticeSum_region_close_prefix z hz _ _ _ S
    (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
    (neighborhoodRegionMargin_positive a ha) hregion hheight n

end ComputableAnalysis.ModularForms
