import ComputableAnalysis.ModularForms.UpperNeighborhood
import ComputableAnalysis.ModularForms.UpperLatticeRegionalBounds

/-! Common regional evidence throughout a represented upper-half-plane neighborhood. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalODE

def neighborhoodRegionWidth (a : Scalar) (ha : InUpperHalfPlane a.val) : Rat :=
  boxCoordinateBound (a.val.compute 0)+3*(upperRadius a ha).val/2

def neighborhoodRegionMargin (a : Scalar) (ha : InUpperHalfPlane a.val) : Rat :=
  (upperRadius a ha).val/2

theorem neighborhoodRegionWidth_nonnegative (a : Scalar) (ha : InUpperHalfPlane a.val) :
    0≤neighborhoodRegionWidth a ha := by
  have hB := boxCoordinateBound_nonneg (a.val.compute 0)
  have hr := (upperRadius a ha).property
  unfold neighborhoodRegionWidth
  grind only

theorem neighborhoodRegionMargin_positive (a : Scalar) (ha : InUpperHalfPlane a.val) :
    0<neighborhoodRegionMargin a ha := by
  have hr := (upperRadius a ha).property
  unfold neighborhoodRegionMargin
  grind only

/-- Nearby valid names have a common region; only their certification stage varies. -/
theorem upperCommonRegion (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) :
    ∃ M, LatticeRegionBox z (neighborhoodRegionWidth a ha)
      (neighborhoodRegionMargin a ha) M ∧
      (z.val.compute M).hi.im≤neighborhoodRegionWidth a ha := by
  let N := positiveImagIndex a ha
  let L := (a.val.compute N).lo.im
  have hL : 0<L := positiveImagIndex_spec a ha
  let eps : QPos := ⟨L/4,by grind only⟩
  obtain ⟨K,hK⟩ := z.property.2.2 eps
  let M := max N K
  have hw := hK M (Nat.le_max_right N K)
  have hn := valid_nestedIn a.property (Nat.le_max_left N K)
  have h0 := valid_nestedIn a.property (Nat.zero_le M)
  have hb := boxCoordinateBound_bounds (a.val.compute 0)
  have hrlo := hs.1 0 M
  have hrhi := hs.2.1 M 0
  have hilo := hs.2.2.1 0 M
  have hihi := hs.2.2.2 M 0
  change -(L/2)≤(z.val.compute M).hi.re + -(a.val.compute M).lo.re at hrlo
  change (z.val.compute M).lo.re + -(a.val.compute M).hi.re≤L/2 at hrhi
  change -(L/2)≤(z.val.compute M).hi.im + -(a.val.compute M).lo.im at hilo
  change (z.val.compute M).lo.im + -(a.val.compute M).hi.im≤L/2 at hihi
  change (z.val.compute M).hi.re-(z.val.compute M).lo.re≤L/4 ∧
    (z.val.compute M).hi.im-(z.val.compute M).lo.im≤L/4 at hw
  have hl : L≤(a.val.compute M).lo.im := hn.1.2
  have hrl : -boxCoordinateBound (a.val.compute 0)≤(a.val.compute M).lo.re :=
    Rat.le_trans hb.1 h0.1.1
  have hrh : (a.val.compute M).hi.re≤boxCoordinateBound (a.val.compute 0) :=
    Rat.le_trans h0.2.1 hb.2.1
  have hih : (a.val.compute M).hi.im≤boxCoordinateBound (a.val.compute 0) :=
    Rat.le_trans h0.2.2 hb.2.2.2
  refine ⟨M,⟨?_,?_,?_⟩,?_⟩
  all_goals simp only [neighborhoodRegionWidth,neighborhoodRegionMargin,upperRadius]
  all_goals grind only

end ComputableAnalysis.ModularForms
