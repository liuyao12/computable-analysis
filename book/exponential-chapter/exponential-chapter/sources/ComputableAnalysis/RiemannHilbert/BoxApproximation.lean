import ComputableAnalysis.RiemannHilbert.EffectiveNeighborhood

/-! Rational centers approximate arbitrary valid represented complex values.
The bounds are exact bounds on values, even when early boxes are wide. -/
namespace ComputableAnalysis.RiemannHilbert.BoxApproximation
open ComplexRaw FunctionTheory LocalODE

def coordinateBound (q : QComplex) : Rat := max (qabs q.re) (qabs q.im)

theorem coordinateBound_nonneg (q : QComplex) : 0 ≤ coordinateBound q := by
  have := qabs_nonneg q.re
  unfold coordinateBound
  grind

theorem coordinateBound_bounds (q : QComplex) :
    -coordinateBound q ≤ q.re ∧ q.re ≤ coordinateBound q ∧
    -coordinateBound q ≤ q.im ∧ q.im ≤ coordinateBound q := by
  unfold coordinateBound qabs
  split <;> split <;> grind

theorem rational_small (q : QComplex) : Small (ofQComplex q) (coordinateBound q) := by
  have hb := coordinateBound_bounds q
  exact ⟨fun _ _ => hb.1, fun _ _ => hb.2.1, fun _ _ => hb.2.2.1, fun _ _ => hb.2.2.2⟩

theorem point_error (z : Scalar) (k : Nat) (q : QComplex) (R : Rat) (hR : 0 ≤ R)
    (hq : (z.val.compute k).lo ≤ q ∧ q ≤ (z.val.compute k).hi)
    (hw : (z.val.compute k).width ≤ R) (hh : (z.val.compute k).height ≤ R) :
    Small (sub z.val (ofQComplex q)) R := by
  let B := z.val.compute k
  have hs := small_from_box (sub z.val (ofQComplex q))
    (sub_valid z.property (ofQComplex_valid _)) k
  apply hs.mono
  change max 0 (max (-(B.lo.re + -q.re))
    (max (B.hi.re + -q.re) (max (-(B.lo.im + -q.im)) (B.hi.im + -q.im)))) ≤ R
  change (B.lo.re ≤ q.re ∧ B.lo.im ≤ q.im) ∧ (q.re ≤ B.hi.re ∧ q.im ≤ B.hi.im) at hq
  change B.hi.re-B.lo.re ≤ R at hw
  change B.hi.im-B.lo.im ≤ R at hh
  grind

theorem center_error (z : Scalar) (k : Nat) (R : Rat) (hR : 0 ≤ R)
    (hw : (z.val.compute k).width ≤ R) (hh : (z.val.compute k).height ≤ R) :
    Small (sub z.val (ofQComplex (z.val.compute k).center)) R := by
  let B := z.val.compute k
  rcases QBox.center_mem (valid_ordered z.property k) with ⟨hcl,hch⟩
  have hs := small_from_box (sub z.val (ofQComplex B.center))
    (sub_valid z.property (ofQComplex_valid _)) k
  apply hs.mono
  change max 0 (max (-(B.lo.re + -B.center.re))
    (max (B.hi.re + -B.center.re) (max (-(B.lo.im + -B.center.im)) (B.hi.im + -B.center.im)))) ≤ R
  change B.lo.re ≤ B.center.re ∧ B.lo.im ≤ B.center.im at hcl
  change B.center.re ≤ B.hi.re ∧ B.center.im ≤ B.hi.im at hch
  change B.hi.re-B.lo.re ≤ R at hw
  change B.hi.im-B.lo.im ≤ R at hh
  grind

theorem center_bound (z : Scalar) (k : Nat) :
    coordinateBound (z.val.compute k).center ≤ boxCoordinateBound (z.val.compute 0) := by
  rcases QBox.center_mem (valid_ordered z.property k) with ⟨hcl,hch⟩
  rcases valid_nestedIn z.property (Nat.zero_le k) with ⟨hnl,hnh⟩
  have hb := boxCoordinateBound_bounds (z.val.compute 0)
  change (z.val.compute k).lo.re ≤ (z.val.compute k).center.re ∧
    (z.val.compute k).lo.im ≤ (z.val.compute k).center.im at hcl
  change (z.val.compute k).center.re ≤ (z.val.compute k).hi.re ∧
    (z.val.compute k).center.im ≤ (z.val.compute k).hi.im at hch
  change (z.val.compute 0).lo.re ≤ (z.val.compute k).lo.re ∧
    (z.val.compute 0).lo.im ≤ (z.val.compute k).lo.im at hnl
  change (z.val.compute k).hi.re ≤ (z.val.compute 0).hi.re ∧
    (z.val.compute k).hi.im ≤ (z.val.compute 0).hi.im at hnh
  unfold coordinateBound qabs
  split <;> split <;> grind

end ComputableAnalysis.RiemannHilbert.BoxApproximation
