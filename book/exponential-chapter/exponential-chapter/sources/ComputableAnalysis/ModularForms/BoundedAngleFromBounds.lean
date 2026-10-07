import ComputableAnalysis.ModularForms.StrictOrderSandwich
import ComputableAnalysis.ModularForms.PositiveReciprocalAgreement

/-! An executable bounded angle name from semantic represented bounds.
The clipping algorithm and its agreement are internal to the constructor. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private def angleLowerName (x : RealRaw) := RealRaw.lowerClip x 1
private def angleBoundedName (x : RealRaw) :=
  RealRaw.neg (RealRaw.lowerClip (RealRaw.neg (angleLowerName x)) (-2))

private theorem angleLower_valid (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat 1).Le x) : (angleLowerName x).Valid :=
  RealRaw.lowerClip_valid x 1 hx (fun n => hl 0 n)

private theorem angleUpper_valid (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat 1).Le x) (hu : x.Le (RealRaw.ofRat 2)) :
    (RealRaw.lowerClip (RealRaw.neg (angleLowerName x)) (-2)).Valid := by
  apply RealRaw.lowerClip_valid _ (-2) (RealRaw.neg_valid (angleLower_valid x hx hl))
  intro n
  have h := hu n 0
  change (x.compute n).lo≤2 at h
  change -2≤ -(maxRat2 (x.compute n).lo 1)
  unfold maxRat2
  split <;> grind only

/-- A bounded angle constructed from its mathematical interval membership,
without imposing a restriction on the caller's individual boxes. -/
def boundedAngleFromBounds (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat 1).Le x) (hu : x.Le (RealRaw.ofRat 2)) : BoundedAngle where
  raw := angleBoundedName x
  valid := RealRaw.neg_valid (angleUpper_valid x hx hl hu)
  bounds n := by
    change 1≤ -(-maxRat2 (x.compute n).lo 1) ∧
      -(maxRat2 (-((x.compute n).hi)) (-2))≤2
    constructor <;> unfold maxRat2 <;> split <;> grind only

/-- The constructed bounded name represents precisely the supplied angle. -/
theorem boundedAngleFromBounds_agreement (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat 1).Le x) (hu : x.Le (RealRaw.ofRat 2)) :
    (boundedAngleFromBounds x hx hl hu).raw.Equiv x := by
  let y := angleLowerName x
  have hy := angleLower_valid x hx hl
  have he : y.Equiv x := lowerClip_equiv x hx 1 hl
  have hbound : (RealRaw.ofRat (-2)).Le (RealRaw.neg y) := by
    intro n m
    have h := hu m 0
    change (x.compute m).lo≤2 at h
    change -2≤ -(maxRat2 (x.compute m).lo 1)
    unfold maxRat2
    split <;> grind only
  have hc := RealRaw.neg_equiv (lowerClip_equiv (RealRaw.neg y) (RealRaw.neg_valid hy) (-2) hbound)
  have hd : (RealRaw.neg (RealRaw.neg y)).Equiv y := by
    intro n
    have ho := RealRaw.interval_order_of_valid y hy n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
    change -(-((y.compute n).lo))≤(y.compute n).hi ∧
      (y.compute n).lo≤ -(-((y.compute n).hi))
    grind only
  exact RealRaw.equiv_trans
    (boundedAngleFromBounds x hx hl hu).valid (RealRaw.neg_valid (RealRaw.neg_valid hy)) hx hc
    (RealRaw.equiv_trans (RealRaw.neg_valid (RealRaw.neg_valid hy)) hy hx hd he)

end ComputableAnalysis.ModularForms
