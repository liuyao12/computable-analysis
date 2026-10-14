import ComputableAnalysis.RiemannHilbert.RepresentedAffineSegments
import ComputableAnalysis.RiemannHilbert.UnitIntervalApproximation
import ComputableAnalysis.ModularForms.BoundedAngleInput

/-! Every represented segment between bounded real angles has a bounded
angle name, with agreement rather than an assumed interval containment. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 2000000

theorem representedAffine_box_sample_mem (p q : Scalar) (t : UnitInterval.Point) (n : Nat) :
    let r := UnitInterval.clamp (((t.value.compute n).lo+(t.value.compute n).hi)/2)
    let x := QComplex.add (p.val.compute n).lo
      (QComplex.mul (QComplex.sub (q.val.compute n).lo (p.val.compute n).lo) (QComplex.ofRat r))
    ((RepresentedAffineSegment.point p q t).val.compute n).lo≤x ∧
      x≤((RepresentedAffineSegment.point p q t).val.compute n).hi := by
  let r := UnitInterval.clamp (((t.value.compute n).lo+(t.value.compute n).hi)/2)
  have hp := ComplexRaw.valid_ordered p.property n
  have hq := ComplexRaw.valid_ordered q.property n
  have hpord := hp
  simp only [QBox.Ordered,QComplex.le_def] at hp hq
  have ht := UnitInterval.clamped_midpoint_mem t n
  have hs : ((UnitInterval.scalar t).val.compute n).lo≤QComplex.ofRat r ∧
      QComplex.ofRat r≤((UnitInterval.scalar t).val.compute n).hi :=
    ⟨⟨ht.1,Rat.le_refl⟩,⟨ht.2,Rat.le_refl⟩⟩
  have hdiff : ((Centered.offset p q).val.compute n).lo≤
      QComplex.sub (q.val.compute n).lo (p.val.compute n).lo ∧
      QComplex.sub (q.val.compute n).lo (p.val.compute n).lo≤((Centered.offset p q).val.compute n).hi := by
    constructor <;> simp only [Centered.offset,sub,neg,add,QBox.add,QBox.neg,QComplex.add,QComplex.sub,QComplex.neg,QComplex.le_def]
      <;> grind only
  have hm := QBox.mul_contains hdiff.1 hdiff.2 hs.1 hs.2
  have ha := QBox.add_contains (QComplex.le_refl (p.val.compute n).lo) hpord hm.1 hm.2
  exact ha


namespace BoundedAngle

def scalar (A : BoundedAngle) : Scalar := ⟨ofRealRaw A.raw,ofRealRaw_valid _ A.valid⟩
def segmentReal (A B : BoundedAngle) (t : UnitInterval.Point) : RealRaw :=
  (RepresentedAffineSegment.point A.scalar B.scalar t).val.realPart

theorem segmentReal_valid (A B : BoundedAngle) (t : UnitInterval.Point) :
    (segmentReal A B t).Valid := realPart_valid (RepresentedAffineSegment.point A.scalar B.scalar t).property

theorem segmentReal_guard_overlap (A B : BoundedAngle) (t : UnitInterval.Point) (n : Nat) :
    ((segmentReal A B t).compute n).Overlaps (⟨1,2⟩ : QInterval) := by
  have hs := representedAffine_box_sample_mem A.scalar B.scalar t n
  let r := UnitInterval.clamp (((t.value.compute n).lo+(t.value.compute n).hi)/2)
  have hr := UnitInterval.clamp_bounds (((t.value.compute n).lo+(t.value.compute n).hi)/2)
  change 0≤r ∧ r≤1 at hr
  have ha := A.bounds n
  have hb := B.bounds n
  have ho := RealRaw.interval_order_of_valid B.raw B.valid n
  have hoa := RealRaw.interval_order_of_valid A.raw A.valid n
  have h1 : 0≤1-r := by dsimp [r]; grind only
  have hl := Rat.mul_le_mul_of_nonneg_left ha.1 h1
  have hl' := Rat.mul_le_mul_of_nonneg_left hb.1 hr.1
  have hu := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hoa ha.2) h1
  have hu' := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans ho hb.2) hr.1
  have hlo := hs.1.1
  have hhi := hs.2.1
  simp only [scalar,ofRealRaw,QComplex.add,QComplex.mul,QComplex.sub,QComplex.neg,QComplex.ofRat,
    Rat.mul_zero,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero] at hlo hhi
  change ((segmentReal A B t).compute n).lo ≤
    (A.raw.compute n).lo+((B.raw.compute n).lo+ -(A.raw.compute n).lo)*r at hlo
  change (A.raw.compute n).lo+((B.raw.compute n).lo+ -(A.raw.compute n).lo)*r≤
    ((segmentReal A B t).compute n).hi at hhi
  change ((segmentReal A B t).compute n).lo≤2 ∧ 1≤((segmentReal A B t).compute n).hi
  generalize (A.raw.compute n).lo=a at hl hu hlo hhi
  generalize (B.raw.compute n).lo=b at hl' hu' hlo hhi
  constructor <;> grind only

def segmentReboxed (A B : BoundedAngle) (t : UnitInterval.Point) : RealRaw where
  compute := fun n => QInterval.intersection ((segmentReal A B t).compute n) (⟨1,2⟩ : QInterval)

theorem segmentReboxed_ordered (A B : BoundedAngle) (t : UnitInterval.Point) (n : Nat) :
    ((segmentReboxed A B t).compute n).lo≤((segmentReboxed A B t).compute n).hi := by
  have hw := (segmentReal_valid A B t).1 n
  have ho : ((segmentReal A B t).compute n).lo≤((segmentReal A B t).compute n).hi := by
    change 0≤((segmentReal A B t).compute n).hi-((segmentReal A B t).compute n).lo at hw
    grind only
  exact QInterval.intersection_ordered_of_overlaps ho (by decide +kernel)
    (segmentReal_guard_overlap A B t n)

theorem segmentReboxed_valid (A B : BoundedAngle) (t : UnitInterval.Point) : (segmentReboxed A B t).Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    have h := segmentReboxed_ordered A B t n
    change 0≤((segmentReboxed A B t).compute n).hi-((segmentReboxed A B t).compute n).lo
    grind only
  · intro n m hnm
    have h := (segmentReal_valid A B t).2.1 n m hnm
    have ho := segmentReboxed_ordered A B t m
    change max ((segmentReal A B t).compute n).lo 1≤max ((segmentReal A B t).compute m).lo 1 ∧
      max ((segmentReal A B t).compute m).lo 1≤min ((segmentReal A B t).compute m).hi 2 ∧
      min ((segmentReal A B t).compute m).hi 2≤min ((segmentReal A B t).compute n).hi 2
    constructor
    · grind
    · exact ⟨ho,by grind⟩
  · intro eps
    obtain ⟨N,hN⟩ := (segmentReal_valid A B t).2.2 eps
    refine ⟨N,?_⟩
    intro n hn
    have h := hN n hn
    have hc := QInterval.intersection_contained_left ((segmentReal A B t).compute n) (⟨1,2⟩ : QInterval)
    change ((segmentReboxed A B t).compute n).hi-((segmentReboxed A B t).compute n).lo≤eps.val
    change ((segmentReal A B t).compute n).hi-((segmentReal A B t).compute n).lo≤eps.val at h
    change ((segmentReal A B t).compute n).lo≤((segmentReboxed A B t).compute n).lo ∧
      ((segmentReboxed A B t).compute n).hi≤((segmentReal A B t).compute n).hi at hc
    grind only

theorem segmentReboxed_equiv (A B : BoundedAngle) (t : UnitInterval.Point) : (segmentReboxed A B t).Equiv (segmentReal A B t) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have h := segmentReboxed_ordered A B t n
  have hc := QInterval.intersection_contained_left ((segmentReal A B t).compute n) (⟨1,2⟩ : QInterval)
  exact ⟨Rat.le_trans h hc.2,Rat.le_trans hc.1 h⟩



def segment (A B : BoundedAngle) (t : UnitInterval.Point) : BoundedAngle where
  raw := segmentReboxed A B t
  valid := segmentReboxed_valid A B t
  bounds n := by
    have h := QInterval.intersection_contained_right ((segmentReal A B t).compute n) (⟨1,2⟩ : QInterval)
    exact h

theorem segment_rotation_derivative_negative (A B : BoundedAngle) (t : UnitInterval.Point) :
    (angleRotationMap_holomorphic.derivative (segment A B t).scalar
      ⟨trivial,trivial⟩).val.realPart.Neg := rotation_derivative_negative (segment A B t)

end BoundedAngle
end ComputableAnalysis.ModularForms
