import ComputableAnalysis.ModularForms.PunctureSafeRectangles
import ComputableAnalysis.RiemannHilbert.RepresentedAffineSegments

/-! All represented parameters between rational rectangle endpoints stay
inside the rectangle, including parameters with wide initial boxes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def rationalAffinePoint (p q : QComplex) (r : Rat) : QComplex :=
  QComplex.add p (QComplex.mul (QComplex.sub q p) (QComplex.ofRat r))

theorem rationalAffinePoint_rectangle_mem (J : QInterval × QInterval) (p q : QComplex)
    (hp : rationalRectangleContains J p) (hq : rationalRectangleContains J q)
    (r : Rat) (hr0 : 0≤r) (hr1 : r≤1) : rationalRectangleContains J (rationalAffinePoint p q r) := by
  have h1 : 0≤1-r := by grind only
  have px0 := Rat.mul_le_mul_of_nonneg_left hp.1 h1
  have qx0 := Rat.mul_le_mul_of_nonneg_left hq.1 hr0
  have px1 := Rat.mul_le_mul_of_nonneg_left hp.2.1 h1
  have qx1 := Rat.mul_le_mul_of_nonneg_left hq.2.1 hr0
  have py0 := Rat.mul_le_mul_of_nonneg_left hp.2.2.1 h1
  have qy0 := Rat.mul_le_mul_of_nonneg_left hq.2.2.1 hr0
  have py1 := Rat.mul_le_mul_of_nonneg_left hp.2.2.2 h1
  have qy1 := Rat.mul_le_mul_of_nonneg_left hq.2.2.2 hr0
  simp only [rationalRectangleContains,rationalAffinePoint,QComplex.add,QComplex.mul,QComplex.sub,QComplex.neg,QComplex.ofRat]
  grind only

theorem representedAffine_rational_rectangle_mem (J : QInterval × QInterval) (p q : QComplex)
    (hp : rationalRectangleContains J p) (hq : rationalRectangleContains J q) (t : UnitInterval.Point) :
    representedRectangleContains J
      (RepresentedAffineSegment.point (rationalRectangleScalar p) (rationalRectangleScalar q) t) := by
  let z := RepresentedAffineSegment.point (rationalRectangleScalar p) (rationalRectangleScalar q) t
  have enclosed (n : Nat) : ∃ w : QComplex, rationalRectangleContains J w ∧
      (z.val.compute n).lo≤w ∧ w≤(z.val.compute n).hi := by
    let r := UnitInterval.clamp (((t.value.compute n).lo+(t.value.compute n).hi)/2)
    have hr := UnitInterval.clamp_bounds (((t.value.compute n).lo+(t.value.compute n).hi)/2)
    have ht := UnitInterval.clamped_midpoint_mem t n
    have htl : (t.value.compute n).lo≤r := ht.1
    have htu : r≤(t.value.compute n).hi := ht.2
    have hscalar : ((UnitInterval.scalar t).val.compute n).lo≤QComplex.ofRat r ∧
        QComplex.ofRat r≤((UnitInterval.scalar t).val.compute n).hi :=
      ⟨⟨htl,Rat.le_refl⟩,⟨htu,Rat.le_refl⟩⟩
    have hm := QBox.mul_contains (A := QBox.point (QComplex.sub q p))
      (QComplex.le_refl _) (QComplex.le_refl _) hscalar.1 hscalar.2
    have ha := QBox.add_contains (A := QBox.point p)
      (QComplex.le_refl _) (QComplex.le_refl _) hm.1 hm.2
    refine ⟨rationalAffinePoint p q r,rationalAffinePoint_rectangle_mem J p q hp hq r hr.1 hr.2, ?_⟩
    exact ha
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · obtain ⟨w,hw,hbox⟩ := enclosed m
    exact Rat.le_trans hw.1 hbox.2.1
  · obtain ⟨w,hw,hbox⟩ := enclosed n
    exact Rat.le_trans hbox.1.1 hw.2.1
  · obtain ⟨w,hw,hbox⟩ := enclosed m
    exact Rat.le_trans hw.2.2.1 hbox.2.2
  · obtain ⟨w,hw,hbox⟩ := enclosed n
    exact Rat.le_trans hbox.1.2 hw.2.2.2

theorem punctureSafeAffineSegment_kernel_domain (a : Scalar) (J : QInterval × QInterval)
    (R : QPos) (hs : rectangleSeparated J R) (p q : QComplex)
    (hp : rationalRectangleContains J p) (hq : rationalRectangleContains J q) (t : UnitInterval.Point) :
    (pairedRiccatiCauchyIntegrandMap a).domain
      (RepresentedAffineSegment.point (rationalRectangleScalar p) (rationalRectangleScalar q) t) :=
  punctureSafeRectangle_kernel_domain a J R hs _
    (representedAffine_rational_rectangle_mem J p q hp hq t)

end ComputableAnalysis.ModularForms
