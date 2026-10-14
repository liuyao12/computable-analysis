import ComputableAnalysis.RiemannHilbert.ContourGeometry

/-! Represented rectangle membership, including all represented segment parameters. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

def representedRectangleContains (J : QInterval × QInterval) (z : Scalar) : Prop :=
  RealRaw.Le (RealRaw.ofRat J.1.lo) z.val.realPart ∧
  RealRaw.Le z.val.realPart (RealRaw.ofRat J.1.hi) ∧
  RealRaw.Le (RealRaw.ofRat J.2.lo) z.val.imagPart ∧
  RealRaw.Le z.val.imagPart (RealRaw.ofRat J.2.hi)

def rectangleSeparated (J : QInterval × QInterval) (R : QPos) : Prop :=
  R.val≤J.1.lo ∨ J.1.hi≤ -R.val ∨ R.val≤J.2.lo ∨ J.2.hi≤ -R.val

theorem representedRectangle_nonzero (J : QInterval × QInterval) (R : QPos)
    (hs : rectangleSeparated J R) (z : Scalar) (hz : representedRectangleContains J z) :
    NonzeroBoxSearch.Nonzero z := by
  intro he
  have hr := ComplexRaw.realPart_equiv he
  have hi := ComplexRaw.imagPart_equiv he
  have hrv := realPart_valid z.property
  have hiv := imagPart_valid z.property
  have hzero : (RealRaw.ofRat 0).Valid := RealRaw.ofRat_valid 0
  have hr0 : RealRaw.Le z.val.realPart (RealRaw.ofRat 0) := RealRaw.le_of_equiv hrv hzero hr
  have h0r : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart :=
    RealRaw.le_of_equiv hzero hrv (RealRaw.equiv_symm hr)
  have hi0 : RealRaw.Le z.val.imagPart (RealRaw.ofRat 0) := RealRaw.le_of_equiv hiv hzero hi
  have h0i : RealRaw.Le (RealRaw.ofRat 0) z.val.imagPart :=
    RealRaw.le_of_equiv hzero hiv (RealRaw.equiv_symm hi)
  rcases hs with hs|hs|hs|hs
  · have hb := (RealRaw.le_trans hrv hz.1 hr0) 0 0
    change J.1.lo≤0 at hb
    have hp := R.property
    grind only
  · have hb := (RealRaw.le_trans hrv h0r hz.2.1) 0 0
    change (0:Rat)≤J.1.hi at hb
    have hp := R.property
    grind only
  · have hb := (RealRaw.le_trans hiv hz.2.2.1 hi0) 0 0
    change J.2.lo≤0 at hb
    have hp := R.property
    grind only
  · have hb := (RealRaw.le_trans hiv h0i hz.2.2.2) 0 0
    change (0:Rat)≤J.2.hi at hb
    have hp := R.property
    grind only

theorem rationalRectangle_represented_mem (J : QInterval × QInterval) (q : QComplex)
    (hq : rationalRectangleContains J q) : representedRectangleContains J (rationalRectangleScalar q) :=
  ⟨fun _ _ => hq.1,fun _ _ => hq.2.1,fun _ _ => hq.2.2.1,fun _ _ => hq.2.2.2⟩
def coordinateComplex (x y : RealRaw) : ComplexRaw where
  compute n := ⟨⟨(x.compute n).lo,(y.compute n).lo⟩,
    ⟨(x.compute n).hi,(y.compute n).hi⟩⟩

theorem coordinateComplex_valid (x y : RealRaw) (hx : x.Valid) (hy : y.Valid) :
    (coordinateComplex x y).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨hx.1 n,hy.1 n⟩
  · intro n m hnm
    have hxn := hx.2.1 n m hnm
    have hyn := hy.2.1 n m hnm
    exact ⟨hxn.1,hxn.2.2,hyn.1,hyn.2.2⟩
  · intro eps
    obtain ⟨X,hX⟩ := hx.2.2 eps
    obtain ⟨Y,hY⟩ := hy.2.2 eps
    refine ⟨max X Y, ?_⟩
    intro n hn
    exact ⟨hX n (by omega),hY n (by omega)⟩

theorem coordinateComplex_neighborhood (x y : RealRaw) (q : QComplex) (r : Rat)
    (hxl : RealRaw.Le (RealRaw.ofRat (q.re-r)) x)
    (hxu : RealRaw.Le x (RealRaw.ofRat (q.re+r)))
    (hyl : RealRaw.Le (RealRaw.ofRat (q.im-r)) y)
    (hyu : RealRaw.Le y (RealRaw.ofRat (q.im+r))) :
    Small (sub (ofQComplex q) (coordinateComplex x y)) r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m
    have hb := hxu m 0
    change (x.compute m).lo≤q.re+r at hb
    change -r≤q.re + -(x.compute m).lo
    grind only
  · intro n m
    have hb := hxl 0 n
    change q.re-r≤(x.compute n).hi at hb
    change q.re + -(x.compute n).hi≤r
    grind only
  · intro n m
    have hb := hyu m 0
    change (y.compute m).lo≤q.im+r at hb
    change -r≤q.im + -(y.compute m).lo
    grind only
  · intro n m
    have hb := hyl 0 n
    change q.im-r≤(y.compute n).hi at hb
    change q.im + -(y.compute n).hi≤r
    grind only

theorem rectangleNear_complex_displacement (J : QInterval × QInterval)
    (x y : RealRaw) (eps : QPos)
    (hx : intervalNear J.1 x eps) (hy : intervalNear J.2 y eps)
    (q : QComplex) (hq : J.1.lo≤q.re ∧ q.re≤J.1.hi ∧
      J.2.lo≤q.im ∧ q.im≤J.2.hi) :
    Small (sub (ofQComplex q) (coordinateComplex x y)) eps.val := by
  have hxr := hx q.re hq.1 hq.2.1
  have hyr := hy q.im hq.2.2.1 hq.2.2.2
  exact coordinateComplex_neighborhood x y q eps.val hxr.1 hxr.2 hyr.1 hyr.2
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

end ComputableAnalysis.RiemannHilbert.RectangularContour
