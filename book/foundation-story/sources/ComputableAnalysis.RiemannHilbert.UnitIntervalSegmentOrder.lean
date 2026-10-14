import ComputableAnalysis.RiemannHilbert.UnitIntervalSegmentAlgebra

/-! Order of represented affine subdivision points. Only value order is
required: early input boxes may extend outside the unit interval or overlap
in either direction. Finite corner bounds prove the exact order laws. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
open ComplexRaw FunctionTheory DomainFunctions

theorem segment_compute (a b t : Point) (n : Nat) :
    (segment a b t).value.compute n =
      { lo := (a.value.compute n).lo +
          (QBox.mulRealInterval ((b.value.compute n).lo-(a.value.compute n).hi)
            ((b.value.compute n).hi-(a.value.compute n).lo)
            (t.value.compute n).lo (t.value.compute n).hi).lo,
        hi := (a.value.compute n).hi +
          (QBox.mulRealInterval ((b.value.compute n).lo-(a.value.compute n).hi)
            ((b.value.compute n).hi-(a.value.compute n).lo)
            (t.value.compute n).lo (t.value.compute n).hi).hi } := by
  simp [segment,segmentRaw,ComplexRaw.realPart,RepresentedAffineSegment.point,
    RepresentedAffineSegment.function,DomainFunctions.affine,Centered.offset,
    scalar,scalarSum,scalarProduct,ComplexRaw.sub,ComplexRaw.add,ComplexRaw.neg,
    ComplexRaw.mul,ofRealRaw,QBox.add,QBox.neg,QBox.mul,QComplex.add,
    QBox.mulRealInterval,min4,max4,minRat,maxRat2,Rat.sub_eq_add_neg,Rat.add_zero]
  exact ⟨rfl,rfl⟩

private theorem corner_lower (a b c d : Rat) : min4 a b c d ≤ c := by
  unfold min4 minRat
  grind

private theorem corner_upper (a b c d : Rat) : d ≤ max4 a b c d := by
  unfold max4 maxRat2
  grind

theorem le_segment (a b t : Point) (hab : a.value.Le b.value) :
    a.value.Le (segment a b t).value := by
  apply RealRaw.le_of_sameStage a.valid (segment a b t).valid
  intro n
  rw [segment_compute]
  have ha := RealRaw.interval_order_of_valid a.value a.valid n
  have hd : 0 ≤ (b.value.compute n).hi-(a.value.compute n).lo := by
    have h := hab n n
    grind only
  have ht : 0 ≤ (t.value.compute n).hi := t.lower 0 n
  have hp := Rat.mul_nonneg hd ht
  have hm := corner_upper
    (((b.value.compute n).lo-(a.value.compute n).hi)*(t.value.compute n).lo)
    (((b.value.compute n).lo-(a.value.compute n).hi)*(t.value.compute n).hi)
    (((b.value.compute n).hi-(a.value.compute n).lo)*(t.value.compute n).lo)
    (((b.value.compute n).hi-(a.value.compute n).lo)*(t.value.compute n).hi)
  dsimp only [QBox.mulRealInterval]
  have h := Rat.le_trans hp hm
  grind only

theorem segment_le (a b t : Point) (hab : a.value.Le b.value) :
    (segment a b t).value.Le b.value := by
  apply RealRaw.le_of_sameStage (segment a b t).valid b.valid
  intro n
  rw [segment_compute]
  have hd : 0 ≤ (b.value.compute n).hi-(a.value.compute n).lo := by
    have h := hab n n
    grind only
  have ht : (t.value.compute n).lo ≤ 1 := t.upper n 0
  have hp := Rat.mul_le_mul_of_nonneg_left ht hd
  rw [Rat.mul_one] at hp
  have hm := corner_lower
    (((b.value.compute n).lo-(a.value.compute n).hi)*(t.value.compute n).lo)
    (((b.value.compute n).lo-(a.value.compute n).hi)*(t.value.compute n).hi)
    (((b.value.compute n).hi-(a.value.compute n).lo)*(t.value.compute n).lo)
    (((b.value.compute n).hi-(a.value.compute n).lo)*(t.value.compute n).hi)
  dsimp only [QBox.mulRealInterval]
  have h := Rat.le_trans hm hp
  grind only

theorem segment_between (a b t : Point) (hab : a.value.Le b.value) :
    a.value.Le (segment a b t).value ∧ (segment a b t).value.Le b.value :=
  ⟨le_segment a b t hab,segment_le a b t hab⟩

end ComputableAnalysis.RiemannHilbert.UnitInterval
