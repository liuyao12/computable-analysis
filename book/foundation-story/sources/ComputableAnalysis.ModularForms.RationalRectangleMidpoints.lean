import ComputableAnalysis.ModularForms.PairedRiccatiDerivativeNeighborhoodCover
import ComputableAnalysis.ModularForms.DyadicSampleAverage

/-! Literal rational rectangle centers, half-side vectors, and edge samples. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def rectangleCenter (J : QInterval × QInterval) : QComplex :=
  ⟨J.1.midpoint,J.2.midpoint⟩
def rectangleHalfX (J : QInterval × QInterval) : QComplex := ⟨J.1.width/2,0⟩
def rectangleHalfY (J : QInterval × QInterval) : QComplex := ⟨0,J.2.width/2⟩
def rectangleRight (J : QInterval × QInterval) : QComplex := ⟨J.1.hi,J.2.midpoint⟩
def rectangleLeft (J : QInterval × QInterval) : QComplex := ⟨J.1.lo,J.2.midpoint⟩
def rectangleTop (J : QInterval × QInterval) : QComplex := ⟨J.1.midpoint,J.2.hi⟩
def rectangleBottom (J : QInterval × QInterval) : QComplex := ⟨J.1.midpoint,J.2.lo⟩
def rationalRectangleScalar (q : QComplex) : Scalar := ⟨ofQComplex q,ofQComplex_valid _⟩

theorem rectangleMidpoints_mem (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    rationalRectangleContains J (rectangleCenter J) ∧
    rationalRectangleContains J (rectangleRight J) ∧
    rationalRectangleContains J (rectangleLeft J) ∧
    rationalRectangleContains J (rectangleTop J) ∧
    rationalRectangleContains J (rectangleBottom J) := by
  have hx := midpoint_mem J.1 hX
  have hy := midpoint_mem J.2 hY
  unfold rationalRectangleContains rectangleCenter rectangleRight rectangleLeft rectangleTop rectangleBottom
  exact ⟨⟨hx.1,hx.2,hy.1,hy.2⟩,
    ⟨hX,Rat.le_refl,hy.1,hy.2⟩,⟨Rat.le_refl,hX,hy.1,hy.2⟩,
    ⟨hx.1,hx.2,hY,Rat.le_refl⟩,⟨hx.1,hx.2,Rat.le_refl,hY⟩⟩

theorem rectangleMidpoints_coordinates (J : QInterval × QInterval) :
    QComplex.add (rectangleCenter J) (rectangleHalfX J)=rectangleRight J ∧
    QComplex.add (rectangleCenter J) (QComplex.neg (rectangleHalfX J))=rectangleLeft J ∧
    QComplex.add (rectangleCenter J) (rectangleHalfY J)=rectangleTop J ∧
    QComplex.add (rectangleCenter J) (QComplex.neg (rectangleHalfY J))=rectangleBottom J := by
  simp only [rectangleCenter,rectangleHalfX,rectangleHalfY,rectangleRight,rectangleLeft,
    rectangleTop,rectangleBottom,QComplex.add,QComplex.neg,QComplex.mk.injEq,QInterval.midpoint,QInterval.width]
  grind only

theorem rationalRectangleScalar_translate (c w : QComplex) :
    (Centered.translate (rationalRectangleScalar c) (rationalRectangleScalar w)).val.Equiv
      (ofQComplex (QComplex.add c w)) := by
  have he : (Centered.translate (rationalRectangleScalar c) (rationalRectangleScalar w)).val=
      ofQComplex (QComplex.add c w) := rfl
  rw [he]
  exact equiv_refl _ (ofQComplex_valid _)

theorem rationalRectangleScalar_neg (w : QComplex) :
    (scalarNeg (rationalRectangleScalar w)).val.Equiv (ofQComplex (QComplex.neg w)) := by
  have he : (scalarNeg (rationalRectangleScalar w)).val=ofQComplex (QComplex.neg w) := rfl
  rw [he]
  exact equiv_refl _ (ofQComplex_valid _)

theorem rectangleHalfVectors_small (J : QInterval × QInterval) (H : QPos)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*H.val) (hy : J.2.width≤2*H.val) :
    Small (rationalRectangleScalar (rectangleHalfX J)).val H.val ∧
    Small (rationalRectangleScalar (rectangleHalfY J)).val H.val := by
  have hx0 : 0≤J.1.width := by unfold QInterval.width; grind only
  have hy0 : 0≤J.2.width := by unfold QInterval.width; grind only
  constructor
  · refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · change -H.val≤J.1.width/2; have hp := H.property; grind only
    · change J.1.width/2≤H.val; grind only
    · change -H.val≤0; have hp := H.property; grind only
    · change (0:Rat)≤H.val; exact Rat.le_of_lt H.property
  · refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · change -H.val≤0; have hp := H.property; grind only
    · change (0:Rat)≤H.val; exact Rat.le_of_lt H.property
    · change -H.val≤J.2.width/2; have hp := H.property; grind only
    · change J.2.width/2≤H.val; grind only

theorem rectangleMidpoints_translations (J : QInterval × QInterval) :
    Centered.translate (rationalRectangleScalar (rectangleCenter J))
      (rationalRectangleScalar (rectangleHalfX J))=rationalRectangleScalar (rectangleRight J) ∧
    Centered.translate (rationalRectangleScalar (rectangleCenter J))
      (scalarNeg (rationalRectangleScalar (rectangleHalfX J)))=rationalRectangleScalar (rectangleLeft J) ∧
    Centered.translate (rationalRectangleScalar (rectangleCenter J))
      (rationalRectangleScalar (rectangleHalfY J))=rationalRectangleScalar (rectangleTop J) ∧
    Centered.translate (rationalRectangleScalar (rectangleCenter J))
      (scalarNeg (rationalRectangleScalar (rectangleHalfY J)))=rationalRectangleScalar (rectangleBottom J) := by
  have h := rectangleMidpoints_coordinates J
  constructor
  · apply Subtype.ext
    change ofQComplex (QComplex.add (rectangleCenter J) (rectangleHalfX J))=ofQComplex (rectangleRight J)
    rw [h.1]
  constructor
  · apply Subtype.ext
    change ofQComplex (QComplex.add (rectangleCenter J) (QComplex.neg (rectangleHalfX J)))=ofQComplex (rectangleLeft J)
    rw [h.2.1]
  constructor
  · apply Subtype.ext
    change ofQComplex (QComplex.add (rectangleCenter J) (rectangleHalfY J))=ofQComplex (rectangleTop J)
    rw [h.2.2.1]
  · apply Subtype.ext
    change ofQComplex (QComplex.add (rectangleCenter J) (QComplex.neg (rectangleHalfY J)))=ofQComplex (rectangleBottom J)
    rw [h.2.2.2]

end ComputableAnalysis.ModularForms
