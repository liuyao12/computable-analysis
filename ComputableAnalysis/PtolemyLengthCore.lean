import ComputableAnalysis.RationalCircle
import ComputableAnalysis.Algebraic

/-!
# Lightweight certified chord lengths

This module contains only the rational squared-distance and square-root
interface needed by finite chord certificates.  It deliberately does not
import the large π proof scoreboard.
-/

namespace ComputableAnalysis

namespace PtolemyLengthCore

open RationalCircle
open RationalCircle.Stage

def pointSegmentNormSq (p q : PiCirclePoint) : Rat :=
  let dx := q.x - p.x
  let dy := q.y - p.y
  dx * dx + dy * dy

theorem pointSegmentNormSq_eq_rationalCircleSegmentNormSq
    (p q : PiCirclePoint) :
    pointSegmentNormSq p q = RationalCircle.Stage.segmentNormSq p q := by
  rfl

theorem pointSegmentNormSq_nonneg (p q : PiCirclePoint) :
    0 <= pointSegmentNormSq p q := by
  unfold pointSegmentNormSq
  have hx := RationalCircle.Stage.ratSquare_nonneg (q.x - p.x)
  have hy := RationalCircle.Stage.ratSquare_nonneg (q.y - p.y)
  grind

theorem pointSegmentNormSq_sqrtDomain (p q : PiCirclePoint) :
    sqrtDomain (pointSegmentNormSq p q) := by
  change ¬pointSegmentNormSq p q < 0
  have h := pointSegmentNormSq_nonneg p q
  grind

def pointSegmentLengthRaw (p q : PiCirclePoint) : RealRaw :=
  sqrtRaw (pointSegmentNormSq p q) (pointSegmentNormSq_sqrtDomain p q)

theorem pointSegmentLengthRaw_spec (p q : PiCirclePoint) :
    SqrtRawSpec (pointSegmentNormSq p q)
      (pointSegmentNormSq_sqrtDomain p q) := by
  exact sqrtRaw_spec _ _

theorem pointSegmentLengthRaw_equiv_of_square
    (p q : PiCirclePoint) (r : Rat)
    (hsquare : sq r = pointSegmentNormSq p q) :
    (pointSegmentLengthRaw p q).Equiv (RealRaw.ofRat (qabs r)) := by
  let hq : sqrtDomain (pointSegmentNormSq p q) :=
    pointSegmentNormSq_sqrtDomain p q
  have hspec : SqrtRawSpec (pointSegmentNormSq p q) hq :=
    pointSegmentLengthRaw_spec p q
  have hreal := sqrt_rational_of_square
    (pointSegmentNormSq p q) r hq hspec hsquare
  simpa [pointSegmentLengthRaw, sqrtReal, Real.ofRat, Real.ofRaw,
    Real.Equiv] using hreal

end PtolemyLengthCore

end ComputableAnalysis
