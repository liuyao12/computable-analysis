import ComputableAnalysis.FinitePtolemyLength

/-!
# A second finite Ptolemy certificate

This is an independent rational-circle parameter quadruple.  The six chord
squares are rational squares, and the corresponding rational lengths satisfy
Ptolemy's identity by exact arithmetic.
-/

namespace ComputableAnalysis

namespace FinitePtolemySecondExample

open RationalCircle
open RationalCircle.Stage
open FinitePtolemyLength
open PtolemyLengthCore

def secondPtolemyPointA : PiCirclePoint := RationalCircle.Stage.point 0
def secondPtolemyPointB : PiCirclePoint := RationalCircle.Stage.point (5 / 12)
def secondPtolemyPointC : PiCirclePoint := RationalCircle.Stage.point (3 / 4)
def secondPtolemyPointD : PiCirclePoint := RationalCircle.Stage.point (4 / 3)

theorem secondPtolemy_square_coordinates :
    segmentNormSq secondPtolemyPointA secondPtolemyPointB = 100 / 169 /\
      segmentNormSq secondPtolemyPointB secondPtolemyPointC = 1024 / 4225 /\
      segmentNormSq secondPtolemyPointC secondPtolemyPointD = 196 / 625 /\
      segmentNormSq secondPtolemyPointD secondPtolemyPointA = 64 / 25 /\
      segmentNormSq secondPtolemyPointA secondPtolemyPointC = 36 / 25 /\
      segmentNormSq secondPtolemyPointB secondPtolemyPointD = 4356 / 4225 := by
  dsimp [secondPtolemyPointA, secondPtolemyPointB,
    secondPtolemyPointC, secondPtolemyPointD]
  repeat' first | constructor
  all_goals
    rw [RationalCircle.Stage.point_segmentNormSq_formula]
    native_decide

theorem secondPtolemy_rational_length_identity :
    (10 / 13 : Rat) * (14 / 25) +
        (32 / 65) * (8 / 5) =
      (6 / 5) * (66 / 65) := by
  native_decide

theorem secondPtolemy_length_certificate :
    (pointSegmentLengthRaw secondPtolemyPointA secondPtolemyPointB).Equiv
        (RealRaw.ofRat (10 / 13)) ∧
      (pointSegmentLengthRaw secondPtolemyPointB secondPtolemyPointC).Equiv
        (RealRaw.ofRat (32 / 65)) ∧
      (pointSegmentLengthRaw secondPtolemyPointC secondPtolemyPointD).Equiv
        (RealRaw.ofRat (14 / 25)) ∧
      (pointSegmentLengthRaw secondPtolemyPointD secondPtolemyPointA).Equiv
        (RealRaw.ofRat (8 / 5)) ∧
      (pointSegmentLengthRaw secondPtolemyPointA secondPtolemyPointC).Equiv
        (RealRaw.ofRat (6 / 5)) ∧
      (pointSegmentLengthRaw secondPtolemyPointB secondPtolemyPointD).Equiv
        (RealRaw.ofRat (66 / 65)) ∧
      (10 / 13 : Rat) * (14 / 25) +
          (32 / 65) * (8 / 5) =
        (6 / 5) * (66 / 65) := by
  have hsquares := secondPtolemy_square_coordinates
  have hab : sq (10 / 13 : Rat) =
      pointSegmentNormSq secondPtolemyPointA secondPtolemyPointB := by
    rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq, hsquares.1]
    native_decide
  have hbc : sq (32 / 65 : Rat) =
      pointSegmentNormSq secondPtolemyPointB secondPtolemyPointC := by
    rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq, hsquares.2.1]
    native_decide
  have hcd : sq (14 / 25 : Rat) =
      pointSegmentNormSq secondPtolemyPointC secondPtolemyPointD := by
    rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq, hsquares.2.2.1]
    native_decide
  have hda : sq (8 / 5 : Rat) =
      pointSegmentNormSq secondPtolemyPointD secondPtolemyPointA := by
    rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq, hsquares.2.2.2.1]
    native_decide
  have hac : sq (6 / 5 : Rat) =
      pointSegmentNormSq secondPtolemyPointA secondPtolemyPointC := by
    rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq, hsquares.2.2.2.2.1]
    native_decide
  have hbd : sq (66 / 65 : Rat) =
      pointSegmentNormSq secondPtolemyPointB secondPtolemyPointD := by
    rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq, hsquares.2.2.2.2.2]
    native_decide
  have hab' := pointSegmentLengthRaw_equiv_of_square
    secondPtolemyPointA secondPtolemyPointB (10 / 13) hab
  have hbc' := pointSegmentLengthRaw_equiv_of_square
    secondPtolemyPointB secondPtolemyPointC (32 / 65) hbc
  have hcd' := pointSegmentLengthRaw_equiv_of_square
    secondPtolemyPointC secondPtolemyPointD (14 / 25) hcd
  have hda' := pointSegmentLengthRaw_equiv_of_square
    secondPtolemyPointD secondPtolemyPointA (8 / 5) hda
  have hac' := pointSegmentLengthRaw_equiv_of_square
    secondPtolemyPointA secondPtolemyPointC (6 / 5) hac
  have hbd' := pointSegmentLengthRaw_equiv_of_square
    secondPtolemyPointB secondPtolemyPointD (66 / 65) hbd
  have hpos₁ : 0 <= (10 / 13 : Rat) := by native_decide
  have hpos₂ : 0 <= (32 / 65 : Rat) := by native_decide
  have hpos₃ : 0 <= (14 / 25 : Rat) := by native_decide
  have hpos₄ : 0 <= (8 / 5 : Rat) := by native_decide
  have hpos₅ : 0 <= (6 / 5 : Rat) := by native_decide
  have hpos₆ : 0 <= (66 / 65 : Rat) := by native_decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [qabs_eq_self_of_nonneg hpos₁] using hab'
  · simpa [qabs_eq_self_of_nonneg hpos₂] using hbc'
  · simpa [qabs_eq_self_of_nonneg hpos₃] using hcd'
  · simpa [qabs_eq_self_of_nonneg hpos₄] using hda'
  · simpa [qabs_eq_self_of_nonneg hpos₅] using hac'
  · simpa [qabs_eq_self_of_nonneg hpos₆] using hbd'
  · native_decide

end FinitePtolemySecondExample

end ComputableAnalysis
