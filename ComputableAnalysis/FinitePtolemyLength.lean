import ComputableAnalysis.PiProofs

/-!
# A finite Ptolemy length certificate

This file lifts the coordinate-level Ptolemy shadow to certified lengths for
one concrete cyclic quadrilateral.  The four vertices are rational points in
the projective rational-circle chart.  The chosen parameters make all six
chord squares rational squares, so the existing square-root algorithm can be
identified with an explicit rational witness at every finite stage.

The proof is finite rational arithmetic throughout.  It does not invoke a
classical Euclidean length theorem, a completed real number, or a completeness
argument.
-/

namespace ComputableAnalysis

namespace FinitePtolemyLength

open RationalCircle
open RationalCircle.Stage
open PiProofs

def ptolemyPointA : PiCirclePoint := RationalCircle.Stage.point 0

def ptolemyPointB : PiCirclePoint := RationalCircle.Stage.point (8 / 15)

def ptolemyPointC : PiCirclePoint := RationalCircle.Stage.point (3 / 4)

def ptolemyPointD : PiCirclePoint := RationalCircle.Stage.point (4 / 3)

/-! A reusable bridge from a rational square certificate to the raw length
algorithm.  This is the concrete square-root witness used below. -/

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

theorem ptolemyPoint_square_coordinates :
    pointSegmentNormSq ptolemyPointA ptolemyPointB = 256 / 289 ∧
      pointSegmentNormSq ptolemyPointB ptolemyPointC = 676 / 7225 ∧
      pointSegmentNormSq ptolemyPointC ptolemyPointD = 196 / 625 ∧
      pointSegmentNormSq ptolemyPointD ptolemyPointA = 64 / 25 ∧
      pointSegmentNormSq ptolemyPointA ptolemyPointC = 36 / 25 ∧
      pointSegmentNormSq ptolemyPointB ptolemyPointD = 5184 / 7225 := by
  dsimp [ptolemyPointA, ptolemyPointB, ptolemyPointC, ptolemyPointD]
  constructor
  · rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq,
      RationalCircle.Stage.point_segmentNormSq_formula]
    native_decide
  constructor
  · rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq,
      RationalCircle.Stage.point_segmentNormSq_formula]
    native_decide
  constructor
  · rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq,
      RationalCircle.Stage.point_segmentNormSq_formula]
    native_decide
  constructor
  · rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq,
      RationalCircle.Stage.point_segmentNormSq_formula]
    native_decide
  constructor
  · rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq,
      RationalCircle.Stage.point_segmentNormSq_formula]
    native_decide
  · rw [pointSegmentNormSq_eq_rationalCircleSegmentNormSq,
      RationalCircle.Stage.point_segmentNormSq_formula]
    native_decide

/-! The main item-95 certificate.  Its first argument is the previously
proved square-root-free shadow; the conclusion supplies the six actual raw
length witnesses and the rational Ptolemy equality for this finite cyclic
quadrilateral. -/

theorem finitePtolemyLength_certificate
    :
    (pointSegmentLengthRaw ptolemyPointA ptolemyPointB).Equiv
        (RealRaw.ofRat (16 / 17)) ∧
      (pointSegmentLengthRaw ptolemyPointB ptolemyPointC).Equiv
        (RealRaw.ofRat (26 / 85)) ∧
      (pointSegmentLengthRaw ptolemyPointC ptolemyPointD).Equiv
        (RealRaw.ofRat (14 / 25)) ∧
      (pointSegmentLengthRaw ptolemyPointD ptolemyPointA).Equiv
        (RealRaw.ofRat (8 / 5)) ∧
      (pointSegmentLengthRaw ptolemyPointA ptolemyPointC).Equiv
        (RealRaw.ofRat (6 / 5)) ∧
      (pointSegmentLengthRaw ptolemyPointB ptolemyPointD).Equiv
        (RealRaw.ofRat (72 / 85)) ∧
      (16 / 17 : Rat) * (14 / 25) +
          (26 / 85) * (8 / 5) =
        (6 / 5) * (72 / 85) := by
  have hsquares := ptolemyPoint_square_coordinates
  have hpq : sq (16 / 17 : Rat) =
      pointSegmentNormSq ptolemyPointA ptolemyPointB := by
    rw [hsquares.1]
    native_decide
  have hqr : sq (26 / 85 : Rat) =
      pointSegmentNormSq ptolemyPointB ptolemyPointC := by
    rw [hsquares.2.1]
    native_decide
  have hrs : sq (14 / 25 : Rat) =
      pointSegmentNormSq ptolemyPointC ptolemyPointD := by
    rw [hsquares.2.2.1]
    native_decide
  have hsp : sq (8 / 5 : Rat) =
      pointSegmentNormSq ptolemyPointD ptolemyPointA := by
    rw [hsquares.2.2.2.1]
    native_decide
  have hpr : sq (6 / 5 : Rat) =
      pointSegmentNormSq ptolemyPointA ptolemyPointC := by
    rw [hsquares.2.2.2.2.1]
    native_decide
  have hqs : sq (72 / 85 : Rat) =
      pointSegmentNormSq ptolemyPointB ptolemyPointD := by
    rw [hsquares.2.2.2.2.2]
    native_decide
  constructor
  · have hpos : 0 <= (16 / 17 : Rat) := by native_decide
    simpa [qabs_eq_self_of_nonneg hpos] using pointSegmentLengthRaw_equiv_of_square
      ptolemyPointA ptolemyPointB (16 / 17) hpq
  constructor
  · have hpos : 0 <= (26 / 85 : Rat) := by native_decide
    simpa [qabs_eq_self_of_nonneg hpos] using pointSegmentLengthRaw_equiv_of_square
      ptolemyPointB ptolemyPointC (26 / 85) hqr
  constructor
  · have hpos : 0 <= (14 / 25 : Rat) := by native_decide
    simpa [qabs_eq_self_of_nonneg hpos] using pointSegmentLengthRaw_equiv_of_square
      ptolemyPointC ptolemyPointD (14 / 25) hrs
  constructor
  · have hpos : 0 <= (8 / 5 : Rat) := by native_decide
    simpa [qabs_eq_self_of_nonneg hpos] using pointSegmentLengthRaw_equiv_of_square
      ptolemyPointD ptolemyPointA (8 / 5) hsp
  constructor
  · have hpos : 0 <= (6 / 5 : Rat) := by native_decide
    simpa [qabs_eq_self_of_nonneg hpos] using pointSegmentLengthRaw_equiv_of_square
      ptolemyPointA ptolemyPointC (6 / 5) hpr
  constructor
  · have hpos : 0 <= (72 / 85 : Rat) := by native_decide
    simpa [qabs_eq_self_of_nonneg hpos] using pointSegmentLengthRaw_equiv_of_square
      ptolemyPointB ptolemyPointD (72 / 85) hqs
  · native_decide

end FinitePtolemyLength

end ComputableAnalysis
