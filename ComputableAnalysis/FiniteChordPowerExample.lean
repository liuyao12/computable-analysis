import ComputableAnalysis.RationalCircle

/-!
# A second worked power-of-a-point certificate

For the rational circle point `(4/5,3/5)` and external horizontal point `1`,
the directed chord product is `9/25`, whose certified square root is `3/5`.
-/

namespace ComputableAnalysis

namespace RationalCircle

theorem horizontalChordPowerSqrtRaw_equiv_three_fifths :
    (horizontalChordPowerSqrtRaw (4 / 5) 1
      (by native_decide) (by native_decide)).Equiv
      (RealRaw.ofRat (3 / 5)) := by
  have h := horizontalChordPowerSqrtRaw_equiv_of_square
    (4 / 5) 1 (3 / 5) (by native_decide) (by native_decide)
      (by native_decide)
  have hqabs : qabs (3 / 5 : Rat) = 3 / 5 := by native_decide
  simpa [hqabs] using h

/-! The interior-point branch is genuinely signed: the directed product is
negative, so it is not yet an unsigned chord-length certificate. -/

theorem horizontalChordPower_inside_three_fifths_certificate :
    (4 / 5 : Rat) * (4 / 5) + (3 / 5) * (3 / 5) = 1 /\
      -(4 / 5 : Rat) < 1 / 2 /\
      (1 / 2 : Rat) < 4 / 5 /\
      ((1 / 2 : Rat) + 4 / 5) * (1 / 2 - 4 / 5) = -39 / 100 /\
      ((1 / 2 : Rat) + 4 / 5) * (1 / 2 - 4 / 5) < 0 := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

end RationalCircle

end ComputableAnalysis
