import ComputableAnalysis.RationalCircle

/-!
# Trigonometric special values

This module keeps the chapter-two special-value layer separate from the core
rational-circle construction.  It reopens the public namespaces from
`RationalCircle.lean`, so blueprint declarations still live where a reader
expects them.
-/

namespace ComputableAnalysis

namespace RationalCircle

namespace Trigonometry

theorem cos_half :
    cos ((1 : Rat) / 2) = (3 : Rat) / 5 := by
  native_decide

theorem sin_half :
    sin ((1 : Rat) / 2) = (4 : Rat) / 5 := by
  native_decide

theorem tan_half :
    tan ((1 : Rat) / 2) = (4 : Rat) / 3 := by
  native_decide

theorem cot_half :
    cot ((1 : Rat) / 2) = (3 : Rat) / 4 := by
  native_decide

theorem sec_half :
    sec ((1 : Rat) / 2) = (5 : Rat) / 3 := by
  native_decide

theorem csc_half :
    csc ((1 : Rat) / 2) = (5 : Rat) / 4 := by
  native_decide

theorem cosRaw_zero_equiv :
    (cosRaw 0).Equiv (RealRaw.ofRat 1) := by
  simpa [cosRaw, cos_zero] using RealRaw.ofRat_equiv_self (1 : Rat)

theorem sinRaw_zero_equiv :
    (sinRaw 0).Equiv (RealRaw.ofRat 0) := by
  simpa [sinRaw, sin_zero] using RealRaw.ofRat_equiv_self (0 : Rat)

theorem cosRaw_one_equiv :
    (cosRaw 1).Equiv (RealRaw.ofRat 0) := by
  simpa [cosRaw, cos_one] using RealRaw.ofRat_equiv_self (0 : Rat)

theorem sinRaw_one_equiv :
    (sinRaw 1).Equiv (RealRaw.ofRat 1) := by
  simpa [sinRaw, sin_one] using RealRaw.ofRat_equiv_self (1 : Rat)

theorem cosRaw_half_equiv :
    (cosRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((3 : Rat) / 5)) := by
  simpa [cosRaw, cos_half] using RealRaw.ofRat_equiv_self ((3 : Rat) / 5)

theorem sinRaw_half_equiv :
    (sinRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((4 : Rat) / 5)) := by
  simpa [sinRaw, sin_half] using RealRaw.ofRat_equiv_self ((4 : Rat) / 5)

theorem tanRaw_half_equiv :
    (tanRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((4 : Rat) / 3)) := by
  simpa [tanRaw, tan_half] using RealRaw.ofRat_equiv_self ((4 : Rat) / 3)

theorem cotRaw_half_equiv :
    (cotRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((3 : Rat) / 4)) := by
  simpa [cotRaw, cot_half] using RealRaw.ofRat_equiv_self ((3 : Rat) / 4)

theorem secRaw_half_equiv :
    (secRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((5 : Rat) / 3)) := by
  simpa [secRaw, sec_half] using RealRaw.ofRat_equiv_self ((5 : Rat) / 3)

theorem cscRaw_half_equiv :
    (cscRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((5 : Rat) / 4)) := by
  simpa [cscRaw, csc_half] using RealRaw.ofRat_equiv_self ((5 : Rat) / 4)

/-- Special values that are already exact in the rational slope chart.

The input is the stereographic slope `u = tan(theta / 2)`, not the normalized
quarter-turn angle.  Thus `u = 1 / 2` is a rational Pythagorean sample rather
than one of the usual degree-marked angles. -/
structure SpecialValuePackage : Prop where
  cos_at_zero : cos 0 = 1
  sin_at_zero : sin 0 = 0
  cos_at_one : cos 1 = 0
  sin_at_one : sin 1 = 1
  cos_at_half : cos ((1 : Rat) / 2) = (3 : Rat) / 5
  sin_at_half : sin ((1 : Rat) / 2) = (4 : Rat) / 5
  tan_at_half : tan ((1 : Rat) / 2) = (4 : Rat) / 3
  cot_at_half : cot ((1 : Rat) / 2) = (3 : Rat) / 4
  sec_at_half : sec ((1 : Rat) / 2) = (5 : Rat) / 3
  csc_at_half : csc ((1 : Rat) / 2) = (5 : Rat) / 4
  cos_raw_at_zero : (cosRaw 0).Equiv (RealRaw.ofRat 1)
  sin_raw_at_zero : (sinRaw 0).Equiv (RealRaw.ofRat 0)
  cos_raw_at_one : (cosRaw 1).Equiv (RealRaw.ofRat 0)
  sin_raw_at_one : (sinRaw 1).Equiv (RealRaw.ofRat 1)
  cos_raw_at_half :
    (cosRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((3 : Rat) / 5))
  sin_raw_at_half :
    (sinRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((4 : Rat) / 5))
  tan_raw_at_half :
    (tanRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((4 : Rat) / 3))
  cot_raw_at_half :
    (cotRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((3 : Rat) / 4))
  sec_raw_at_half :
    (secRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((5 : Rat) / 3))
  csc_raw_at_half :
    (cscRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((5 : Rat) / 4))

theorem specialValuePackage : SpecialValuePackage where
  cos_at_zero := cos_zero
  sin_at_zero := sin_zero
  cos_at_one := cos_one
  sin_at_one := sin_one
  cos_at_half := cos_half
  sin_at_half := sin_half
  tan_at_half := tan_half
  cot_at_half := cot_half
  sec_at_half := sec_half
  csc_at_half := csc_half
  cos_raw_at_zero := cosRaw_zero_equiv
  sin_raw_at_zero := sinRaw_zero_equiv
  cos_raw_at_one := cosRaw_one_equiv
  sin_raw_at_one := sinRaw_one_equiv
  cos_raw_at_half := cosRaw_half_equiv
  sin_raw_at_half := sinRaw_half_equiv
  tan_raw_at_half := tanRaw_half_equiv
  cot_raw_at_half := cotRaw_half_equiv
  sec_raw_at_half := secRaw_half_equiv
  csc_raw_at_half := cscRaw_half_equiv

end Trigonometry

namespace GeometricTrig

theorem unitIntervalBranch_two_fifths :
    unitIntervalBranch ((2 : Rat) / 5) := by
  unfold unitIntervalBranch
  constructor <;> native_decide

theorem unitIntervalBranch_four_fifths :
    unitIntervalBranch ((4 : Rat) / 5) := by
  unfold unitIntervalBranch
  constructor <;> native_decide

theorem unitIntervalBranch_one_third :
    unitIntervalBranch ((1 : Rat) / 3) := by
  unfold unitIntervalBranch
  constructor <;> native_decide

theorem unitIntervalBranch_two_thirds :
    unitIntervalBranch ((2 : Rat) / 3) := by
  unfold unitIntervalBranch
  constructor <;> native_decide

namespace SpecialAngles

/-!
Named special-value targets for the normalized angle layer.

Here `t` denotes the angle `t * (pi / 2)`.  Thus `1 / 2` is forty-five
degrees, `1 / 3` is thirty degrees, `2 / 3` is sixty degrees, `2 / 5`
is thirty-six degrees, and `4 / 5` is seventy-two degrees.  The cosine values
at thirty-six and seventy-two degrees only need the rational sqrt algorithm
for `sqrt(5)`.  The corresponding sine values are recorded by their squares;
turning them into positive nested square-root values belongs to the later
raw-real square-root operation.
-/

theorem sqrtHalfDomain : sqrtDomain ((1 : Rat) / 2) := by
  unfold sqrtDomain
  native_decide

theorem sqrtFiveDomain : sqrtDomain (5 : Rat) := by
  unfold sqrtDomain
  native_decide

theorem sqrtThreeDomain : sqrtDomain (3 : Rat) := by
  unfold sqrtDomain
  native_decide

def sqrtHalfValue : RealRaw :=
  sqrtRaw ((1 : Rat) / 2) sqrtHalfDomain

def sqrtThreeValue : RealRaw :=
  sqrtRaw (3 : Rat) sqrtThreeDomain

def sqrtFiveValue : RealRaw :=
  sqrtRaw (5 : Rat) sqrtFiveDomain

def sqrtThreeHalfValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 2) sqrtThreeValue

def sqrtThreeThirdValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 3) sqrtThreeValue

def sqrtFiveHalfValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 2) sqrtFiveValue

def sqrtFiveQuarterValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 4) sqrtFiveValue

def cosFortyFiveValue : RealRaw :=
  sqrtHalfValue

def sinFortyFiveValue : RealRaw :=
  sqrtHalfValue

def sinThirtyValue : RealRaw :=
  RealRaw.ofRat ((1 : Rat) / 2)

def cosThirtyValue : RealRaw :=
  sqrtThreeHalfValue

def cosSixtyValue : RealRaw :=
  RealRaw.ofRat ((1 : Rat) / 2)

def sinSixtyValue : RealRaw :=
  sqrtThreeHalfValue

def tanThirtyValue : RealRaw :=
  sqrtThreeThirdValue

def tanSixtyValue : RealRaw :=
  sqrtThreeValue

def cosThirtySixValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 4) (sqrtFiveValue + RealRaw.ofRat 1)

def cosSeventyTwoValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 4) (sqrtFiveValue - RealRaw.ofRat 1)

def sinThirtySixSquareValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 8) (RealRaw.ofRat 5 - sqrtFiveValue)

def sinSeventyTwoSquareValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 8) (RealRaw.ofRat 5 + sqrtFiveValue)

theorem sqrtHalfValue_stage_spec (n : Nat) :
    SqrtIntervalSpec ((1 : Rat) / 2) (sqrtHalfValue.compute n) := by
  simpa [sqrtHalfValue] using
    sqrtRaw_stage_spec ((1 : Rat) / 2) sqrtHalfDomain n

theorem sqrtFiveValue_stage_spec (n : Nat) :
    SqrtIntervalSpec (5 : Rat) (sqrtFiveValue.compute n) := by
  simpa [sqrtFiveValue] using
    sqrtRaw_stage_spec (5 : Rat) sqrtFiveDomain n

theorem sqrtThreeValue_stage_spec (n : Nat) :
    SqrtIntervalSpec (3 : Rat) (sqrtThreeValue.compute n) := by
  simpa [sqrtThreeValue] using
    sqrtRaw_stage_spec (3 : Rat) sqrtThreeDomain n

theorem sqrtHalfValue_valid_of_spec
    (h : SqrtRawSpec ((1 : Rat) / 2) sqrtHalfDomain) :
    sqrtHalfValue.Valid := by
  simpa [sqrtHalfValue] using h.1

theorem sqrtThreeValue_valid_of_spec
    (h : SqrtRawSpec (3 : Rat) sqrtThreeDomain) :
    sqrtThreeValue.Valid := by
  simpa [sqrtThreeValue] using h.1

theorem sqrtFiveValue_valid_of_spec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    sqrtFiveValue.Valid := by
  simpa [sqrtFiveValue] using h.1

theorem sqrtThreeHalfValue_valid_of_sqrtThreeSpec
    (h : SqrtRawSpec (3 : Rat) sqrtThreeDomain) :
    sqrtThreeHalfValue.Valid := by
  unfold sqrtThreeHalfValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (sqrtThreeValue_valid_of_spec h)

theorem sqrtThreeThirdValue_valid_of_sqrtThreeSpec
    (h : SqrtRawSpec (3 : Rat) sqrtThreeDomain) :
    sqrtThreeThirdValue.Valid := by
  unfold sqrtThreeThirdValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (sqrtThreeValue_valid_of_spec h)

theorem sqrtFiveHalfValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    sqrtFiveHalfValue.Valid := by
  unfold sqrtFiveHalfValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (sqrtFiveValue_valid_of_spec h)

theorem sqrtFiveQuarterValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    sqrtFiveQuarterValue.Valid := by
  unfold sqrtFiveQuarterValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (sqrtFiveValue_valid_of_spec h)

theorem sinThirtyValue_valid :
    sinThirtyValue.Valid := by
  simpa [sinThirtyValue] using RealRaw.ofRat_valid ((1 : Rat) / 2)

theorem cosSixtyValue_valid :
    cosSixtyValue.Valid := by
  simpa [cosSixtyValue] using RealRaw.ofRat_valid ((1 : Rat) / 2)

theorem cosThirtyValue_valid_of_sqrtThreeSpec
    (h : SqrtRawSpec (3 : Rat) sqrtThreeDomain) :
    cosThirtyValue.Valid := by
  simpa [cosThirtyValue] using sqrtThreeHalfValue_valid_of_sqrtThreeSpec h

theorem sinSixtyValue_valid_of_sqrtThreeSpec
    (h : SqrtRawSpec (3 : Rat) sqrtThreeDomain) :
    sinSixtyValue.Valid := by
  simpa [sinSixtyValue] using sqrtThreeHalfValue_valid_of_sqrtThreeSpec h

theorem tanThirtyValue_valid_of_sqrtThreeSpec
    (h : SqrtRawSpec (3 : Rat) sqrtThreeDomain) :
    tanThirtyValue.Valid := by
  simpa [tanThirtyValue] using sqrtThreeThirdValue_valid_of_sqrtThreeSpec h

theorem tanSixtyValue_valid_of_sqrtThreeSpec
    (h : SqrtRawSpec (3 : Rat) sqrtThreeDomain) :
    tanSixtyValue.Valid := by
  simpa [tanSixtyValue] using sqrtThreeValue_valid_of_spec h

theorem cosFortyFiveValue_valid_of_sqrtHalfSpec
    (h : SqrtRawSpec ((1 : Rat) / 2) sqrtHalfDomain) :
    cosFortyFiveValue.Valid := by
  simpa [cosFortyFiveValue] using sqrtHalfValue_valid_of_spec h

theorem sinFortyFiveValue_valid_of_sqrtHalfSpec
    (h : SqrtRawSpec ((1 : Rat) / 2) sqrtHalfDomain) :
    sinFortyFiveValue.Valid := by
  simpa [sinFortyFiveValue] using sqrtHalfValue_valid_of_spec h

theorem cosThirtySixValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    cosThirtySixValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hone : (RealRaw.ofRat (1 : Rat)).Valid := by
    simpa using RealRaw.ofRat_valid (1 : Rat)
  unfold cosThirtySixValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.add_valid hsqrt hone)

theorem cosSeventyTwoValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    cosSeventyTwoValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hone : (RealRaw.ofRat (1 : Rat)).Valid := by
    simpa using RealRaw.ofRat_valid (1 : Rat)
  unfold cosSeventyTwoValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.sub_valid hsqrt hone)

theorem sinThirtySixSquareValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    sinThirtySixSquareValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hfive : (RealRaw.ofRat (5 : Rat)).Valid := by
    simpa using RealRaw.ofRat_valid (5 : Rat)
  unfold sinThirtySixSquareValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.sub_valid hfive hsqrt)

theorem sinSeventyTwoSquareValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    sinSeventyTwoSquareValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hfive : (RealRaw.ofRat (5 : Rat)).Valid := by
    simpa using RealRaw.ofRat_valid (5 : Rat)
  unfold sinSeventyTwoSquareValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.add_valid hfive hsqrt)

structure SpecialAngleDisplayedValuesValid : Prop where
  sqrt_half : sqrtHalfValue.Valid
  sqrt_three : sqrtThreeValue.Valid
  sqrt_five : sqrtFiveValue.Valid
  sqrt_three_half : sqrtThreeHalfValue.Valid
  sqrt_three_third : sqrtThreeThirdValue.Valid
  sqrt_five_half : sqrtFiveHalfValue.Valid
  sqrt_five_quarter : sqrtFiveQuarterValue.Valid
  cos_forty_five : cosFortyFiveValue.Valid
  sin_forty_five : sinFortyFiveValue.Valid
  sin_thirty : sinThirtyValue.Valid
  cos_thirty : cosThirtyValue.Valid
  cos_sixty : cosSixtyValue.Valid
  sin_sixty : sinSixtyValue.Valid
  tan_thirty : tanThirtyValue.Valid
  tan_sixty : tanSixtyValue.Valid
  cos_thirty_six : cosThirtySixValue.Valid
  cos_seventy_two : cosSeventyTwoValue.Valid
  sin_thirty_six_square : sinThirtySixSquareValue.Valid
  sin_seventy_two_square : sinSeventyTwoSquareValue.Valid

theorem specialAngleDisplayedValuesValid_of_sqrtSpecs
    (hhalf : SqrtRawSpec ((1 : Rat) / 2) sqrtHalfDomain)
    (hthree : SqrtRawSpec (3 : Rat) sqrtThreeDomain)
    (hfive : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    SpecialAngleDisplayedValuesValid where
  sqrt_half := sqrtHalfValue_valid_of_spec hhalf
  sqrt_three := sqrtThreeValue_valid_of_spec hthree
  sqrt_five := sqrtFiveValue_valid_of_spec hfive
  sqrt_three_half := sqrtThreeHalfValue_valid_of_sqrtThreeSpec hthree
  sqrt_three_third := sqrtThreeThirdValue_valid_of_sqrtThreeSpec hthree
  sqrt_five_half := sqrtFiveHalfValue_valid_of_sqrtFiveSpec hfive
  sqrt_five_quarter := sqrtFiveQuarterValue_valid_of_sqrtFiveSpec hfive
  cos_forty_five := cosFortyFiveValue_valid_of_sqrtHalfSpec hhalf
  sin_forty_five := sinFortyFiveValue_valid_of_sqrtHalfSpec hhalf
  sin_thirty := sinThirtyValue_valid
  cos_thirty := cosThirtyValue_valid_of_sqrtThreeSpec hthree
  cos_sixty := cosSixtyValue_valid
  sin_sixty := sinSixtyValue_valid_of_sqrtThreeSpec hthree
  tan_thirty := tanThirtyValue_valid_of_sqrtThreeSpec hthree
  tan_sixty := tanSixtyValue_valid_of_sqrtThreeSpec hthree
  cos_thirty_six := cosThirtySixValue_valid_of_sqrtFiveSpec hfive
  cos_seventy_two := cosSeventyTwoValue_valid_of_sqrtFiveSpec hfive
  sin_thirty_six_square :=
    sinThirtySixSquareValue_valid_of_sqrtFiveSpec hfive
  sin_seventy_two_square :=
    sinSeventyTwoSquareValue_valid_of_sqrtFiveSpec hfive

theorem specialAngleDisplayedValuesValid :
    SpecialAngleDisplayedValuesValid :=
  specialAngleDisplayedValuesValid_of_sqrtSpecs
    (sqrtRaw_spec ((1 : Rat) / 2) sqrtHalfDomain)
    (sqrtRaw_spec (3 : Rat) sqrtThreeDomain)
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

def CosValue (C : FunctionRawConstruction) (t : QuarterTurn)
    (value : RealRaw) : Prop :=
  Exists fun ht : C.cosFunctionRaw.definedAt t =>
    (C.cosFunctionRaw.evalRaw t ht).Equiv value

def SinValue (C : FunctionRawConstruction) (t : QuarterTurn)
    (value : RealRaw) : Prop :=
  Exists fun ht : C.sinFunctionRaw.definedAt t =>
    (C.sinFunctionRaw.evalRaw t ht).Equiv value

def rawSquare (x : RealRaw) : RealRaw :=
  x * x

def SinSquareValue (C : FunctionRawConstruction) (t : QuarterTurn)
    (value : RealRaw) : Prop :=
  Exists fun ht : C.sinFunctionRaw.definedAt t =>
    (rawSquare (C.sinFunctionRaw.evalRaw t ht)).Equiv value

/-- Special values expected of the geometric, normalized-angle sine and cosine
construction once the angle-to-circle-point algorithm has endpoint,
equilateral-triangle, and pentagon-value theorems. -/
structure SpecialAngleValueTargets (C : FunctionRawConstruction) : Prop where
  cos_zero : CosValue C 0 (RealRaw.ofRat 1)
  sin_zero : SinValue C 0 (RealRaw.ofRat 0)
  cos_one : CosValue C 1 (RealRaw.ofRat 0)
  sin_one : SinValue C 1 (RealRaw.ofRat 1)
  cos_forty_five : CosValue C ((1 : Rat) / 2) cosFortyFiveValue
  sin_forty_five : SinValue C ((1 : Rat) / 2) sinFortyFiveValue
  sin_thirty : SinValue C ((1 : Rat) / 3) sinThirtyValue
  cos_thirty : CosValue C ((1 : Rat) / 3) cosThirtyValue
  cos_sixty : CosValue C ((2 : Rat) / 3) cosSixtyValue
  sin_sixty : SinValue C ((2 : Rat) / 3) sinSixtyValue
  cos_thirty_six : CosValue C ((2 : Rat) / 5) cosThirtySixValue
  cos_seventy_two : CosValue C ((4 : Rat) / 5) cosSeventyTwoValue
  sin_thirty_six_square :
    SinSquareValue C ((2 : Rat) / 5) sinThirtySixSquareValue
  sin_seventy_two_square :
    SinSquareValue C ((4 : Rat) / 5) sinSeventyTwoSquareValue

end SpecialAngles

end GeometricTrig

end RationalCircle

end ComputableAnalysis
