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
  cos_raw_at_zero : (cosRaw 0).Equiv (RealRaw.ofRat 1)
  sin_raw_at_zero : (sinRaw 0).Equiv (RealRaw.ofRat 0)
  cos_raw_at_one : (cosRaw 1).Equiv (RealRaw.ofRat 0)
  sin_raw_at_one : (sinRaw 1).Equiv (RealRaw.ofRat 1)
  cos_raw_at_half :
    (cosRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((3 : Rat) / 5))
  sin_raw_at_half :
    (sinRaw ((1 : Rat) / 2)).Equiv (RealRaw.ofRat ((4 : Rat) / 5))

theorem specialValuePackage : SpecialValuePackage where
  cos_at_zero := cos_zero
  sin_at_zero := sin_zero
  cos_at_one := cos_one
  sin_at_one := sin_one
  cos_at_half := cos_half
  sin_at_half := sin_half
  cos_raw_at_zero := cosRaw_zero_equiv
  sin_raw_at_zero := sinRaw_zero_equiv
  cos_raw_at_one := cosRaw_one_equiv
  sin_raw_at_one := sinRaw_one_equiv
  cos_raw_at_half := cosRaw_half_equiv
  sin_raw_at_half := sinRaw_half_equiv

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

def sqrtHalfValue : RealRaw :=
  sqrtRaw ((1 : Rat) / 2) sqrtHalfDomain

def sqrtFiveValue : RealRaw :=
  sqrtRaw (5 : Rat) sqrtFiveDomain

def cosFortyFiveValue : RealRaw :=
  sqrtHalfValue

def sinFortyFiveValue : RealRaw :=
  sqrtHalfValue

def sinThirtyValue : RealRaw :=
  RealRaw.ofRat ((1 : Rat) / 2)

def cosSixtyValue : RealRaw :=
  RealRaw.ofRat ((1 : Rat) / 2)

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

theorem sqrtHalfValue_valid_of_spec
    (h : SqrtRawSpec ((1 : Rat) / 2) sqrtHalfDomain) :
    sqrtHalfValue.Valid := by
  simpa [sqrtHalfValue] using h.1

theorem sqrtFiveValue_valid_of_spec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    sqrtFiveValue.Valid := by
  simpa [sqrtFiveValue] using h.1

theorem sinThirtyValue_valid :
    sinThirtyValue.Valid := by
  simpa [sinThirtyValue] using RealRaw.ofRat_valid ((1 : Rat) / 2)

theorem cosSixtyValue_valid :
    cosSixtyValue.Valid := by
  simpa [cosSixtyValue] using RealRaw.ofRat_valid ((1 : Rat) / 2)

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
  cos_sixty : CosValue C ((2 : Rat) / 3) cosSixtyValue
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
