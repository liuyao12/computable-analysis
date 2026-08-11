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

theorem finiteTan_half :
    finiteTan ((1 : Rat) / 2) = (4 : Rat) / 3 := by
  native_decide

theorem tan_half :
    tan ((1 : Rat) / 2) = ProjectiveRat.finite ((4 : Rat) / 3) := by
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
  simpa [tanRaw, finiteTan_half] using
    RealRaw.ofRat_equiv_self ((4 : Rat) / 3)

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
  finite_tan_at_half : finiteTan ((1 : Rat) / 2) = (4 : Rat) / 3
  tan_at_half : tan ((1 : Rat) / 2) = ProjectiveRat.finite ((4 : Rat) / 3)
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
  finite_tan_at_half := finiteTan_half
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

def tanZeroValue : RealRaw :=
  RealRaw.ofRat (0 : Rat)

def tanThirtyValue : RealRaw :=
  sqrtThreeThirdValue

def tanFortyFiveValue : RealRaw :=
  RealRaw.ofRat (1 : Rat)

def tanSixtyValue : RealRaw :=
  sqrtThreeValue

def cosThirtySixValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 4) (sqrtFiveValue + RealRaw.ofRat 1)

def cosSeventyTwoValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 4) (sqrtFiveValue - RealRaw.ofRat 1)

def cosThirtySixSquareValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 8) (RealRaw.ofRat 3 + sqrtFiveValue)

def cosSeventyTwoSquareValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 8) (RealRaw.ofRat 3 - sqrtFiveValue)

def sinThirtySixSquareValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 8) (RealRaw.ofRat 5 - sqrtFiveValue)

def sinSeventyTwoSquareValue : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 8) (RealRaw.ofRat 5 + sqrtFiveValue)

def tanThirtySixSquareValue : RealRaw :=
  RealRaw.ofRat (5 : Rat) - RealRaw.scaleRat (2 : Rat) sqrtFiveValue

def tanSeventyTwoSquareValue : RealRaw :=
  RealRaw.ofRat (5 : Rat) + RealRaw.scaleRat (2 : Rat) sqrtFiveValue

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
  change RealRaw.ValidCompute (fun _ => { lo := (1 : Rat) / 2, hi := 1 / 2 })
  exact RealRaw.ofRat_valid ((1 : Rat) / 2)

theorem cosSixtyValue_valid :
    cosSixtyValue.Valid := by
  change RealRaw.ValidCompute (fun _ => { lo := (1 : Rat) / 2, hi := 1 / 2 })
  exact RealRaw.ofRat_valid ((1 : Rat) / 2)

theorem tanZeroValue_valid :
    tanZeroValue.Valid := by
  change RealRaw.ValidCompute (fun _ => { lo := 0, hi := 0 })
  exact RealRaw.ofRat_valid (0 : Rat)

theorem tanFortyFiveValue_valid :
    tanFortyFiveValue.Valid := by
  change RealRaw.ValidCompute (fun _ => { lo := 1, hi := 1 })
  exact RealRaw.ofRat_valid (1 : Rat)

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
    change RealRaw.ValidCompute (fun _ => { lo := 1, hi := 1 })
    exact RealRaw.ofRat_valid (1 : Rat)
  unfold cosThirtySixValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.add_valid hsqrt hone)

theorem cosSeventyTwoValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    cosSeventyTwoValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hone : (RealRaw.ofRat (1 : Rat)).Valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 1, hi := 1 })
    exact RealRaw.ofRat_valid (1 : Rat)
  unfold cosSeventyTwoValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.sub_valid hsqrt hone)

theorem cosThirtySixSquareValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    cosThirtySixSquareValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hthree : (RealRaw.ofRat (3 : Rat)).Valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 3, hi := 3 })
    exact RealRaw.ofRat_valid (3 : Rat)
  unfold cosThirtySixSquareValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.add_valid hthree hsqrt)

theorem cosSeventyTwoSquareValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    cosSeventyTwoSquareValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hthree : (RealRaw.ofRat (3 : Rat)).Valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 3, hi := 3 })
    exact RealRaw.ofRat_valid (3 : Rat)
  unfold cosSeventyTwoSquareValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.sub_valid hthree hsqrt)

theorem sinThirtySixSquareValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    sinThirtySixSquareValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hfive : (RealRaw.ofRat (5 : Rat)).Valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 5, hi := 5 })
    exact RealRaw.ofRat_valid (5 : Rat)
  unfold sinThirtySixSquareValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.sub_valid hfive hsqrt)

theorem sinSeventyTwoSquareValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    sinSeventyTwoSquareValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hfive : (RealRaw.ofRat (5 : Rat)).Valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 5, hi := 5 })
    exact RealRaw.ofRat_valid (5 : Rat)
  unfold sinSeventyTwoSquareValue
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (RealRaw.add_valid hfive hsqrt)

theorem tanThirtySixSquareValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    tanThirtySixSquareValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hfive : (RealRaw.ofRat (5 : Rat)).Valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 5, hi := 5 })
    exact RealRaw.ofRat_valid (5 : Rat)
  have htwoSqrt : (RealRaw.scaleRat (2 : Rat) sqrtFiveValue).Valid :=
    RealRaw.scaleRat_valid_of_nonneg (by native_decide) hsqrt
  unfold tanThirtySixSquareValue
  exact RealRaw.sub_valid hfive htwoSqrt

theorem tanSeventyTwoSquareValue_valid_of_sqrtFiveSpec
    (h : SqrtRawSpec (5 : Rat) sqrtFiveDomain) :
    tanSeventyTwoSquareValue.Valid := by
  have hsqrt : sqrtFiveValue.Valid := sqrtFiveValue_valid_of_spec h
  have hfive : (RealRaw.ofRat (5 : Rat)).Valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 5, hi := 5 })
    exact RealRaw.ofRat_valid (5 : Rat)
  have htwoSqrt : (RealRaw.scaleRat (2 : Rat) sqrtFiveValue).Valid :=
    RealRaw.scaleRat_valid_of_nonneg (by native_decide) hsqrt
  unfold tanSeventyTwoSquareValue
  exact RealRaw.add_valid hfive htwoSqrt

theorem sqrtHalfValue_valid :
    sqrtHalfValue.Valid :=
  sqrtHalfValue_valid_of_spec
    (sqrtRaw_spec ((1 : Rat) / 2) sqrtHalfDomain)

theorem sqrtThreeValue_valid :
    sqrtThreeValue.Valid :=
  sqrtThreeValue_valid_of_spec
    (sqrtRaw_spec (3 : Rat) sqrtThreeDomain)

theorem sqrtFiveValue_valid :
    sqrtFiveValue.Valid :=
  sqrtFiveValue_valid_of_spec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem sqrtThreeHalfValue_valid :
    sqrtThreeHalfValue.Valid :=
  sqrtThreeHalfValue_valid_of_sqrtThreeSpec
    (sqrtRaw_spec (3 : Rat) sqrtThreeDomain)

theorem sqrtThreeThirdValue_valid :
    sqrtThreeThirdValue.Valid :=
  sqrtThreeThirdValue_valid_of_sqrtThreeSpec
    (sqrtRaw_spec (3 : Rat) sqrtThreeDomain)

theorem sqrtFiveHalfValue_valid :
    sqrtFiveHalfValue.Valid :=
  sqrtFiveHalfValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem sqrtFiveQuarterValue_valid :
    sqrtFiveQuarterValue.Valid :=
  sqrtFiveQuarterValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem cosFortyFiveValue_valid :
    cosFortyFiveValue.Valid :=
  cosFortyFiveValue_valid_of_sqrtHalfSpec
    (sqrtRaw_spec ((1 : Rat) / 2) sqrtHalfDomain)

theorem sinFortyFiveValue_valid :
    sinFortyFiveValue.Valid :=
  sinFortyFiveValue_valid_of_sqrtHalfSpec
    (sqrtRaw_spec ((1 : Rat) / 2) sqrtHalfDomain)

theorem cosThirtyValue_valid :
    cosThirtyValue.Valid :=
  cosThirtyValue_valid_of_sqrtThreeSpec
    (sqrtRaw_spec (3 : Rat) sqrtThreeDomain)

theorem sinSixtyValue_valid :
    sinSixtyValue.Valid :=
  sinSixtyValue_valid_of_sqrtThreeSpec
    (sqrtRaw_spec (3 : Rat) sqrtThreeDomain)

theorem tanThirtyValue_valid :
    tanThirtyValue.Valid :=
  tanThirtyValue_valid_of_sqrtThreeSpec
    (sqrtRaw_spec (3 : Rat) sqrtThreeDomain)

theorem tanSixtyValue_valid :
    tanSixtyValue.Valid :=
  tanSixtyValue_valid_of_sqrtThreeSpec
    (sqrtRaw_spec (3 : Rat) sqrtThreeDomain)

theorem cosThirtySixValue_valid :
    cosThirtySixValue.Valid :=
  cosThirtySixValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem cosSeventyTwoValue_valid :
    cosSeventyTwoValue.Valid :=
  cosSeventyTwoValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem cosThirtySixSquareValue_valid :
    cosThirtySixSquareValue.Valid :=
  cosThirtySixSquareValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem cosSeventyTwoSquareValue_valid :
    cosSeventyTwoSquareValue.Valid :=
  cosSeventyTwoSquareValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem sinThirtySixSquareValue_valid :
    sinThirtySixSquareValue.Valid :=
  sinThirtySixSquareValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem sinSeventyTwoSquareValue_valid :
    sinSeventyTwoSquareValue.Valid :=
  sinSeventyTwoSquareValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem tanThirtySixSquareValue_valid :
    tanThirtySixSquareValue.Valid :=
  tanThirtySixSquareValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

theorem tanSeventyTwoSquareValue_valid :
    tanSeventyTwoSquareValue.Valid :=
  tanSeventyTwoSquareValue_valid_of_sqrtFiveSpec
    (sqrtRaw_spec (5 : Rat) sqrtFiveDomain)

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
  tan_zero : tanZeroValue.Valid
  tan_thirty : tanThirtyValue.Valid
  tan_forty_five : tanFortyFiveValue.Valid
  tan_sixty : tanSixtyValue.Valid
  cos_thirty_six : cosThirtySixValue.Valid
  cos_seventy_two : cosSeventyTwoValue.Valid
  cos_thirty_six_square : cosThirtySixSquareValue.Valid
  cos_seventy_two_square : cosSeventyTwoSquareValue.Valid
  sin_thirty_six_square : sinThirtySixSquareValue.Valid
  sin_seventy_two_square : sinSeventyTwoSquareValue.Valid
  tan_thirty_six_square : tanThirtySixSquareValue.Valid
  tan_seventy_two_square : tanSeventyTwoSquareValue.Valid

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
  tan_zero := tanZeroValue_valid
  tan_thirty := tanThirtyValue_valid_of_sqrtThreeSpec hthree
  tan_forty_five := tanFortyFiveValue_valid
  tan_sixty := tanSixtyValue_valid_of_sqrtThreeSpec hthree
  cos_thirty_six := cosThirtySixValue_valid_of_sqrtFiveSpec hfive
  cos_seventy_two := cosSeventyTwoValue_valid_of_sqrtFiveSpec hfive
  cos_thirty_six_square :=
    cosThirtySixSquareValue_valid_of_sqrtFiveSpec hfive
  cos_seventy_two_square :=
    cosSeventyTwoSquareValue_valid_of_sqrtFiveSpec hfive
  sin_thirty_six_square :=
    sinThirtySixSquareValue_valid_of_sqrtFiveSpec hfive
  sin_seventy_two_square :=
    sinSeventyTwoSquareValue_valid_of_sqrtFiveSpec hfive
  tan_thirty_six_square :=
    tanThirtySixSquareValue_valid_of_sqrtFiveSpec hfive
  tan_seventy_two_square :=
    tanSeventyTwoSquareValue_valid_of_sqrtFiveSpec hfive

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

private theorem min4_le_first (a b c d : Rat) :
    min4 a b c d <= a := by
  unfold min4 minRat
  grind

private theorem fourth_le_max4 (a b c d : Rat) :
    d <= max4 a b c d := by
  unfold max4 maxRat2
  grind

private theorem rawSquare_sqrt_equiv_of_stageSpec
    {q : Rat} {x : RealRaw}
    (hstage : forall n, SqrtIntervalSpec q (x.compute n)) :
    (rawSquare x).Equiv (RealRaw.ofRat q) := by
  intro n
  let I := x.compute n
  have hspec := hstage n
  apply (RealRaw.compareAt_overlap_iff
    (rawSquare x) (RealRaw.ofRat q) n n).2
  change QInterval.Overlaps
    (QBox.mulRealInterval I.lo I.hi I.lo I.hi)
    ((RealRaw.ofRat q).compute n)
  unfold QBox.mulRealInterval QInterval.Overlaps RealRaw.ofRat
  exact ⟨Rat.le_trans
      (min4_le_first
        (I.lo * I.lo)
        (I.lo * I.hi)
        (I.hi * I.lo)
        (I.hi * I.hi))
      (by
        dsimp [I]
        simpa [sq] using hspec.2.2.1),
    Rat.le_trans
      (by
        dsimp [I]
        simpa [sq] using hspec.2.2.2)
      (fourth_le_max4
        (I.lo * I.lo)
        (I.lo * I.hi)
        (I.hi * I.lo)
        (I.hi * I.hi))⟩

private theorem rawSquare_scale_sqrt_equiv_of_stageSpec
    {q : Rat} {x : RealRaw}
    (hstage : forall n, SqrtIntervalSpec q (x.compute n))
    (r : Rat) (hr : 0 <= r) :
    (rawSquare (RealRaw.scaleRat r x)).Equiv
      (RealRaw.ofRat (r * r * q)) := by
  intro n
  let I := x.compute n
  have hspec := hstage n
  have hr2 : 0 <= r * r := Rat.mul_nonneg hr hr
  have hlo :
      (r * I.lo) * (r * I.lo) <= r * r * q := by
    have h := Rat.mul_le_mul_of_nonneg_left hspec.2.2.1 hr2
    dsimp [I] at h ⊢
    unfold sq at h
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hhi :
      r * r * q <= (r * I.hi) * (r * I.hi) := by
    have h := Rat.mul_le_mul_of_nonneg_left hspec.2.2.2 hr2
    dsimp [I] at h ⊢
    unfold sq at h
    grind [Rat.mul_assoc, Rat.mul_comm]
  apply (RealRaw.compareAt_overlap_iff
    (rawSquare (RealRaw.scaleRat r x))
    (RealRaw.ofRat (r * r * q)) n n).2
  unfold rawSquare
  change QInterval.Overlaps
    (RealRaw.mulCompute
      (RealRaw.scaleRat r x) (RealRaw.scaleRat r x) n)
    ((RealRaw.ofRat (r * r * q)).compute n)
  unfold RealRaw.mulCompute RealRaw.scaleRat RealRaw.scaleRatCompute
  simp [hr]
  change QInterval.Overlaps
    (QBox.mulRealInterval
      (r * I.lo) (r * I.hi) (r * I.lo) (r * I.hi))
    ((RealRaw.ofRat (r * r * q)).compute n)
  unfold QBox.mulRealInterval QInterval.Overlaps RealRaw.ofRat
  exact ⟨Rat.le_trans
      (min4_le_first
        ((r * I.lo) * (r * I.lo))
        ((r * I.lo) * (r * I.hi))
        ((r * I.hi) * (r * I.lo))
        ((r * I.hi) * (r * I.hi)))
      hlo,
    Rat.le_trans hhi
      (fourth_le_max4
        ((r * I.lo) * (r * I.lo))
        ((r * I.lo) * (r * I.hi))
        ((r * I.hi) * (r * I.lo))
        ((r * I.hi) * (r * I.hi)))⟩

private theorem rawSquare_ofRat_equiv (q : Rat) :
    (rawSquare (RealRaw.ofRat q)).Equiv (RealRaw.ofRat (q * q)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (rawSquare (RealRaw.ofRat q)) (RealRaw.ofRat (q * q)) n n).2
  change QInterval.Overlaps
    (QBox.mulRealInterval q q q q)
    ((RealRaw.ofRat (q * q)).compute n)
  unfold QBox.mulRealInterval QInterval.Overlaps RealRaw.ofRat
    min4 max4 minRat maxRat2
  grind

theorem tanZeroValue_square_equiv :
    (rawSquare tanZeroValue).Equiv (RealRaw.ofRat (0 : Rat)) := by
  have hrat : (0 : Rat) * (0 : Rat) = 0 := by
    native_decide
  simpa [tanZeroValue, hrat] using rawSquare_ofRat_equiv (0 : Rat)

theorem tanFortyFiveValue_square_equiv :
    (rawSquare tanFortyFiveValue).Equiv (RealRaw.ofRat (1 : Rat)) := by
  have hrat : (1 : Rat) * (1 : Rat) = 1 := by
    native_decide
  simpa [tanFortyFiveValue, hrat] using rawSquare_ofRat_equiv (1 : Rat)

theorem sqrtHalfValue_square_equiv :
    (rawSquare sqrtHalfValue).Equiv (RealRaw.ofRat ((1 : Rat) / 2)) := by
  exact rawSquare_sqrt_equiv_of_stageSpec
    (q := (1 : Rat) / 2) (x := sqrtHalfValue)
    sqrtHalfValue_stage_spec

theorem sqrtThreeValue_square_equiv :
    (rawSquare sqrtThreeValue).Equiv (RealRaw.ofRat (3 : Rat)) := by
  exact rawSquare_sqrt_equiv_of_stageSpec
    (q := (3 : Rat)) (x := sqrtThreeValue)
    sqrtThreeValue_stage_spec

theorem sqrtFiveValue_square_equiv :
    (rawSquare sqrtFiveValue).Equiv (RealRaw.ofRat (5 : Rat)) := by
  exact rawSquare_sqrt_equiv_of_stageSpec
    (q := (5 : Rat)) (x := sqrtFiveValue)
    sqrtFiveValue_stage_spec

theorem sqrtThreeHalfValue_square_equiv :
    (rawSquare sqrtThreeHalfValue).Equiv
      (RealRaw.ofRat ((3 : Rat) / 4)) := by
  have hrat :
      ((1 : Rat) / 2) * ((1 : Rat) / 2) * 3 = (3 : Rat) / 4 := by
    native_decide
  simpa [sqrtThreeHalfValue, hrat] using
    rawSquare_scale_sqrt_equiv_of_stageSpec
      (q := (3 : Rat)) (x := sqrtThreeValue)
      sqrtThreeValue_stage_spec ((1 : Rat) / 2) (by native_decide)

theorem sqrtThreeThirdValue_square_equiv :
    (rawSquare sqrtThreeThirdValue).Equiv
      (RealRaw.ofRat ((1 : Rat) / 3)) := by
  have hrat :
      ((1 : Rat) / 3) * ((1 : Rat) / 3) * 3 = (1 : Rat) / 3 := by
    native_decide
  simpa [sqrtThreeThirdValue, hrat] using
    rawSquare_scale_sqrt_equiv_of_stageSpec
      (q := (3 : Rat)) (x := sqrtThreeValue)
      sqrtThreeValue_stage_spec ((1 : Rat) / 3) (by native_decide)

theorem sqrtFiveHalfValue_square_equiv :
    (rawSquare sqrtFiveHalfValue).Equiv
      (RealRaw.ofRat ((5 : Rat) / 4)) := by
  have hrat :
      ((1 : Rat) / 2) * ((1 : Rat) / 2) * 5 = (5 : Rat) / 4 := by
    native_decide
  simpa [sqrtFiveHalfValue, hrat] using
    rawSquare_scale_sqrt_equiv_of_stageSpec
      (q := (5 : Rat)) (x := sqrtFiveValue)
      sqrtFiveValue_stage_spec ((1 : Rat) / 2) (by native_decide)

theorem sqrtFiveQuarterValue_square_equiv :
    (rawSquare sqrtFiveQuarterValue).Equiv
      (RealRaw.ofRat ((5 : Rat) / 16)) := by
  have hrat :
      ((1 : Rat) / 4) * ((1 : Rat) / 4) * 5 = (5 : Rat) / 16 := by
    native_decide
  simpa [sqrtFiveQuarterValue, hrat] using
    rawSquare_scale_sqrt_equiv_of_stageSpec
      (q := (5 : Rat)) (x := sqrtFiveValue)
      sqrtFiveValue_stage_spec ((1 : Rat) / 4) (by native_decide)

theorem cosFortyFiveValue_square_equiv :
    (rawSquare cosFortyFiveValue).Equiv
      (RealRaw.ofRat ((1 : Rat) / 2)) := by
  simpa [cosFortyFiveValue] using sqrtHalfValue_square_equiv

theorem sinFortyFiveValue_square_equiv :
    (rawSquare sinFortyFiveValue).Equiv
      (RealRaw.ofRat ((1 : Rat) / 2)) := by
  simpa [sinFortyFiveValue] using sqrtHalfValue_square_equiv

theorem sinThirtyValue_square_equiv :
    (rawSquare sinThirtyValue).Equiv
      (RealRaw.ofRat ((1 : Rat) / 4)) := by
  have hrat :
      ((1 : Rat) / 2) * ((1 : Rat) / 2) = (1 : Rat) / 4 := by
    native_decide
  simpa [sinThirtyValue, hrat] using
    rawSquare_ofRat_equiv ((1 : Rat) / 2)

theorem cosThirtyValue_square_equiv :
    (rawSquare cosThirtyValue).Equiv
      (RealRaw.ofRat ((3 : Rat) / 4)) := by
  simpa [cosThirtyValue] using sqrtThreeHalfValue_square_equiv

theorem cosSixtyValue_square_equiv :
    (rawSquare cosSixtyValue).Equiv
      (RealRaw.ofRat ((1 : Rat) / 4)) := by
  have hrat :
      ((1 : Rat) / 2) * ((1 : Rat) / 2) = (1 : Rat) / 4 := by
    native_decide
  simpa [cosSixtyValue, hrat] using
    rawSquare_ofRat_equiv ((1 : Rat) / 2)

theorem sinSixtyValue_square_equiv :
    (rawSquare sinSixtyValue).Equiv
      (RealRaw.ofRat ((3 : Rat) / 4)) := by
  simpa [sinSixtyValue] using sqrtThreeHalfValue_square_equiv

theorem tanThirtyValue_square_equiv :
    (rawSquare tanThirtyValue).Equiv
      (RealRaw.ofRat ((1 : Rat) / 3)) := by
  simpa [tanThirtyValue] using sqrtThreeThirdValue_square_equiv

theorem tanSixtyValue_square_equiv :
    (rawSquare tanSixtyValue).Equiv (RealRaw.ofRat (3 : Rat)) := by
  simpa [tanSixtyValue] using sqrtThreeValue_square_equiv

private theorem cosThirtySixValue_square_overlap
    (n : Nat) :
    QInterval.Overlaps
      ((rawSquare cosThirtySixValue).compute n)
      (cosThirtySixSquareValue.compute n) := by
  let I := sqrtFiveValue.compute n
  have hspec := sqrtFiveValue_stage_spec n
  have hlohi : I.lo <= I.hi := hspec.2.1
  have hlo_sq : I.lo * I.lo <= (5 : Rat) := by
    simpa [I, sq] using hspec.2.2.1
  have hhi_sq : (5 : Rat) <= I.hi * I.hi := by
    simpa [I, sq] using hspec.2.2.2
  have hcos_value_lo :
      (cosThirtySixValue.compute n).lo =
        (1 : Rat) / 4 * (I.lo + 1) := by
    unfold cosThirtySixValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 4)]
    change
      (1 : Rat) / 4 *
          ((RealRaw.add sqrtFiveValue (RealRaw.ofRat 1)).compute n).lo =
        (1 : Rat) / 4 * (I.lo + 1)
    unfold RealRaw.add RealRaw.addCompute RealRaw.ofRat
    simp [I]
  have hcos_value_hi :
      (cosThirtySixValue.compute n).hi =
        (1 : Rat) / 4 * (I.hi + 1) := by
    unfold cosThirtySixValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 4)]
    change
      (1 : Rat) / 4 *
          ((RealRaw.add sqrtFiveValue (RealRaw.ofRat 1)).compute n).hi =
        (1 : Rat) / 4 * (I.hi + 1)
    unfold RealRaw.add RealRaw.addCompute RealRaw.ofRat
    simp [I]
  have hcos_lo :
      ((rawSquare cosThirtySixValue).compute n).lo <=
        ((1 : Rat) / 4 * (I.lo + 1)) *
          ((1 : Rat) / 4 * (I.lo + 1)) := by
    unfold rawSquare
    change
      (QBox.mulRealInterval
        (cosThirtySixValue.compute n).lo
        (cosThirtySixValue.compute n).hi
        (cosThirtySixValue.compute n).lo
        (cosThirtySixValue.compute n).hi).lo <=
          ((1 : Rat) / 4 * (I.lo + 1)) *
            ((1 : Rat) / 4 * (I.lo + 1))
    simpa [QBox.mulRealInterval, hcos_value_lo] using
      min4_le_first
        ((1 : Rat) / 4 * (I.lo + 1) *
          ((1 : Rat) / 4 * (I.lo + 1)))
        ((1 : Rat) / 4 * (I.lo + 1) *
          (cosThirtySixValue.compute n).hi)
        ((cosThirtySixValue.compute n).hi *
          ((1 : Rat) / 4 * (I.lo + 1)))
        ((cosThirtySixValue.compute n).hi *
          (cosThirtySixValue.compute n).hi)
  have hcos_hi :
      ((1 : Rat) / 4 * (I.hi + 1)) *
          ((1 : Rat) / 4 * (I.hi + 1)) <=
        ((rawSquare cosThirtySixValue).compute n).hi := by
    unfold rawSquare
    change
      ((1 : Rat) / 4 * (I.hi + 1)) *
          ((1 : Rat) / 4 * (I.hi + 1)) <=
        (QBox.mulRealInterval
          (cosThirtySixValue.compute n).lo
          (cosThirtySixValue.compute n).hi
          (cosThirtySixValue.compute n).lo
          (cosThirtySixValue.compute n).hi).hi
    simpa [QBox.mulRealInterval, hcos_value_hi] using
      fourth_le_max4
        ((cosThirtySixValue.compute n).lo *
          (cosThirtySixValue.compute n).lo)
        ((cosThirtySixValue.compute n).lo *
          ((1 : Rat) / 4 * (I.hi + 1)))
        (((1 : Rat) / 4 * (I.hi + 1)) *
          (cosThirtySixValue.compute n).lo)
        (((1 : Rat) / 4 * (I.hi + 1)) *
          ((1 : Rat) / 4 * (I.hi + 1)))
  have htarget_lo :
      (cosThirtySixSquareValue.compute n).lo =
        (1 : Rat) / 8 * (3 + I.lo) := by
    unfold cosThirtySixSquareValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 8)]
    change
      (1 : Rat) / 8 *
          ((RealRaw.add (RealRaw.ofRat 3) sqrtFiveValue).compute n).lo =
        (1 : Rat) / 8 * (3 + I.lo)
    unfold RealRaw.add RealRaw.addCompute RealRaw.ofRat
    simp [I]
  have htarget_hi :
      (cosThirtySixSquareValue.compute n).hi =
        (1 : Rat) / 8 * (3 + I.hi) := by
    unfold cosThirtySixSquareValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 8)]
    change
      (1 : Rat) / 8 *
          ((RealRaw.add (RealRaw.ofRat 3) sqrtFiveValue).compute n).hi =
        (1 : Rat) / 8 * (3 + I.hi)
    unfold RealRaw.add RealRaw.addCompute RealRaw.ofRat
    simp [I]
  unfold QInterval.Overlaps
  constructor
  · calc
      ((rawSquare cosThirtySixValue).compute n).lo <=
          ((1 : Rat) / 4 * (I.lo + 1)) *
            ((1 : Rat) / 4 * (I.lo + 1)) := hcos_lo
      _ <= (1 : Rat) / 8 * (3 + I.hi) := by
        have htwo : (2 : Rat) * I.lo <= 2 * I.hi :=
          Rat.mul_le_mul_of_nonneg_left hlohi (by native_decide)
        have hgap :
            I.lo * I.lo + 2 * I.lo - 2 * I.hi <= (5 : Rat) := by
          grind
        apply Rat.le_of_mul_le_mul_right (c := (16 : Rat))
        · grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        · native_decide
      _ = (cosThirtySixSquareValue.compute n).hi := by rw [htarget_hi]
  · calc
      (cosThirtySixSquareValue.compute n).lo =
          (1 : Rat) / 8 * (3 + I.lo) := htarget_lo
      _ <= ((1 : Rat) / 4 * (I.hi + 1)) *
          ((1 : Rat) / 4 * (I.hi + 1)) := by
        have htwo : (2 : Rat) * I.lo <= 2 * I.hi :=
          Rat.mul_le_mul_of_nonneg_left hlohi (by native_decide)
        have hgap :
            (5 : Rat) + 2 * I.lo <= I.hi * I.hi + 2 * I.hi := by
          grind
        apply Rat.le_of_mul_le_mul_right (c := (16 : Rat))
        · grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        · native_decide
      _ <= ((rawSquare cosThirtySixValue).compute n).hi := hcos_hi

theorem cosThirtySixValue_square_equiv :
    (rawSquare cosThirtySixValue).Equiv cosThirtySixSquareValue := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (rawSquare cosThirtySixValue) cosThirtySixSquareValue n n).2
  exact cosThirtySixValue_square_overlap n

private theorem cosSeventyTwoValue_square_overlap
    (n : Nat) :
    QInterval.Overlaps
      ((rawSquare cosSeventyTwoValue).compute n)
      (cosSeventyTwoSquareValue.compute n) := by
  let I := sqrtFiveValue.compute n
  have hspec := sqrtFiveValue_stage_spec n
  have hlo_sq : I.lo * I.lo <= (5 : Rat) := by
    simpa [I, sq] using hspec.2.2.1
  have hhi_sq : (5 : Rat) <= I.hi * I.hi := by
    simpa [I, sq] using hspec.2.2.2
  have hcos_value_lo :
      (cosSeventyTwoValue.compute n).lo =
        (1 : Rat) / 4 * (I.lo - 1) := by
    unfold cosSeventyTwoValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 4)]
    change
      (1 : Rat) / 4 *
          ((RealRaw.sub sqrtFiveValue (RealRaw.ofRat 1)).compute n).lo =
        (1 : Rat) / 4 * (I.lo - 1)
    unfold RealRaw.sub RealRaw.subCompute RealRaw.ofRat
    simp [I]
  have hcos_value_hi :
      (cosSeventyTwoValue.compute n).hi =
        (1 : Rat) / 4 * (I.hi - 1) := by
    unfold cosSeventyTwoValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 4)]
    change
      (1 : Rat) / 4 *
          ((RealRaw.sub sqrtFiveValue (RealRaw.ofRat 1)).compute n).hi =
        (1 : Rat) / 4 * (I.hi - 1)
    unfold RealRaw.sub RealRaw.subCompute RealRaw.ofRat
    simp [I]
  have hcos_lo :
      ((rawSquare cosSeventyTwoValue).compute n).lo <=
        ((1 : Rat) / 4 * (I.lo - 1)) *
          ((1 : Rat) / 4 * (I.lo - 1)) := by
    unfold rawSquare
    change
      (QBox.mulRealInterval
        (cosSeventyTwoValue.compute n).lo
        (cosSeventyTwoValue.compute n).hi
        (cosSeventyTwoValue.compute n).lo
        (cosSeventyTwoValue.compute n).hi).lo <=
          ((1 : Rat) / 4 * (I.lo - 1)) *
            ((1 : Rat) / 4 * (I.lo - 1))
    simpa [QBox.mulRealInterval, hcos_value_lo] using
      min4_le_first
        ((1 : Rat) / 4 * (I.lo - 1) *
          ((1 : Rat) / 4 * (I.lo - 1)))
        ((1 : Rat) / 4 * (I.lo - 1) *
          (cosSeventyTwoValue.compute n).hi)
        ((cosSeventyTwoValue.compute n).hi *
          ((1 : Rat) / 4 * (I.lo - 1)))
        ((cosSeventyTwoValue.compute n).hi *
          (cosSeventyTwoValue.compute n).hi)
  have hcos_hi :
      ((1 : Rat) / 4 * (I.hi - 1)) *
          ((1 : Rat) / 4 * (I.hi - 1)) <=
        ((rawSquare cosSeventyTwoValue).compute n).hi := by
    unfold rawSquare
    change
      ((1 : Rat) / 4 * (I.hi - 1)) *
          ((1 : Rat) / 4 * (I.hi - 1)) <=
        (QBox.mulRealInterval
          (cosSeventyTwoValue.compute n).lo
          (cosSeventyTwoValue.compute n).hi
          (cosSeventyTwoValue.compute n).lo
          (cosSeventyTwoValue.compute n).hi).hi
    simpa [QBox.mulRealInterval, hcos_value_hi] using
      fourth_le_max4
        ((cosSeventyTwoValue.compute n).lo *
          (cosSeventyTwoValue.compute n).lo)
        ((cosSeventyTwoValue.compute n).lo *
          ((1 : Rat) / 4 * (I.hi - 1)))
        (((1 : Rat) / 4 * (I.hi - 1)) *
          (cosSeventyTwoValue.compute n).lo)
        (((1 : Rat) / 4 * (I.hi - 1)) *
          ((1 : Rat) / 4 * (I.hi - 1)))
  have htarget_lo :
      (cosSeventyTwoSquareValue.compute n).lo =
        (1 : Rat) / 8 * (3 - I.hi) := by
    unfold cosSeventyTwoSquareValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 8)]
    change
      (1 : Rat) / 8 *
          ((RealRaw.sub (RealRaw.ofRat 3) sqrtFiveValue).compute n).lo =
        (1 : Rat) / 8 * (3 - I.hi)
    unfold RealRaw.sub RealRaw.subCompute RealRaw.ofRat
    simp [I]
  have htarget_hi :
      (cosSeventyTwoSquareValue.compute n).hi =
        (1 : Rat) / 8 * (3 - I.lo) := by
    unfold cosSeventyTwoSquareValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 8)]
    change
      (1 : Rat) / 8 *
          ((RealRaw.sub (RealRaw.ofRat 3) sqrtFiveValue).compute n).hi =
        (1 : Rat) / 8 * (3 - I.lo)
    unfold RealRaw.sub RealRaw.subCompute RealRaw.ofRat
    simp [I]
  unfold QInterval.Overlaps
  constructor
  · calc
      ((rawSquare cosSeventyTwoValue).compute n).lo <=
          ((1 : Rat) / 4 * (I.lo - 1)) *
            ((1 : Rat) / 4 * (I.lo - 1)) := hcos_lo
      _ <= (1 : Rat) / 8 * (3 - I.lo) := by
        apply Rat.le_of_mul_le_mul_right (c := (16 : Rat))
        · grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        · native_decide
      _ = (cosSeventyTwoSquareValue.compute n).hi := by rw [htarget_hi]
  · calc
      (cosSeventyTwoSquareValue.compute n).lo =
          (1 : Rat) / 8 * (3 - I.hi) := htarget_lo
      _ <= ((1 : Rat) / 4 * (I.hi - 1)) *
          ((1 : Rat) / 4 * (I.hi - 1)) := by
        apply Rat.le_of_mul_le_mul_right (c := (16 : Rat))
        · grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        · native_decide
      _ <= ((rawSquare cosSeventyTwoValue).compute n).hi := hcos_hi

theorem cosSeventyTwoValue_square_equiv :
    (rawSquare cosSeventyTwoValue).Equiv cosSeventyTwoSquareValue := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (rawSquare cosSeventyTwoValue) cosSeventyTwoSquareValue n n).2
  exact cosSeventyTwoValue_square_overlap n

private theorem realRaw_add_equiv_of_equiv_ofRat
    {x y : RealRaw} {a b : Rat}
    (hx : x.Equiv (RealRaw.ofRat a))
    (hy : y.Equiv (RealRaw.ofRat b)) :
    (x + y).Equiv (RealRaw.ofRat (a + b)) := by
  intro n
  have hxover := (RealRaw.compareAt_overlap_iff
    x (RealRaw.ofRat a) n n).1 (hx n)
  have hyover := (RealRaw.compareAt_overlap_iff
    y (RealRaw.ofRat b) n n).1 (hy n)
  apply (RealRaw.compareAt_overlap_iff
    (x + y) (RealRaw.ofRat (a + b)) n n).2
  change QInterval.Overlaps (RealRaw.addCompute x y n)
    ((RealRaw.ofRat (a + b)).compute n)
  unfold RealRaw.addCompute RealRaw.ofRat QInterval.Overlaps at hxover hyover ⊢
  constructor <;> grind

private theorem realRaw_scaleRat_equiv_of_equiv_ofRat
    {x : RealRaw} {a r b : Rat}
    (hx : x.Equiv (RealRaw.ofRat a)) (hr : 0 <= r)
    (hb : r * a = b) :
    (RealRaw.scaleRat r x).Equiv (RealRaw.ofRat b) := by
  intro n
  have hxover := (RealRaw.compareAt_overlap_iff
    x (RealRaw.ofRat a) n n).1 (hx n)
  apply (RealRaw.compareAt_overlap_iff
    (RealRaw.scaleRat r x) (RealRaw.ofRat b) n n).2
  change QInterval.Overlaps (RealRaw.scaleRatCompute r x n)
    ((RealRaw.ofRat b).compute n)
  unfold RealRaw.scaleRatCompute RealRaw.ofRat QInterval.Overlaps at hxover ⊢
  simp [hr]
  rw [← hb]
  exact ⟨Rat.mul_le_mul_of_nonneg_left hxover.1 hr,
    Rat.mul_le_mul_of_nonneg_left hxover.2 hr⟩

private theorem realRaw_equiv_of_equiv_same_ofRat
    {x y : RealRaw} {q : Rat}
    (hx : x.Equiv (RealRaw.ofRat q))
    (hy : y.Equiv (RealRaw.ofRat q)) :
    x.Equiv y := by
  intro n
  have hxover := (RealRaw.compareAt_overlap_iff
    x (RealRaw.ofRat q) n n).1 (hx n)
  have hyover := (RealRaw.compareAt_overlap_iff
    y (RealRaw.ofRat q) n n).1 (hy n)
  apply (RealRaw.compareAt_overlap_iff x y n n).2
  exact ⟨Rat.le_trans hxover.1 hyover.2,
    Rat.le_trans hyover.1 hxover.2⟩

theorem cosFortyFive_square_add_sinFortyFive_square_equiv_one :
    (rawSquare cosFortyFiveValue + rawSquare sinFortyFiveValue).Equiv
      (RealRaw.ofRat (1 : Rat)) := by
  have hsum :=
    realRaw_add_equiv_of_equiv_ofRat
      cosFortyFiveValue_square_equiv
      sinFortyFiveValue_square_equiv
  have hrat : ((1 : Rat) / 2) + ((1 : Rat) / 2) = 1 := by
    native_decide
  simpa [hrat] using hsum

theorem cosThirty_square_add_sinThirty_square_equiv_one :
    (rawSquare cosThirtyValue + rawSquare sinThirtyValue).Equiv
      (RealRaw.ofRat (1 : Rat)) := by
  have hsum :=
    realRaw_add_equiv_of_equiv_ofRat
      cosThirtyValue_square_equiv
      sinThirtyValue_square_equiv
  have hrat : ((3 : Rat) / 4) + ((1 : Rat) / 4) = 1 := by
    native_decide
  simpa [hrat] using hsum

theorem cosSixty_square_add_sinSixty_square_equiv_one :
    (rawSquare cosSixtyValue + rawSquare sinSixtyValue).Equiv
      (RealRaw.ofRat (1 : Rat)) := by
  have hsum :=
    realRaw_add_equiv_of_equiv_ofRat
      cosSixtyValue_square_equiv
      sinSixtyValue_square_equiv
  have hrat : ((1 : Rat) / 4) + ((3 : Rat) / 4) = 1 := by
    native_decide
  simpa [hrat] using hsum

theorem tanThirty_square_scale_cosThirty_square_equiv_sinThirty_square :
    (RealRaw.scaleRat ((1 : Rat) / 3)
        (rawSquare cosThirtyValue)).Equiv
      (rawSquare sinThirtyValue) := by
  have hleft :
      (RealRaw.scaleRat ((1 : Rat) / 3)
          (rawSquare cosThirtyValue)).Equiv
        (RealRaw.ofRat ((1 : Rat) / 4)) :=
    realRaw_scaleRat_equiv_of_equiv_ofRat
      cosThirtyValue_square_equiv
      (by native_decide : 0 <= ((1 : Rat) / 3))
      (by native_decide :
        ((1 : Rat) / 3) * ((3 : Rat) / 4) = (1 : Rat) / 4)
  exact realRaw_equiv_of_equiv_same_ofRat hleft sinThirtyValue_square_equiv

theorem tanFortyFive_square_scale_cosFortyFive_square_equiv_sinFortyFive_square :
    (RealRaw.scaleRat (1 : Rat)
        (rawSquare cosFortyFiveValue)).Equiv
      (rawSquare sinFortyFiveValue) := by
  have hleft :
      (RealRaw.scaleRat (1 : Rat)
          (rawSquare cosFortyFiveValue)).Equiv
        (RealRaw.ofRat ((1 : Rat) / 2)) :=
    realRaw_scaleRat_equiv_of_equiv_ofRat
      cosFortyFiveValue_square_equiv
      (by native_decide : 0 <= (1 : Rat))
      (by native_decide :
        (1 : Rat) * ((1 : Rat) / 2) = (1 : Rat) / 2)
  exact realRaw_equiv_of_equiv_same_ofRat hleft sinFortyFiveValue_square_equiv

theorem tanSixty_square_scale_cosSixty_square_equiv_sinSixty_square :
    (RealRaw.scaleRat (3 : Rat)
        (rawSquare cosSixtyValue)).Equiv
      (rawSquare sinSixtyValue) := by
  have hleft :
      (RealRaw.scaleRat (3 : Rat)
          (rawSquare cosSixtyValue)).Equiv
        (RealRaw.ofRat ((3 : Rat) / 4)) :=
    realRaw_scaleRat_equiv_of_equiv_ofRat
      cosSixtyValue_square_equiv
      (by native_decide : 0 <= (3 : Rat))
      (by native_decide :
        (3 : Rat) * ((1 : Rat) / 4) = (3 : Rat) / 4)
  exact realRaw_equiv_of_equiv_same_ofRat hleft sinSixtyValue_square_equiv

private theorem realRaw_add_overlap_of_lower_upper
    {x y : RealRaw} {q : Rat} (n : Nat)
    (hlo : (x.compute n).lo + (y.compute n).lo <= q)
    (hhi : q <= (x.compute n).hi + (y.compute n).hi) :
    QInterval.Overlaps ((x + y).compute n) ((RealRaw.ofRat q).compute n) := by
  change QInterval.Overlaps (RealRaw.addCompute x y n)
    ((RealRaw.ofRat q).compute n)
  unfold RealRaw.addCompute RealRaw.ofRat QInterval.Overlaps
  exact ⟨hlo, hhi⟩

private theorem cosThirtySix_square_add_sinThirtySixSquare_overlap_one
    (n : Nat) :
    QInterval.Overlaps
      ((rawSquare cosThirtySixValue + sinThirtySixSquareValue).compute n)
      ((RealRaw.ofRat (1 : Rat)).compute n) := by
  let I := sqrtFiveValue.compute n
  have hspec := sqrtFiveValue_stage_spec n
  have hlo0 : 0 <= I.lo := hspec.1
  have hlohi : I.lo <= I.hi := hspec.2.1
  have hlo_sq : I.lo * I.lo <= (5 : Rat) := by
    simpa [I, sq] using hspec.2.2.1
  have hhi_sq : (5 : Rat) <= I.hi * I.hi := by
    simpa [I, sq] using hspec.2.2.2
  have hcos_value_lo :
      (cosThirtySixValue.compute n).lo =
        (1 : Rat) / 4 * (I.lo + 1) := by
    unfold cosThirtySixValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 4)]
    change
      (1 : Rat) / 4 *
          ((RealRaw.add sqrtFiveValue (RealRaw.ofRat 1)).compute n).lo =
        (1 : Rat) / 4 * (I.lo + 1)
    unfold RealRaw.add RealRaw.addCompute RealRaw.ofRat
    simp [I]
  have hcos_value_hi :
      (cosThirtySixValue.compute n).hi =
        (1 : Rat) / 4 * (I.hi + 1) := by
    unfold cosThirtySixValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 4)]
    change
      (1 : Rat) / 4 *
          ((RealRaw.add sqrtFiveValue (RealRaw.ofRat 1)).compute n).hi =
        (1 : Rat) / 4 * (I.hi + 1)
    unfold RealRaw.add RealRaw.addCompute RealRaw.ofRat
    simp [I]
  have hcos_lo :
      ((rawSquare cosThirtySixValue).compute n).lo <=
        ((1 : Rat) / 4 * (I.lo + 1)) *
          ((1 : Rat) / 4 * (I.lo + 1)) := by
    unfold rawSquare
    change
      (QBox.mulRealInterval
        (cosThirtySixValue.compute n).lo
        (cosThirtySixValue.compute n).hi
        (cosThirtySixValue.compute n).lo
        (cosThirtySixValue.compute n).hi).lo <=
          ((1 : Rat) / 4 * (I.lo + 1)) *
            ((1 : Rat) / 4 * (I.lo + 1))
    simpa [QBox.mulRealInterval, hcos_value_lo] using
      min4_le_first
        ((1 : Rat) / 4 * (I.lo + 1) *
          ((1 : Rat) / 4 * (I.lo + 1)))
        ((1 : Rat) / 4 * (I.lo + 1) *
          (cosThirtySixValue.compute n).hi)
        ((cosThirtySixValue.compute n).hi *
          ((1 : Rat) / 4 * (I.lo + 1)))
        ((cosThirtySixValue.compute n).hi *
          (cosThirtySixValue.compute n).hi)
  have hcos_hi :
      ((1 : Rat) / 4 * (I.hi + 1)) *
          ((1 : Rat) / 4 * (I.hi + 1)) <=
        ((rawSquare cosThirtySixValue).compute n).hi := by
    unfold rawSquare
    change
      ((1 : Rat) / 4 * (I.hi + 1)) *
          ((1 : Rat) / 4 * (I.hi + 1)) <=
        (QBox.mulRealInterval
          (cosThirtySixValue.compute n).lo
          (cosThirtySixValue.compute n).hi
          (cosThirtySixValue.compute n).lo
          (cosThirtySixValue.compute n).hi).hi
    simpa [QBox.mulRealInterval, hcos_value_hi] using
      fourth_le_max4
        ((cosThirtySixValue.compute n).lo *
          (cosThirtySixValue.compute n).lo)
        ((cosThirtySixValue.compute n).lo *
          ((1 : Rat) / 4 * (I.hi + 1)))
        (((1 : Rat) / 4 * (I.hi + 1)) *
          (cosThirtySixValue.compute n).lo)
        (((1 : Rat) / 4 * (I.hi + 1)) *
          ((1 : Rat) / 4 * (I.hi + 1)))
  have hsin_lo :
      (sinThirtySixSquareValue.compute n).lo =
        (1 : Rat) / 8 * (5 - I.hi) := by
    unfold sinThirtySixSquareValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 8)]
    change
      (1 : Rat) / 8 *
          ((RealRaw.sub (RealRaw.ofRat 5) sqrtFiveValue).compute n).lo =
        (1 : Rat) / 8 * (5 - I.hi)
    unfold RealRaw.sub RealRaw.subCompute RealRaw.ofRat
    simp [I]
  have hsin_hi :
      (sinThirtySixSquareValue.compute n).hi =
        (1 : Rat) / 8 * (5 - I.lo) := by
    unfold sinThirtySixSquareValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 8)]
    change
      (1 : Rat) / 8 *
          ((RealRaw.sub (RealRaw.ofRat 5) sqrtFiveValue).compute n).hi =
        (1 : Rat) / 8 * (5 - I.lo)
    unfold RealRaw.sub RealRaw.subCompute RealRaw.ofRat
    simp [I]
  apply realRaw_add_overlap_of_lower_upper
  · calc
      ((rawSquare cosThirtySixValue).compute n).lo +
          (sinThirtySixSquareValue.compute n).lo
          <=
        ((1 : Rat) / 4 * (I.lo + 1)) *
            ((1 : Rat) / 4 * (I.lo + 1)) +
          ((1 : Rat) / 8 * (5 - I.hi)) := by
            rw [hsin_lo]
            grind
      _ <= 1 := by
        have htwo : (2 : Rat) * I.lo <= 2 * I.hi :=
          Rat.mul_le_mul_of_nonneg_left hlohi (by native_decide)
        have hgap :
            I.lo * I.lo + 2 * I.lo - 2 * I.hi <= (5 : Rat) := by
          grind
        apply Rat.le_of_mul_le_mul_right (c := (16 : Rat))
        · grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        · native_decide
  · calc
      (1 : Rat) <=
        ((1 : Rat) / 4 * (I.hi + 1)) *
            ((1 : Rat) / 4 * (I.hi + 1)) +
          ((1 : Rat) / 8 * (5 - I.lo)) := by
        have htwo : (2 : Rat) * I.lo <= 2 * I.hi :=
          Rat.mul_le_mul_of_nonneg_left hlohi (by native_decide)
        have hgap :
            (5 : Rat) <= I.hi * I.hi + 2 * I.hi - 2 * I.lo := by
          grind
        apply Rat.le_of_mul_le_mul_right (c := (16 : Rat))
        · grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        · native_decide
      _ <= ((rawSquare cosThirtySixValue).compute n).hi +
          (sinThirtySixSquareValue.compute n).hi := by
            rw [hsin_hi]
            grind

theorem cosThirtySix_square_add_sinThirtySixSquare_equiv_one :
    (rawSquare cosThirtySixValue + sinThirtySixSquareValue).Equiv
      (RealRaw.ofRat (1 : Rat)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (rawSquare cosThirtySixValue + sinThirtySixSquareValue)
    (RealRaw.ofRat (1 : Rat)) n n).2
  exact cosThirtySix_square_add_sinThirtySixSquare_overlap_one n

private theorem cosSeventyTwo_square_add_sinSeventyTwoSquare_overlap_one
    (n : Nat) :
    QInterval.Overlaps
      ((rawSquare cosSeventyTwoValue + sinSeventyTwoSquareValue).compute n)
      ((RealRaw.ofRat (1 : Rat)).compute n) := by
  let I := sqrtFiveValue.compute n
  have hspec := sqrtFiveValue_stage_spec n
  have hlohi : I.lo <= I.hi := hspec.2.1
  have hlo_sq : I.lo * I.lo <= (5 : Rat) := by
    simpa [I, sq] using hspec.2.2.1
  have hhi_sq : (5 : Rat) <= I.hi * I.hi := by
    simpa [I, sq] using hspec.2.2.2
  have hcos_value_lo :
      (cosSeventyTwoValue.compute n).lo =
        (1 : Rat) / 4 * (I.lo - 1) := by
    unfold cosSeventyTwoValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 4)]
    change
      (1 : Rat) / 4 *
          ((RealRaw.sub sqrtFiveValue (RealRaw.ofRat 1)).compute n).lo =
        (1 : Rat) / 4 * (I.lo - 1)
    unfold RealRaw.sub RealRaw.subCompute RealRaw.ofRat
    simp [I]
  have hcos_value_hi :
      (cosSeventyTwoValue.compute n).hi =
        (1 : Rat) / 4 * (I.hi - 1) := by
    unfold cosSeventyTwoValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 4)]
    change
      (1 : Rat) / 4 *
          ((RealRaw.sub sqrtFiveValue (RealRaw.ofRat 1)).compute n).hi =
        (1 : Rat) / 4 * (I.hi - 1)
    unfold RealRaw.sub RealRaw.subCompute RealRaw.ofRat
    simp [I]
  have hcos_lo :
      ((rawSquare cosSeventyTwoValue).compute n).lo <=
        ((1 : Rat) / 4 * (I.lo - 1)) *
          ((1 : Rat) / 4 * (I.lo - 1)) := by
    unfold rawSquare
    change
      (QBox.mulRealInterval
        (cosSeventyTwoValue.compute n).lo
        (cosSeventyTwoValue.compute n).hi
        (cosSeventyTwoValue.compute n).lo
        (cosSeventyTwoValue.compute n).hi).lo <=
          ((1 : Rat) / 4 * (I.lo - 1)) *
            ((1 : Rat) / 4 * (I.lo - 1))
    simpa [QBox.mulRealInterval, hcos_value_lo] using
      min4_le_first
        ((1 : Rat) / 4 * (I.lo - 1) *
          ((1 : Rat) / 4 * (I.lo - 1)))
        ((1 : Rat) / 4 * (I.lo - 1) *
          (cosSeventyTwoValue.compute n).hi)
        ((cosSeventyTwoValue.compute n).hi *
          ((1 : Rat) / 4 * (I.lo - 1)))
        ((cosSeventyTwoValue.compute n).hi *
          (cosSeventyTwoValue.compute n).hi)
  have hcos_hi :
      ((1 : Rat) / 4 * (I.hi - 1)) *
          ((1 : Rat) / 4 * (I.hi - 1)) <=
        ((rawSquare cosSeventyTwoValue).compute n).hi := by
    unfold rawSquare
    change
      ((1 : Rat) / 4 * (I.hi - 1)) *
          ((1 : Rat) / 4 * (I.hi - 1)) <=
        (QBox.mulRealInterval
          (cosSeventyTwoValue.compute n).lo
          (cosSeventyTwoValue.compute n).hi
          (cosSeventyTwoValue.compute n).lo
          (cosSeventyTwoValue.compute n).hi).hi
    simpa [QBox.mulRealInterval, hcos_value_hi] using
      fourth_le_max4
        ((cosSeventyTwoValue.compute n).lo *
          (cosSeventyTwoValue.compute n).lo)
        ((cosSeventyTwoValue.compute n).lo *
          ((1 : Rat) / 4 * (I.hi - 1)))
        (((1 : Rat) / 4 * (I.hi - 1)) *
          (cosSeventyTwoValue.compute n).lo)
        (((1 : Rat) / 4 * (I.hi - 1)) *
          ((1 : Rat) / 4 * (I.hi - 1)))
  have hsin_lo :
      (sinSeventyTwoSquareValue.compute n).lo =
        (1 : Rat) / 8 * (5 + I.lo) := by
    unfold sinSeventyTwoSquareValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 8)]
    change
      (1 : Rat) / 8 *
          ((RealRaw.add (RealRaw.ofRat 5) sqrtFiveValue).compute n).lo =
        (1 : Rat) / 8 * (5 + I.lo)
    unfold RealRaw.add RealRaw.addCompute RealRaw.ofRat
    simp [I]
  have hsin_hi :
      (sinSeventyTwoSquareValue.compute n).hi =
        (1 : Rat) / 8 * (5 + I.hi) := by
    unfold sinSeventyTwoSquareValue RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp
    rw [if_pos (by native_decide : (0 : Rat) <= (1 : Rat) / 8)]
    change
      (1 : Rat) / 8 *
          ((RealRaw.add (RealRaw.ofRat 5) sqrtFiveValue).compute n).hi =
        (1 : Rat) / 8 * (5 + I.hi)
    unfold RealRaw.add RealRaw.addCompute RealRaw.ofRat
    simp [I]
  apply realRaw_add_overlap_of_lower_upper
  · calc
      ((rawSquare cosSeventyTwoValue).compute n).lo +
          (sinSeventyTwoSquareValue.compute n).lo
          <=
        ((1 : Rat) / 4 * (I.lo - 1)) *
            ((1 : Rat) / 4 * (I.lo - 1)) +
          ((1 : Rat) / 8 * (5 + I.lo)) := by
            rw [hsin_lo]
            grind
      _ <= 1 := by
        apply Rat.le_of_mul_le_mul_right (c := (16 : Rat))
        · grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        · native_decide
  · calc
      (1 : Rat) <=
        ((1 : Rat) / 4 * (I.hi - 1)) *
            ((1 : Rat) / 4 * (I.hi - 1)) +
          ((1 : Rat) / 8 * (5 + I.hi)) := by
        apply Rat.le_of_mul_le_mul_right (c := (16 : Rat))
        · grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        · native_decide
      _ <= ((rawSquare cosSeventyTwoValue).compute n).hi +
          (sinSeventyTwoSquareValue.compute n).hi := by
            rw [hsin_hi]
            grind

theorem cosSeventyTwo_square_add_sinSeventyTwoSquare_equiv_one :
    (rawSquare cosSeventyTwoValue + sinSeventyTwoSquareValue).Equiv
      (RealRaw.ofRat (1 : Rat)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (rawSquare cosSeventyTwoValue + sinSeventyTwoSquareValue)
    (RealRaw.ofRat (1 : Rat)) n n).2
  exact cosSeventyTwo_square_add_sinSeventyTwoSquare_overlap_one n

structure SpecialAngleSquareIdentities : Prop where
  sqrt_half_square :
    (rawSquare sqrtHalfValue).Equiv (RealRaw.ofRat ((1 : Rat) / 2))
  sqrt_three_square :
    (rawSquare sqrtThreeValue).Equiv (RealRaw.ofRat (3 : Rat))
  sqrt_five_square :
    (rawSquare sqrtFiveValue).Equiv (RealRaw.ofRat (5 : Rat))
  sqrt_three_half_square :
    (rawSquare sqrtThreeHalfValue).Equiv (RealRaw.ofRat ((3 : Rat) / 4))
  sqrt_three_third_square :
    (rawSquare sqrtThreeThirdValue).Equiv (RealRaw.ofRat ((1 : Rat) / 3))
  sqrt_five_half_square :
    (rawSquare sqrtFiveHalfValue).Equiv (RealRaw.ofRat ((5 : Rat) / 4))
  sqrt_five_quarter_square :
    (rawSquare sqrtFiveQuarterValue).Equiv (RealRaw.ofRat ((5 : Rat) / 16))

theorem specialAngleSquareIdentities : SpecialAngleSquareIdentities where
  sqrt_half_square := sqrtHalfValue_square_equiv
  sqrt_three_square := sqrtThreeValue_square_equiv
  sqrt_five_square := sqrtFiveValue_square_equiv
  sqrt_three_half_square := sqrtThreeHalfValue_square_equiv
  sqrt_three_third_square := sqrtThreeThirdValue_square_equiv
  sqrt_five_half_square := sqrtFiveHalfValue_square_equiv
  sqrt_five_quarter_square := sqrtFiveQuarterValue_square_equiv

structure SpecialAngleDisplayedSquareIdentities : Prop where
  cos_forty_five_square :
    (rawSquare cosFortyFiveValue).Equiv (RealRaw.ofRat ((1 : Rat) / 2))
  sin_forty_five_square :
    (rawSquare sinFortyFiveValue).Equiv (RealRaw.ofRat ((1 : Rat) / 2))
  sin_thirty_square :
    (rawSquare sinThirtyValue).Equiv (RealRaw.ofRat ((1 : Rat) / 4))
  cos_thirty_square :
    (rawSquare cosThirtyValue).Equiv (RealRaw.ofRat ((3 : Rat) / 4))
  cos_sixty_square :
    (rawSquare cosSixtyValue).Equiv (RealRaw.ofRat ((1 : Rat) / 4))
  sin_sixty_square :
    (rawSquare sinSixtyValue).Equiv (RealRaw.ofRat ((3 : Rat) / 4))
  tan_zero_square :
    (rawSquare tanZeroValue).Equiv (RealRaw.ofRat (0 : Rat))
  tan_thirty_square :
    (rawSquare tanThirtyValue).Equiv (RealRaw.ofRat ((1 : Rat) / 3))
  tan_forty_five_square :
    (rawSquare tanFortyFiveValue).Equiv (RealRaw.ofRat (1 : Rat))
  tan_sixty_square :
    (rawSquare tanSixtyValue).Equiv (RealRaw.ofRat (3 : Rat))
  tan_thirty_square_cos_thirty_square :
    (RealRaw.scaleRat ((1 : Rat) / 3)
        (rawSquare cosThirtyValue)).Equiv
      (rawSquare sinThirtyValue)
  tan_forty_five_square_cos_forty_five_square :
    (RealRaw.scaleRat (1 : Rat)
        (rawSquare cosFortyFiveValue)).Equiv
      (rawSquare sinFortyFiveValue)
  tan_sixty_square_cos_sixty_square :
    (RealRaw.scaleRat (3 : Rat)
        (rawSquare cosSixtyValue)).Equiv
      (rawSquare sinSixtyValue)
  cos_thirty_six_square :
    (rawSquare cosThirtySixValue).Equiv cosThirtySixSquareValue
  cos_seventy_two_square :
    (rawSquare cosSeventyTwoValue).Equiv cosSeventyTwoSquareValue
  forty_five_pythagorean :
    (rawSquare cosFortyFiveValue + rawSquare sinFortyFiveValue).Equiv
      (RealRaw.ofRat (1 : Rat))
  thirty_pythagorean :
    (rawSquare cosThirtyValue + rawSquare sinThirtyValue).Equiv
      (RealRaw.ofRat (1 : Rat))
  sixty_pythagorean :
    (rawSquare cosSixtyValue + rawSquare sinSixtyValue).Equiv
      (RealRaw.ofRat (1 : Rat))
  thirty_six_pythagorean :
    (rawSquare cosThirtySixValue + sinThirtySixSquareValue).Equiv
      (RealRaw.ofRat (1 : Rat))
  seventy_two_pythagorean :
    (rawSquare cosSeventyTwoValue + sinSeventyTwoSquareValue).Equiv
      (RealRaw.ofRat (1 : Rat))

theorem specialAngleDisplayedSquareIdentities :
    SpecialAngleDisplayedSquareIdentities where
  cos_forty_five_square := cosFortyFiveValue_square_equiv
  sin_forty_five_square := sinFortyFiveValue_square_equiv
  sin_thirty_square := sinThirtyValue_square_equiv
  cos_thirty_square := cosThirtyValue_square_equiv
  cos_sixty_square := cosSixtyValue_square_equiv
  sin_sixty_square := sinSixtyValue_square_equiv
  tan_zero_square := tanZeroValue_square_equiv
  tan_thirty_square := tanThirtyValue_square_equiv
  tan_forty_five_square := tanFortyFiveValue_square_equiv
  tan_sixty_square := tanSixtyValue_square_equiv
  tan_thirty_square_cos_thirty_square :=
    tanThirty_square_scale_cosThirty_square_equiv_sinThirty_square
  tan_forty_five_square_cos_forty_five_square :=
    tanFortyFive_square_scale_cosFortyFive_square_equiv_sinFortyFive_square
  tan_sixty_square_cos_sixty_square :=
    tanSixty_square_scale_cosSixty_square_equiv_sinSixty_square
  cos_thirty_six_square := cosThirtySixValue_square_equiv
  cos_seventy_two_square := cosSeventyTwoValue_square_equiv
  forty_five_pythagorean :=
    cosFortyFive_square_add_sinFortyFive_square_equiv_one
  thirty_pythagorean :=
    cosThirty_square_add_sinThirty_square_equiv_one
  sixty_pythagorean :=
    cosSixty_square_add_sinSixty_square_equiv_one
  thirty_six_pythagorean :=
    cosThirtySix_square_add_sinThirtySixSquare_equiv_one
  seventy_two_pythagorean :=
    cosSeventyTwo_square_add_sinSeventyTwoSquare_equiv_one

def SinSquareValue (C : FunctionRawConstruction) (t : QuarterTurn)
    (value : RealRaw) : Prop :=
  Exists fun ht : C.sinFunctionRaw.definedAt t =>
    (rawSquare (C.sinFunctionRaw.evalRaw t ht)).Equiv value

def TanValue (T : ArctanInverseConstruction) (t : QuarterTurn)
    (value : RealRaw) : Prop :=
  Exists fun ht : T.tangentRaw.definedAt t =>
    (T.tangentRaw.evalRaw t ht).Equiv value

def TanSquareValue (T : ArctanInverseConstruction) (t : QuarterTurn)
    (value : RealRaw) : Prop :=
  Exists fun ht : T.tangentRaw.definedAt t =>
    (rawSquare (T.tangentRaw.evalRaw t ht)).Equiv value

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

/-- Finite tangent values expected of the normalized tangent construction on
the principal branch, with pentagon tangent values recorded by their squares. -/
structure SpecialAngleTangentValueTargets
    (T : ArctanInverseConstruction) : Prop where
  tan_zero : TanValue T 0 tanZeroValue
  tan_thirty : TanValue T ((1 : Rat) / 3) tanThirtyValue
  tan_forty_five : TanValue T ((1 : Rat) / 2) tanFortyFiveValue
  tan_sixty : TanValue T ((2 : Rat) / 3) tanSixtyValue
  tan_thirty_six_square :
    TanSquareValue T ((2 : Rat) / 5) tanThirtySixSquareValue
  tan_seventy_two_square :
    TanSquareValue T ((4 : Rat) / 5) tanSeventyTwoSquareValue

end SpecialAngles

end GeometricTrig

end RationalCircle

end ComputableAnalysis
