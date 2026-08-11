import ComputableAnalysis.Series

namespace ComputableAnalysis

/-! A concrete finite certificate for the geometric-series benchmark.
The ratio `1/2` is evaluated at a finite stage, and the exact tail is retained
as a rational error budget.
-/

theorem geometricHalf_stage5_sum :
    Series.geometricSum ((1 : Rat) / 2) 5 = 31 / 16 := by
  native_decide

theorem geometricHalf_stage5_tail :
    2 - Series.geometricSum ((1 : Rat) / 2) 5 = 1 / 16 := by
  rw [geometricHalf_stage5_sum]
  native_decide

theorem geometricHalf_stage5_enclosure :
    Series.geometricSum ((1 : Rat) / 2) 5 <= 2 /\
      2 - Series.geometricSum ((1 : Rat) / 2) 5 <= 1 / 16 := by
  constructor
  · rw [geometricHalf_stage5_sum]
    native_decide
  · rw [geometricHalf_stage5_tail]
    native_decide

theorem geometricHalf_stage10_sum :
    Series.geometricSum ((1 : Rat) / 2) 10 = 1023 / 512 := by
  native_decide

theorem geometricHalf_stage10_tail :
    2 - Series.geometricSum ((1 : Rat) / 2) 10 = 1 / 512 := by
  rw [geometricHalf_stage10_sum]
  native_decide

theorem geometricHalf_stage10_enclosure :
    Series.geometricSum ((1 : Rat) / 2) 10 <= 2 /\
      2 - Series.geometricSum ((1 : Rat) / 2) 10 <= 1 / 512 := by
  constructor
  · rw [geometricHalf_stage10_sum]
    native_decide
  · rw [geometricHalf_stage10_tail]
    native_decide

theorem geometricHalf_stage20_sum :
    Series.geometricSum ((1 : Rat) / 2) 20 = 1048575 / 524288 := by
  native_decide

theorem geometricHalf_stage20_tail :
    2 - Series.geometricSum ((1 : Rat) / 2) 20 = 1 / 524288 := by
  rw [geometricHalf_stage20_sum]
  native_decide

theorem geometricHalf_stage20_enclosure :
    Series.geometricSum ((1 : Rat) / 2) 20 <= 2 /\
      2 - Series.geometricSum ((1 : Rat) / 2) 20 <= 1 / 524288 := by
  constructor
  · rw [geometricHalf_stage20_sum]
    native_decide
  · rw [geometricHalf_stage20_tail]
    native_decide

theorem geometricHalf_stage40_sum :
    Series.geometricSum ((1 : Rat) / 2) 40 =
      1099511627775 / 549755813888 := by
  native_decide

theorem geometricHalf_stage40_tail :
    2 - Series.geometricSum ((1 : Rat) / 2) 40 =
      1 / 549755813888 := by
  rw [geometricHalf_stage40_sum]
  native_decide

theorem geometricHalf_stage40_enclosure :
    Series.geometricSum ((1 : Rat) / 2) 40 <= 2 /\
      2 - Series.geometricSum ((1 : Rat) / 2) 40 <=
        1 / 549755813888 := by
  constructor
  · rw [geometricHalf_stage40_sum]
    native_decide
  · rw [geometricHalf_stage40_tail]
    native_decide

theorem geometricHalf_stage80_sum :
    Series.geometricSum ((1 : Rat) / 2) 80 =
      1208925819614629174706175 / 604462909807314587353088 := by
  native_decide

theorem geometricHalf_stage80_tail :
    2 - Series.geometricSum ((1 : Rat) / 2) 80 =
      1 / 604462909807314587353088 := by
  rw [geometricHalf_stage80_sum]
  native_decide

theorem geometricHalf_stage80_enclosure :
    Series.geometricSum ((1 : Rat) / 2) 80 <= 2 /\
      2 - Series.geometricSum ((1 : Rat) / 2) 80 <=
        1 / 604462909807314587353088 := by
  constructor
  · rw [geometricHalf_stage80_sum]
    native_decide
  · rw [geometricHalf_stage80_tail]
    native_decide

theorem geometricHalf_stage160_sum :
    Series.geometricSum ((1 : Rat) / 2) 160 =
      1461501637330902918203684832716283019655932542975 /
        730750818665451459101842416358141509827966271488 := by
  native_decide

theorem geometricHalf_stage160_tail :
    2 - Series.geometricSum ((1 : Rat) / 2) 160 =
      1 / 730750818665451459101842416358141509827966271488 := by
  rw [geometricHalf_stage160_sum]
  native_decide

theorem geometricHalf_stage160_enclosure :
    Series.geometricSum ((1 : Rat) / 2) 160 <= 2 /\
      2 - Series.geometricSum ((1 : Rat) / 2) 160 <=
        1 / 730750818665451459101842416358141509827966271488 := by
  constructor
  · rw [geometricHalf_stage160_sum]
    native_decide
  · rw [geometricHalf_stage160_tail]
    native_decide

theorem geometricHalf_stage320_sum :
    Series.geometricSum ((1 : Rat) / 2) 320 =
      2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936575 /
        1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288 := by
  native_decide

theorem geometricHalf_stage320_tail :
    2 - Series.geometricSum ((1 : Rat) / 2) 320 =
      1 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288 := by
  rw [geometricHalf_stage320_sum]
  native_decide

theorem geometricHalf_stage320_enclosure :
    Series.geometricSum ((1 : Rat) / 2) 320 <= 2 /\
      2 - Series.geometricSum ((1 : Rat) / 2) 320 <=
        1 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288 := by
  constructor
  · rw [geometricHalf_stage320_sum]
    native_decide
  · rw [geometricHalf_stage320_tail]
    native_decide

theorem geometricHalf_stage640_tail_formula :
    2 - Series.geometricSum ((1 : Rat) / 2) 640 =
      ((1 : Rat) / 2) ^ 639 := by
  native_decide

theorem geometricHalf_stage640_enclosure :
    Series.geometricSum ((1 : Rat) / 2) 640 <= 2 /\
      2 - Series.geometricSum ((1 : Rat) / 2) 640 <=
        ((1 : Rat) / 2) ^ 639 := by
  constructor
  · have h := Series.geometricSum_le_inv_one_sub
      (r := (1 : Rat) / 2) (by native_decide) (by native_decide) 640
    calc
      Series.geometricSum ((1 : Rat) / 2) 640 <=
          1 / (1 - (1 : Rat) / 2) := h
      _ = 2 := by native_decide
  · rw [geometricHalf_stage640_tail_formula]
    exact Rat.le_refl

theorem geometricTwoThirds_stage4_sum :
    Series.geometricSum ((2 : Rat) / 3) 4 = 65 / 27 := by
  native_decide

theorem geometricTwoThirds_stage4_tail_to_three :
    3 - Series.geometricSum ((2 : Rat) / 3) 4 = 16 / 27 := by
  rw [geometricTwoThirds_stage4_sum]
  native_decide

end ComputableAnalysis
