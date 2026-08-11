import ComputableAnalysis.Pi

namespace ComputableAnalysis

/-! A concrete finite enclosure produced by the Leibniz pi evaluator.

The statement is intentionally stage-indexed and rational: it records what
the executable alternating-sum algorithm proves at stage 10, without treating
the limiting pi value as an attained infinite sum.
-/

theorem piLeibniz_stage10_enclosure :
    (3 : Rat) <= (piLeibniz.compute 10).lo /\
      (piLeibniz.compute 10).hi <= 16 / 5 := by
  native_decide

theorem piLeibniz_stage10_width :
    (piLeibniz.compute 10).width <= 1 / 10 := by
  native_decide

theorem piLeibniz_stage20_enclosure :
    (3 : Rat) <= (piLeibniz.compute 20).lo /\
      (piLeibniz.compute 20).hi <= 16 / 5 := by
  native_decide

theorem piLeibniz_stage20_width :
    (piLeibniz.compute 20).width <= 1 / 20 := by
  native_decide

theorem piLeibniz_stage40_enclosure :
    (3 : Rat) <= (piLeibniz.compute 40).lo /\
      (piLeibniz.compute 40).hi <= 16 / 5 := by
  native_decide

theorem piLeibniz_stage40_width :
    (piLeibniz.compute 40).width <= 1 / 40 := by
  native_decide

theorem piLeibniz_stage80_enclosure :
    (3 : Rat) <= (piLeibniz.compute 80).lo /\
      (piLeibniz.compute 80).hi <= 16 / 5 := by
  native_decide

theorem piLeibniz_stage80_width :
    (piLeibniz.compute 80).width <= 1 / 80 := by
  native_decide

theorem piLeibniz_stage160_enclosure :
    (3 : Rat) <= (piLeibniz.compute 160).lo /\
      (piLeibniz.compute 160).hi <= 16 / 5 := by
  native_decide

theorem piLeibniz_stage160_width :
    (piLeibniz.compute 160).width <= 1 / 160 := by
  native_decide

theorem piLeibniz_stage320_enclosure :
    (3 : Rat) <= (piLeibniz.compute 320).lo /\
      (piLeibniz.compute 320).hi <= 16 / 5 := by
  native_decide

theorem piLeibniz_stage320_width :
    (piLeibniz.compute 320).width <= 1 / 320 := by
  native_decide

theorem piLeibniz_stage640_enclosure :
    (3 : Rat) <= (piLeibniz.compute 640).lo /\
      (piLeibniz.compute 640).hi <= 16 / 5 := by
  native_decide

theorem piLeibniz_stage640_width :
    (piLeibniz.compute 640).width <= 1 / 640 := by
  native_decide

end ComputableAnalysis
