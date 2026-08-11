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

end ComputableAnalysis
