import ComputableAnalysis.Basic

/-!
# A worked finite Cauchy--Schwarz certificate

The rational vectors `(1,2)` and `(2,4)` are proportional, so the
two-coordinate Cauchy--Schwarz inequality is attained exactly.  Both the
numerical equality and the project's equality criterion are recorded.
-/

namespace ComputableAnalysis

theorem cauchy_schwarz_2d_example_equality :
    (1 * 2 + 2 * 4 : Rat) ^ 2 =
      (1 * 1 + 2 * 2) * (2 * 2 + 4 * 4) := by
  native_decide

theorem cauchy_schwarz_2d_example_proportional :
    (1 : Rat) * 4 = 2 * 2 := by
  native_decide

theorem cauchy_schwarz_2d_example_certificate :
    (1 * 2 + 2 * 4 : Rat) ^ 2 <=
        (1 * 1 + 2 * 2) * (2 * 2 + 4 * 4) ∧
      ((1 * 2 + 2 * 4 : Rat) ^ 2 =
        (1 * 1 + 2 * 2) * (2 * 2 + 4 * 4)) := by
  exact ⟨cauchy_schwarz_2d 1 2 2 4,
    cauchy_schwarz_2d_example_equality⟩

end ComputableAnalysis
