import ComputableAnalysis.Basic

namespace ComputableAnalysis

/-! A concrete finite Cramer's-rule certificate for item 97. -/

theorem cramer_2_1_1_3_determinant :
    (2 : Rat) * 3 - 1 * 1 = 5 := by
  native_decide

theorem cramer_2_1_1_3_solution :
    (2 : Rat) * 1 + 1 * 3 = 5 /\
      1 * 1 + 3 * 3 = 10 := by
  native_decide

theorem cramer_2_1_1_3_formula :
    (5 * 3 - 1 * 10) / (2 * 3 - 1 * 1) = 1 /\
      (2 * 10 - 5 * 1) / (2 * 3 - 1 * 1) = 3 := by
  native_decide

theorem cramer_2_1_1_3_certificate :
    (2 : Rat) * 3 - 1 * 1 = 5 /\
      (5 * 3 - 1 * 10) / (2 * 3 - 1 * 1) = 1 /\
      (2 * 10 - 5 * 1) / (2 * 3 - 1 * 1) = 3 /\
      ((2 : Rat) * 1 + 1 * 3 = 5 /\ 1 * 1 + 3 * 3 = 10) := by
  exact ⟨cramer_2_1_1_3_determinant,
    cramer_2_1_1_3_formula.1,
    cramer_2_1_1_3_formula.2,
    cramer_2_1_1_3_solution⟩

end ComputableAnalysis
