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

theorem cramer_3_2_1_2_determinant :
    (3 : Rat) * 2 - 2 * 1 = 4 := by
  native_decide

theorem cramer_3_2_1_2_solution :
    (3 : Rat) * 2 + 2 * 3 = 12 /\
      1 * 2 + 2 * 3 = 8 := by
  native_decide

theorem cramer_3_2_1_2_formula :
    (12 * 2 - 2 * 8) / (3 * 2 - 2 * 1) = 2 /\
      (3 * 8 - 12 * 1) / (3 * 2 - 2 * 1) = 3 := by
  native_decide

theorem cramer_3_2_1_2_certificate :
    (3 : Rat) * 2 - 2 * 1 = 4 /\
      (12 * 2 - 2 * 8) / (3 * 2 - 2 * 1) = 2 /\
      (3 * 8 - 12 * 1) / (3 * 2 - 2 * 1) = 3 /\
      ((3 : Rat) * 2 + 2 * 3 = 12 /\ 1 * 2 + 2 * 3 = 8) := by
  exact ⟨cramer_3_2_1_2_determinant,
    cramer_3_2_1_2_formula.1,
    cramer_3_2_1_2_formula.2,
    cramer_3_2_1_2_solution⟩

/-! A signed rational instance with a genuinely nonintegral solution. -/

theorem cramer_signed_determinant :
    (1 : Rat) * 4 - (-2) * 3 = 10 := by
  native_decide

theorem cramer_signed_formula :
    (5 * 4 - (-2) * 6) / ((1 : Rat) * 4 - (-2) * 3) = 16 / 5 /\
      (1 * 6 - 3 * 5) / ((1 : Rat) * 4 - (-2) * 3) = -(9 / 10 : Rat) := by
  native_decide

theorem cramer_signed_solution :
    (1 : Rat) * (16 / 5) + (-2) * (-(9 / 10 : Rat)) = 5 /\
      3 * (16 / 5) + 4 * (-(9 / 10 : Rat)) = 6 := by
  native_decide

theorem cramer_signed_certificate :
    (1 : Rat) * 4 - (-2) * 3 = 10 /\
      (5 * 4 - (-2) * 6) / ((1 : Rat) * 4 - (-2) * 3) = 16 / 5 /\
      (1 * 6 - 3 * 5) / ((1 : Rat) * 4 - (-2) * 3) = -(9 / 10 : Rat) /\
      ((1 : Rat) * (16 / 5) + (-2) * (-(9 / 10 : Rat)) = 5 /\
        3 * (16 / 5) + 4 * (-(9 / 10 : Rat)) = 6) := by
  exact ⟨cramer_signed_determinant, cramer_signed_formula.1,
    cramer_signed_formula.2, cramer_signed_solution⟩

end ComputableAnalysis
