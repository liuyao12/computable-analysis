import ComputableAnalysis.Basic

/-!
# A worked finite Pascal certificate

The coefficient `C(8,3)` is evaluated through the project's finite Pascal
recurrence and checked against its two predecessor coefficients.
-/

namespace ComputableAnalysis

theorem pascal_combination_8_3 :
    FiniteCounting.combination 8 3 = 56 := by
  native_decide

theorem pascal_combination_7_2 :
    FiniteCounting.combination 7 2 = 21 := by
  native_decide

theorem pascal_combination_7_3 :
    FiniteCounting.combination 7 3 = 35 := by
  native_decide

theorem pascal_combination_8_3_recurrence :
    FiniteCounting.combination 8 3 =
      FiniteCounting.combination 7 2 +
        FiniteCounting.combination 7 3 := by
  exact FiniteCounting.combination_pascal 7 2

theorem pascal_combination_8_3_certificate :
    FiniteCounting.combination 8 3 = 56 ∧
      FiniteCounting.combination 8 3 =
        FiniteCounting.combination 7 2 +
          FiniteCounting.combination 7 3 := by
  exact ⟨pascal_combination_8_3, pascal_combination_8_3_recurrence⟩

end ComputableAnalysis
