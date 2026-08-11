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

theorem pascal_combination_10_3 :
    FiniteCounting.combination 10 3 = 120 := by
  native_decide

theorem pascal_combination_9_2 :
    FiniteCounting.combination 9 2 = 36 := by
  native_decide

theorem pascal_combination_9_3 :
    FiniteCounting.combination 9 3 = 84 := by
  native_decide

theorem pascal_combination_10_3_recurrence :
    FiniteCounting.combination 10 3 =
      FiniteCounting.combination 9 2 +
        FiniteCounting.combination 9 3 := by
  exact FiniteCounting.combination_pascal 9 2

theorem pascal_combination_10_3_certificate :
    FiniteCounting.combination 10 3 = 120 /\
      FiniteCounting.combination 10 3 =
        FiniteCounting.combination 9 2 +
          FiniteCounting.combination 9 3 := by
  exact ⟨pascal_combination_10_3, pascal_combination_10_3_recurrence⟩

theorem pascal_combination_15_3 :
    FiniteCounting.combination 15 3 = 455 := by
  native_decide

theorem pascal_combination_14_2 :
    FiniteCounting.combination 14 2 = 91 := by
  native_decide

theorem pascal_combination_14_3 :
    FiniteCounting.combination 14 3 = 364 := by
  native_decide

theorem pascal_combination_15_3_recurrence :
    FiniteCounting.combination 15 3 =
      FiniteCounting.combination 14 2 +
        FiniteCounting.combination 14 3 := by
  exact FiniteCounting.combination_pascal 14 2

theorem pascal_combination_15_3_certificate :
    FiniteCounting.combination 15 3 = 455 /\
      FiniteCounting.combination 15 3 =
        FiniteCounting.combination 14 2 +
          FiniteCounting.combination 14 3 := by
  exact ⟨pascal_combination_15_3, pascal_combination_15_3_recurrence⟩

theorem pascal_combination_20_3 :
    FiniteCounting.combination 20 3 = 1140 := by
  native_decide

theorem pascal_combination_19_2 :
    FiniteCounting.combination 19 2 = 171 := by
  native_decide

theorem pascal_combination_19_3 :
    FiniteCounting.combination 19 3 = 969 := by
  native_decide

theorem pascal_combination_20_3_recurrence :
    FiniteCounting.combination 20 3 =
      FiniteCounting.combination 19 2 +
        FiniteCounting.combination 19 3 := by
  exact FiniteCounting.combination_pascal 19 2

theorem pascal_combination_20_3_certificate :
    FiniteCounting.combination 20 3 = 1140 /\
      FiniteCounting.combination 20 3 =
        FiniteCounting.combination 19 2 +
          FiniteCounting.combination 19 3 := by
  exact ⟨pascal_combination_20_3, pascal_combination_20_3_recurrence⟩

theorem pascal_combination_25_3 :
    FiniteCounting.combination 25 3 = 2300 := by
  native_decide

theorem pascal_combination_24_2 :
    FiniteCounting.combination 24 2 = 276 := by
  native_decide

theorem pascal_combination_24_3 :
    FiniteCounting.combination 24 3 = 2024 := by
  native_decide

theorem pascal_combination_25_3_recurrence :
    FiniteCounting.combination 25 3 =
      FiniteCounting.combination 24 2 +
        FiniteCounting.combination 24 3 := by
  exact FiniteCounting.combination_pascal 24 2

theorem pascal_combination_25_3_certificate :
    FiniteCounting.combination 25 3 = 2300 /\
      FiniteCounting.combination 25 3 =
        FiniteCounting.combination 24 2 +
          FiniteCounting.combination 24 3 := by
  exact ⟨pascal_combination_25_3, pascal_combination_25_3_recurrence⟩

theorem pascal_combination_32_3 :
    FiniteCounting.combination 32 3 = 4960 := by
  native_decide

theorem pascal_combination_31_2 :
    FiniteCounting.combination 31 2 = 465 := by
  native_decide

theorem pascal_combination_31_3 :
    FiniteCounting.combination 31 3 = 4495 := by
  native_decide

theorem pascal_combination_32_3_recurrence :
    FiniteCounting.combination 32 3 =
      FiniteCounting.combination 31 2 +
        FiniteCounting.combination 31 3 := by
  exact FiniteCounting.combination_pascal 31 2

theorem pascal_combination_32_3_certificate :
    FiniteCounting.combination 32 3 = 4960 /\
      FiniteCounting.combination 32 3 =
        FiniteCounting.combination 31 2 +
          FiniteCounting.combination 31 3 := by
  exact ⟨pascal_combination_32_3, pascal_combination_32_3_recurrence⟩

end ComputableAnalysis
