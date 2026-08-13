import ComputableAnalysis.Basic

/-!
# Reusable finite decimal divisibility interface

The digit-sum algorithm is a terminating decimal computation.  Its residue
theorem gives the project-native form of the divisibility-by-three test for
every natural input.
-/

namespace ComputableAnalysis

theorem decimalDigitSum_divisibility_certificate (n : Nat) :
    (3 ∣ n ↔ 3 ∣ decimalDigitSum n) ∧
      decimalDigitSum n % 3 = n % 3 := by
  exact ⟨three_dvd_iff_decimalDigitSum_dvd n,
    decimalDigitSum_mod_three n⟩

theorem decimalDigitSum_divisible_by_three_iff (n : Nat) :
    3 ∣ n ↔ decimalDigitSum n % 3 = 0 := by
  rw [three_dvd_iff_decimalDigitSum_dvd]
  exact Nat.dvd_iff_mod_eq_zero

end ComputableAnalysis
