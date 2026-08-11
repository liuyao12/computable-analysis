import ComputableAnalysis.RationalCircle

namespace ComputableAnalysis
namespace RationalCircle

/-! A concrete scaled Pythagorean-triple certificate for item 23. -/

theorem pythagoreanTriple_six_eight_ten :
    (6 : Rat) ^ 2 + 8 ^ 2 = 10 ^ 2 := by
  native_decide

theorem pythagoreanTriple_parameter_two_one :
    ((2 : Rat) * 2 - 1 * 1) ^ 2 + (2 * 2 * 1) ^ 2 =
      (2 * 2 + 1 * 1) ^ 2 := by
  simpa using pythagoreanTriple_identity 2 1

theorem pythagoreanTriple_six_eight_ten_certificate :
    (6 : Rat) ^ 2 + 8 ^ 2 = 10 ^ 2 /\
      ((2 : Rat) * 2 - 1 * 1) ^ 2 + (2 * 2 * 1) ^ 2 =
        (2 * 2 + 1 * 1) ^ 2 := by
  exact ⟨pythagoreanTriple_six_eight_ten,
    pythagoreanTriple_parameter_two_one⟩

end RationalCircle
end ComputableAnalysis
