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

theorem pythagoreanTriple_five_twelve_thirteen :
    (5 : Rat) ^ 2 + 12 ^ 2 = 13 ^ 2 := by
  native_decide

theorem pythagoreanTriple_five_twelve_thirteen_parameter_three_two :
    ((3 : Rat) * 3 - 2 * 2) ^ 2 + (2 * 3 * 2) ^ 2 =
      (3 * 3 + 2 * 2) ^ 2 := by
  simpa using pythagoreanTriple_identity 3 2

theorem pythagoreanTriple_five_twelve_thirteen_certificate :
    (5 : Rat) ^ 2 + 12 ^ 2 = 13 ^ 2 /\
      ((3 : Rat) * 3 - 2 * 2) ^ 2 + (2 * 3 * 2) ^ 2 =
        (3 * 3 + 2 * 2) ^ 2 := by
  exact ⟨pythagoreanTriple_five_twelve_thirteen,
    pythagoreanTriple_five_twelve_thirteen_parameter_three_two⟩

namespace Stage

/-! A non-axis rational-coordinate instance of the orthogonality theorem. -/

theorem rightTriangle_rotated_three_four_six_eight_certificate :
    segmentNormSq origin { x := 3, y := 4 } +
        segmentNormSq origin { x := -8, y := 6 } =
      segmentNormSq { x := 3, y := 4 } { x := -8, y := 6 } /\
      dot { x := 3, y := 4 } { x := -8, y := 6 } = 0 := by
  constructor
  · native_decide
  · native_decide

end Stage

end RationalCircle
end ComputableAnalysis
