import ComputableAnalysis.RationalCircle

/-!
# A worked unit-circle law-of-cosines certificate

The rational unit points `(3/5,4/5)` and `(-4/5,3/5)` are orthogonal.  Their
squared chord length is therefore `2`, providing a second finite checkpoint
for the squared law of cosines beyond the generic coordinate certificate.
-/

namespace ComputableAnalysis

namespace RationalCircle

namespace Stage

theorem finiteLawOfCosines_unit_orthogonal_certificate :
    let p : PiCirclePoint := { x := 3 / 5, y := 4 / 5 }
    let q : PiCirclePoint := { x := -4 / 5, y := 3 / 5 }
    normSq p = 1 ∧
      normSq q = 1 ∧
      dot p q = 0 ∧
      segmentNormSq p q = 2 ∧
      segmentNormSq p q = normSq p + normSq q - 2 * dot p q := by
  dsimp
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · exact segmentNormSq_law_of_cosines _ _

theorem finiteLawOfCosines_unit_antipodal_certificate :
    let p : PiCirclePoint := { x := 3 / 5, y := 4 / 5 }
    let q : PiCirclePoint := { x := -3 / 5, y := -4 / 5 }
    normSq p = 1 ∧
      normSq q = 1 ∧
      dot p q = -1 ∧
      segmentNormSq p q = 4 ∧
      segmentNormSq p q = normSq p + normSq q - 2 * dot p q := by
  dsimp
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · exact segmentNormSq_law_of_cosines _ _

theorem finiteLawOfCosines_three_four_five_certificate :
    let p : PiCirclePoint := { x := 3, y := 0 }
    let q : PiCirclePoint := { x := 0, y := 4 }
    normSq p = 9 ∧
      normSq q = 16 ∧
      dot p q = 0 ∧
      segmentNormSq p q = 25 ∧
      segmentNormSq p q = normSq p + normSq q - 2 * dot p q := by
  dsimp
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · exact segmentNormSq_law_of_cosines _ _

end Stage

end RationalCircle

end ComputableAnalysis
