import ComputableAnalysis.Basic

/-!
# A rational rectangle isoperimetric certificate

For rectangles, the isoperimetric inequality is an exact rational consequence
of the project's AM--GM square bound.  The general inequality for arbitrary
plane regions remains outside this finite coordinate core.
-/

namespace ComputableAnalysis

def rectanglePerimeter (a b : Rat) : Rat := 2 * (a + b)
def rectangleArea (a b : Rat) : Rat := a * b

theorem rectangle_isoperimetric {a b : Rat} :
    16 * rectangleArea a b ≤ rectanglePerimeter a b ^ 2 := by
  unfold rectangleArea rectanglePerimeter
  have h := am_gm_square_bound a b
  grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
    Rat.add_mul]

theorem rectangle_isoperimetric_gap {a b : Rat} :
    rectanglePerimeter a b ^ 2 - 16 * rectangleArea a b =
      4 * (a - b) ^ 2 := by
  unfold rectangleArea rectanglePerimeter
  grind [Rat.pow_succ, Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_add, Rat.add_mul]

theorem rectangle_isoperimetric_eq_iff {a b : Rat} :
    16 * rectangleArea a b = rectanglePerimeter a b ^ 2 ↔ a = b := by
  unfold rectangleArea rectanglePerimeter
  constructor
  · intro h
    apply am_gm_rational_half_eq_iff.mp
    rw [Rat.div_def]
    grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
      Rat.add_mul, Rat.mul_inv_cancel]
  · intro h
    subst b
    grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
      Rat.add_mul]

theorem rectangle_three_by_four_certificate :
    rectangleArea 3 4 = 12 /\
      rectanglePerimeter 3 4 = 14 /\
      16 * rectangleArea 3 4 ≤ rectanglePerimeter 3 4 ^ 2 := by
  native_decide

theorem rectangle_five_by_twelve_certificate :
    rectangleArea 5 12 = 60 /\
      rectanglePerimeter 5 12 = 34 /\
      16 * rectangleArea 5 12 < rectanglePerimeter 5 12 ^ 2 /\
      rectanglePerimeter 5 12 ^ 2 - 16 * rectangleArea 5 12 = 196 := by
  native_decide

end ComputableAnalysis
