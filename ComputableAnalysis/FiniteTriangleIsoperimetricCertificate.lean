import ComputableAnalysis.RationalCircle

namespace ComputableAnalysis

namespace RationalCircle

/-!
Square-root-free triangle isoperimetric core.

The sharp Euclidean theorem is not assumed.  For rational side data satisfying
the four Heron factors' sign conditions, AM--GM gives a reusable perimeter
bound on the Heron product.  Since the product is the squared area, this is a
finite certificate for item 43 in the project's computable style.
-/

theorem triangle_isoperimetric_heron_bound {a b c : Rat}
    (h1 : 0 ≤ a + b + c) (h2 : 0 ≤ -a + b + c)
    (h3 : 0 ≤ a - b + c) (h4 : 0 ≤ a + b - c) :
    256 * heronProduct a b c ≤ (a + b + c) ^ 4 := by
  have h := am_gm_four (a := a + b + c) (b := -a + b + c)
    (c := a - b + c) (d := a + b - c) h1 h2 h3 h4
  have hsum : ((a + b + c) + (-a + b + c) +
      (a - b + c) + (a + b - c)) / 4 = (a + b + c) / 2 := by
    grind [Rat.div_def, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]
  rw [hsum] at h
  calc
    256 * heronProduct a b c =
        16 * ((a + b + c) * (-a + b + c) *
          (a - b + c) * (a + b - c)) := by
            simp [heronProduct, Rat.div_def]
            grind [Rat.mul_assoc, Rat.mul_comm]
    _ ≤ 16 * ((a + b + c) / 2) ^ 4 := by
      exact Rat.mul_le_mul_of_nonneg_left h (by native_decide)
    _ = (a + b + c) ^ 4 := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ, Rat.mul_inv_cancel]

theorem triangle_isoperimetric_345_certificate :
    256 * heronProduct 3 4 5 ≤ (3 + 4 + 5 : Rat) ^ 4 := by
  apply triangle_isoperimetric_heron_bound <;> native_decide

end RationalCircle

end ComputableAnalysis
