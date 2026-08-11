import ComputableAnalysis.FiniteCubicSqrtTwoExample

/-!
# A finite quartic with exact and square-root branches

The quartic `x^4 - 3*x^2 + 2` factors as `(x^2 - 1)(x^2 - 2)`.
Its rational roots are `-1` and `1`; the remaining two roots are represented
by the finite positive and negative `sqrt 2` intervals.
-/

namespace ComputableAnalysis

namespace Polynomial

def quarticSqrtTwo : List Rat := [2, 0, -3, 0, 1]

theorem quarticSqrtTwo_factorization (x : Rat) :
    eval quarticSqrtTwo x = (x ^ 2 - 1) * (x ^ 2 - 2) := by
  simp [quarticSqrtTwo, eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem quarticSqrtTwo_exact_roots :
    eval quarticSqrtTwo (-1) = 0 /\ eval quarticSqrtTwo 1 = 0 := by
  native_decide

theorem quarticSqrtTwo_positive_sqrt_interval_bracket :
    eval quarticSqrtTwo (11 / 8) <= 0 /\
      0 <= eval quarticSqrtTwo (23 / 16) := by
  native_decide

theorem quarticSqrtTwo_negative_sqrt_interval_bracket :
    0 <= eval quarticSqrtTwo (-23 / 16) /\
      eval quarticSqrtTwo (-11 / 8) <= 0 := by
  native_decide

theorem quarticSqrtTwo_positive_sqrt_stage24_interval_bracket :
    eval quarticSqrtTwo (11863283 / 8388608) <= 0 /\
      0 <= eval quarticSqrtTwo (23726567 / 16777216) := by
  native_decide

theorem quarticSqrtTwo_negative_sqrt_stage24_interval_bracket :
    0 <= eval quarticSqrtTwo (-23726567 / 16777216) /\
      eval quarticSqrtTwo (-11863283 / 8388608) <= 0 := by
  native_decide

end Polynomial

end ComputableAnalysis
