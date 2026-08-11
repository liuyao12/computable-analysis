import ComputableAnalysis.FiniteSqrtTwoBisectionExample
import ComputableAnalysis.Polynomial

/-!
# A finite cubic with a `sqrt 2` residual branch

The cubic `x^3 - x^2 - 2*x + 2` factors as `(x - 1)(x^2 - 2)`.
Its rational root is exact, while the two remaining roots are represented by
the finite rational enclosure already certified for `sqrt 2`.
-/

namespace ComputableAnalysis

namespace Polynomial

def cubicSqrtTwo : List Rat := [2, -2, -1, 1]

theorem cubicSqrtTwo_factorization (x : Rat) :
    eval cubicSqrtTwo x = (x - 1) * (x ^ 2 - 2) := by
  simp [cubicSqrtTwo, eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem cubicSqrtTwo_one_root :
    eval cubicSqrtTwo 1 = 0 := by
  native_decide

theorem cubicSqrtTwo_sqrtTwo_interval_bracket :
    eval cubicSqrtTwo (11 / 8) <= 0 /\
      0 <= eval cubicSqrtTwo (23 / 16) := by
  native_decide

theorem cubicSqrtTwo_bracket_matches_sqrtTwo_stage4 :
    (11 / 8 : Rat) < 23 / 16 /\
      (11 / 8 : Rat) ^ 2 <= 2 /\
      2 <= (23 / 16 : Rat) ^ 2 := by
  native_decide

theorem cubicSqrtTwo_sqrtTwo_stage24_interval_bracket :
    eval cubicSqrtTwo (11863283 / 8388608) <= 0 /\
      0 <= eval cubicSqrtTwo (23726567 / 16777216) := by
  native_decide

theorem cubicSqrtTwo_bracket_matches_sqrtTwo_stage24 :
    (11863283 / 8388608 : Rat) < 23726567 / 16777216 /\
      (11863283 / 8388608 : Rat) ^ 2 <= 2 /\
      2 <= (23726567 / 16777216 : Rat) ^ 2 := by
  native_decide

end Polynomial

end ComputableAnalysis
