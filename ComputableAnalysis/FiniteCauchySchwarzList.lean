import ComputableAnalysis.Basic

/-!
# Finite rational Cauchy--Schwarz certificates

This file contains the finite, executable form of Cauchy--Schwarz needed by
the project.  The vectors are lists of rationals; no completed real line,
limits, or infinite sums occur.
-/

namespace ComputableAnalysis

/-- The finite dot product, with unmatched entries contributing zero. -/
def rationalDot : List Rat → List Rat → Rat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + rationalDot xs ys

/-- The finite sum of coordinate squares. -/
def rationalSumSquares : List Rat → Rat
  | [] => 0
  | x :: xs => x * x + rationalSumSquares xs

theorem rationalSumSquares_nonneg :
    ∀ xs : List Rat, 0 ≤ rationalSumSquares xs
  | [] => by simp [rationalSumSquares]
  | x :: xs => by
      simp only [rationalSumSquares]
      exact Rat.add_nonneg (rat_square_nonneg_basic x) (rationalSumSquares_nonneg xs)

/-- The finite sum of the squared two-by-two minors involving a fixed head. -/
def rationalCrossSquareSum (x : Rat) : List Rat → Rat → List Rat → Rat
  | [], _, _ => 0
  | _, _, [] => 0
  | x' :: xs, y, y' :: ys =>
      (x * y' - x' * y) * (x * y' - x' * y) +
        rationalCrossSquareSum x xs y ys

/-- The sum of all squared two-by-two minors of two aligned lists. -/
def rationalMinorSquareSum : List Rat → List Rat → Rat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
      rationalMinorSquareSum xs ys + rationalCrossSquareSum x xs y ys

theorem rationalCrossSquareSum_nonneg :
    ∀ (x : Rat) (xs : List Rat) (y : Rat) (ys : List Rat),
      0 ≤ rationalCrossSquareSum x xs y ys
  | _, [], _, _ => by simp [rationalCrossSquareSum]
  | x, x' :: xs, y, [] => by simp [rationalCrossSquareSum]
  | x, x' :: xs, y, y' :: ys => by
      simp only [rationalCrossSquareSum]
      exact Rat.add_nonneg (rat_square_nonneg_basic _) 
        (rationalCrossSquareSum_nonneg x xs y ys)

theorem rationalMinorSquareSum_nonneg :
    ∀ xs ys : List Rat, 0 ≤ rationalMinorSquareSum xs ys
  | [], _ => by simp [rationalMinorSquareSum]
  | xs, [] => by
      cases xs with
      | nil => simp [rationalMinorSquareSum]
      | cons x xs => simp [rationalMinorSquareSum]
  | x :: xs, y :: ys => by
      simp only [rationalMinorSquareSum]
      exact Rat.add_nonneg (rationalMinorSquareSum_nonneg xs ys)
        (rationalCrossSquareSum_nonneg x xs y ys)

private theorem rationalCrossSquareSum_expand :
    ∀ (x : Rat) (xs : List Rat) (y : Rat) (ys : List Rat),
      xs.length = ys.length →
      rationalCrossSquareSum x xs y ys =
        x * x * rationalSumSquares ys +
          y * y * rationalSumSquares xs -
            2 * x * y * rationalDot xs ys
  | _, [], _, [], _ => by
      simp only [rationalCrossSquareSum, rationalSumSquares, rationalDot]
      grind
  | x, x' :: xs, y, y' :: ys, hlen => by
      rw [rationalCrossSquareSum,
        rationalCrossSquareSum_expand x xs y ys (Nat.add_right_cancel hlen)]
      simp only [rationalSumSquares, rationalDot]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

private theorem rationalCauchy_residual_identity :
    ∀ {xs ys : List Rat}, xs.length = ys.length →
      rationalSumSquares xs * rationalSumSquares ys -
          rationalDot xs ys * rationalDot xs ys =
        rationalMinorSquareSum xs ys
  | [], [], _ => by
      simp only [rationalSumSquares, rationalDot, rationalMinorSquareSum]
      grind
  | x :: xs, y :: ys, hlen => by
      simp only [rationalSumSquares, rationalDot, rationalMinorSquareSum]
      have htail := rationalCauchy_residual_identity (Nat.add_right_cancel hlen)
      have hcross := rationalCrossSquareSum_expand x xs y ys (Nat.add_right_cancel hlen)
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem rationalDot_cauchy_schwarz_of_length_eq {xs ys : List Rat}
    (hlen : xs.length = ys.length) :
    (rationalDot xs ys) ^ 2 ≤
      rationalSumSquares xs * rationalSumSquares ys := by
  have hres := rationalCauchy_residual_identity hlen
  have hnonneg := rationalMinorSquareSum_nonneg xs ys
  grind [Rat.sub_eq_add_neg, Rat.pow_succ]

end ComputableAnalysis
