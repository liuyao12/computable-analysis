import ComputableAnalysis.Basic

/-!
The finite cancellation behind Taylor's integral remainder.

If F_k' = F_(k+1) and w_k(t) = (b-t)^k/k!, then
w_0' = 0 and w_(k+1)' = -w_k.  Product differentiation of
sum_(k=0)^n w_k F_k therefore leaves just w_n F_(n+1).

This file proves that cancellation at arbitrary finite order, using only
rational arithmetic. It does not yet assert a derivative or integral
identity: those must be obtained from the existing calculus certificates.
-/
namespace ComputableAnalysis.TaylorCancellation

/-- A finite weighted sum; `terms` is the number of terms, not the degree. -/
def sum (w f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sum w f n + w n * f n

/-- Derivatives of the reversed divided powers, represented by their values. -/
def lowered (w : Nat → Rat) : Nat → Rat
  | 0 => 0
  | k + 1 => -w k

/-- After applying the product rule to the weighted derivative chain,
all intermediate terms cancel, at every finite degree. -/
theorem derivative_sum_cancels (w f : Nat → Rat) (n : Nat) :
    sum (lowered w) f (n + 1) +
      sum w (fun k => f (k + 1)) (n + 1) = w n * f (n + 1) := by
  induction n with
  | zero => simp only [sum, lowered]; grind
  | succ n ih =>
      simp only [sum, lowered] at ih ⊢
      grind

/-- A finite Taylor polynomial with rational coefficient approximations. -/
def polynomial (c : Nat → Rat) (h : Rat) (n : Nat) : Rat :=
  sum (fun k => h ^ k) c (n + 1)

/-- Coefficient-error bookkeeping is finite algebra, independent of FTC. -/
theorem sum_error_bound (w f g err : Nat → Rat) (terms : Nat)
    (herror : ∀ k, k < terms → qabs (f k - g k) ≤ err k) :
    qabs (sum w f terms - sum w g terms) ≤
      sum (fun k => qabs (w k)) err terms := by
  induction terms with
  | zero => simp only [sum, Rat.sub_self]; exact qabs_nonneg 0
  | succ n ih =>
    have hp := ih (fun k hk => herror k (by omega))
    have hn := herror n (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_left hn (qabs_nonneg (w n))
    have ht := qabs_add_le (sum w f n - sum w g n) (w n * (f n - g n))
    rw [qabs_mul] at ht
    have hid : sum w f (n+1)-sum w g (n+1) =
        (sum w f n-sum w g n)+w n*(f n-g n) := by
      simp only [sum]; grind
    rw [hid]
    simp only [sum]
    grind only

theorem polynomial_error_bound (c approx err : Nat → Rat) (h : Rat) (n : Nat)
    (herror : ∀ k, k ≤ n → qabs (c k - approx k) ≤ err k) :
    qabs (polynomial c h n - polynomial approx h n) ≤
      sum (fun k => qabs (h ^ k)) err (n + 1) := by
  exact sum_error_bound (fun k => h ^ k) c approx err (n+1)
    (fun k hk => herror k (by omega))

end ComputableAnalysis.TaylorCancellation

