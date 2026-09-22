import ComputableAnalysis.FormalPowerSeriesAlgebra
import ComputableAnalysis.FinitePolynomialCalculus

/-! Finite coefficient identities connected to the existing polynomial
runtime and its two-sided finite-difference derivative certificates. -/
namespace ComputableAnalysis.FormalPowerSeries
open FinitePolynomial

theorem taylorPrefix_eq_sumBelow (c : Coeffs) (N : Nat) (x : Rat) :
    taylorPrefix c N x = sumBelow (fun k => c k * x ^ k) N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [taylorPrefix_succ, sumBelow_succ, ih]

theorem polynomial_eval_append (p q : List Rat) (x : Rat) :
    Polynomial.eval (p ++ q) x =
      Polynomial.eval p x + x ^ p.length * Polynomial.eval q x := by
  induction p with
  | nil => simp [Polynomial.eval]; grind
  | cons a p ih =>
      change a + x * Polynomial.eval (p ++ q) x =
        (a + x * Polynomial.eval p x) + x ^ (p.length + 1) * Polynomial.eval q x
      rw [ih, Rat.pow_succ]
      grind

/-- The certified Taylor evaluator agrees with the executable Horner list evaluator. -/
theorem eval_truncation (c : Coeffs) (N : Nat) (x : Rat) :
    Polynomial.eval (truncation c N) x = taylorPrefix c N x := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hp : truncation c (N + 1) = truncation c N ++ [c N] := by
        simp [truncation, List.range_succ, List.map_append]
      rw [hp, polynomial_eval_append, ih, taylorPrefix_succ]
      simp only [truncation, List.length_map, List.length_range, Polynomial.eval,
        List.foldr_cons, List.foldr_nil]
      grind

theorem taylorPrefix_congr_below {c d : Coeffs} {N : Nat}
    (h : ∀ k, k < N → c k = d k) (x : Rat) :
    taylorPrefix c N x = taylorPrefix d N x := by
  rw [taylorPrefix_eq_sumBelow, taylorPrefix_eq_sumBelow]
  apply sumBelow_congr
  intro k hk
  rw [h k hk]

theorem taylorPrefix_add (c d : Coeffs) (N : Nat) (x : Rat) :
    taylorPrefix (fun k => c k + d k) N x = taylorPrefix c N x + taylorPrefix d N x := by
  simp only [taylorPrefix_eq_sumBelow]
  rw [← sumBelow_add]
  apply sumBelow_congr
  intro k _
  grind

theorem taylorPrefix_scale (a : Rat) (c : Coeffs) (N : Nat) (x : Rat) :
    taylorPrefix (fun k => a * c k) N x = a * taylorPrefix c N x := by
  simp only [taylorPrefix_eq_sumBelow]
  rw [← sumBelow_mul]
  apply sumBelow_congr
  intro k _
  grind

theorem taylorPrefix_zero (N : Nat) (x : Rat) :
    taylorPrefix (fun _ => 0) N x = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [taylorPrefix_succ, ih]; grind

theorem taylorPrefix_mulX_succ (c : Coeffs) (N : Nat) (x : Rat) :
    taylorPrefix (mulX c) (N + 1) x = x * taylorPrefix c N x := by
  induction N with
  | zero => simp [taylorPrefix, integratedTaylorPrefix, mulX]; grind
  | succ N ih =>
      rw [taylorPrefix_succ, ih, taylorPrefix_succ]
      simp only [mulX, Rat.pow_succ]
      grind

/-- A zero boundary coefficient lets multiplication by `x` use the same cutoff. -/
theorem taylorPrefix_mulX (c : Coeffs) (N : Nat) (x : Rat)
    (hboundary : c (N - 1) = 0) :
    taylorPrefix (mulX c) N x = x * taylorPrefix c N x := by
  cases N with
  | zero => simp [taylorPrefix]
  | succ N =>
      rw [taylorPrefix_mulX_succ, taylorPrefix_succ]
      have hN : c N = 0 := by simpa using hboundary
      rw [hN]
      grind

/-- If the first omitted coefficient vanishes, the finite polynomial's
actual derivative is the coefficient shift with the same cutoff. -/
theorem taylorPrefixShift_eq_of_boundary (c : Coeffs) (N : Nat)
    (hboundary : c N = 0) :
    taylorPrefixShift c N = taylorPrefix (coefficientShift c) N := by
  funext x
  cases N with
  | zero => rfl
  | succ N =>
      rw [taylorPrefixShift, ← taylorPrefix_eq_taylorDerivativePrefix,
        taylorPrefix_succ]
      simp only [coefficientShift, hboundary]
      grind

def polynomialDerivativeCertificate (c : Coeffs) (N : Nat) (hboundary : c N = 0)
    (a b C : Rat) (hleft : -C ≤ a) (hright : b ≤ C) (hC : 1 ≤ C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (taylorPrefix c N) a b)
      (FunctionOnInterval.exactRat (taylorPrefix (coefficientShift c) N) a b) := by
  have h := taylorPrefix_hasDerivativeOnInterval c N a b C hleft hright hC
  rw [taylorPrefixShift_eq_of_boundary c N hboundary] at h
  exact h

end ComputableAnalysis.FormalPowerSeries
