import ComputableAnalysis.FormalPowerSeriesAlgebra
import ComputableAnalysis.GeometricSeriesCalculus

/-! Exact binomial arithmetic for the Apéry numbers. -/
namespace ComputableAnalysis.Apery
open FiniteCounting FormalPowerSeries

def choose (n k : Nat) : Rat := (combination n k : Rat)

@[simp] theorem choose_zero (n : Nat) : choose n 0 = 1 := by simp [choose, combination_zero_right]
@[simp] theorem choose_self (n : Nat) : choose n n = 1 := by simp [choose, combination_self]
theorem choose_outside {n k : Nat} (h : n < k) : choose n k = 0 := by
  simp [choose, combination_outside n k h]
theorem choose_pascal (n k : Nat) : choose (n+1) (k+1) = choose n k + choose n (k+1) :=
  combination_rat_pascal n k

theorem choose_column (n k : Nat) :
    ((k : Rat)+1)*choose n (k+1) = ((n : Rat)-k)*choose n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [choose, combination, Rat.natCast_add] <;> grind
  | succ n ih =>
    cases k with
    | zero => simp [choose, combination_one, combination_zero_right]; grind
    | succ k =>
      have h0 := ih k
      have h1 := ih (k+1)
      rw [choose_pascal n (k+1), choose_pascal n k]
      simp only [Rat.natCast_add] at *
      grind only

theorem choose_row (n k : Nat) :
    ((n : Rat)+1-k)*choose (n+1) k = ((n : Rat)+1)*choose n k := by
  cases k with
  | zero => simp; grind
  | succ k =>
    rw [choose_pascal]
    have h := choose_column n k
    simp only [Rat.natCast_add]
    grind only

theorem choose_diagonal (n k : Nat) :
    ((k : Rat)+1)*choose (n+1) (k+1) = ((n : Rat)+1)*choose n k := by
  rw [choose_pascal]
  have h := choose_column n k
  grind only

/-- The integer square root of the binomial summand. -/
def rootTerm (n k : Nat) : Rat := choose n k * choose (n+k) k
/-- `binom(n,k)^2 * binom(n+k,k)^2`, evaluated in rational arithmetic. -/
def term (n k : Nat) : Rat := rootTerm n k ^ 2

theorem rootTerm_row (n k : Nat) :
    ((n : Rat)+1-k)*rootTerm (n+1) k = ((n : Rat)+1+k)*rootTerm n k := by
  have h1 := choose_row n k
  have h2 := choose_row (n+k) k
  rw [show n+k+1=(n+1)+k by omega] at h2
  simp only [Rat.natCast_add] at h2
  unfold rootTerm
  grind only

theorem rootTerm_column (n k : Nat) :
    ((k : Rat)+1)^2*rootTerm n (k+1) =
      ((n : Rat)-k)*((n : Rat)+k+1)*rootTerm n k := by
  have h1 := choose_column n k
  have h2 := choose_diagonal (n+k) k
  rw [show n+k+1=n+(k+1) by omega] at h2
  simp only [Rat.natCast_add] at h2
  simp only [rootTerm, Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  grind only

theorem term_row (n k : Nat) :
    ((n : Rat)+1-k)^2*term (n+1) k = ((n : Rat)+1+k)^2*term n k := by
  have h := rootTerm_row n k
  unfold term
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  grind only

theorem term_column (n k : Nat) :
    ((k : Rat)+1)^4*term n (k+1) =
      ((n : Rat)-k)^2*((n : Rat)+k+1)^2*term n k := by
  have h := rootTerm_column n k
  unfold term
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at *
  grind only

@[simp] theorem term_zero (n : Nat) : term n 0 = 1 := by simp [term, rootTerm, Rat.pow_succ, Rat.pow_zero]
theorem term_outside {n k : Nat} (h : n < k) : term n k = 0 := by
  simp [term, rootTerm, choose_outside h, Rat.pow_succ, Rat.pow_zero]

/-- The finite binomial definition is independent of the differential equation. -/
def number (n : Nat) : Rat := sumBelow (term n) (n+1)

def numberNat (n : Nat) : Nat :=
  ((List.range (n+1)).map (fun k => (combination n k * combination (n+k) k)^2)).sum

theorem number_integral (n : Nat) : number n = (numberNat n : Rat) := by
  unfold number numberNat sumBelow term rootTerm choose
  have hcast (l : List Nat) : ratListSum (l.map (fun (m : Nat) => (m : Rat))) = (l.sum : Rat) := by
    induction l with
    | nil => rfl
    | cons m ms ih => simp [ratListSum, ih, Rat.natCast_add]
  rw [← hcast, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [Rat.natCast_mul, Rat.natCast_pow]

def recurrencePolynomial (n : Rat) : Rat := 34*n^3+51*n^2+27*n+5
/-- Cohen–Zagier's finite telescoping certificate. -/
def certificate (n : Nat) (k : Rat) : Rat :=
  4*(2*(n : Rat)+1)*(k*(2*k+1)-(2*(n : Rat)+1)^2)

private theorem certificate_algebra (n k a b c d : Rat)
    (h1 : (n+1-k)^2*a = (n+1+k)^2*b)
    (h2 : (n+k)^2*c = (n-k)^2*b)
    (h3 : k^4*b = (n+1-k)^2*(n+k)^2*d)
    (hn : n+1-k ≠ 0) (hk : n+k ≠ 0) :
    (n+1)^3*a-(34*n^3+51*n^2+27*n+5)*b+n^3*c =
      4*(2*n+1)*(k*(2*k+1)-(2*n+1)^2)*b -
      4*(2*n+1)*((k-1)*(2*(k-1)+1)-(2*n+1)^2)*d := by
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at *
  grind only

private theorem term_top (n : Nat) :
    ((n : Rat)+1)^2*term (n+1) (n+1) = 4*(2*(n : Rat)+1)^2*term n n := by
  have h1 := choose_diagonal (n+n) n
  have h2 := choose_row (n+n+1) (n+1)
  rw [show n+n+1+1=(n+1)+(n+1) by omega] at h2
  simp only [Rat.natCast_add] at h1 h2
  have hn : (n : Rat)+1 ≠ 0 := by have := Rat.natCast_nonneg (a := n); grind
  have h : ((n : Rat)+1)*choose ((n+1)+(n+1)) (n+1) =
      2*(2*(n : Rat)+1)*choose (n+n) n := by grind only
  simp only [term, rootTerm, choose_self, Rat.one_mul,
    Rat.pow_succ, Rat.pow_zero] at *
  grind only

/-- Pointwise certificate, including both ends of the finite support. -/
theorem term_telescopes (n k : Nat) :
    ((n : Rat)+2)^3*term (n+2) (k+1) - recurrencePolynomial ((n : Rat)+1)*term (n+1) (k+1) +
      ((n : Rat)+1)^3*term n (k+1) =
    certificate (n+1) (k+1)*term (n+1) (k+1) - certificate (n+1) k*term (n+1) k := by
  by_cases hi : k < n+1
  · have h1 := term_row (n+1) (k+1)
    have h2 := term_row n (k+1)
    have h3 := term_column (n+1) k
    have hnk : (k : Rat) < (n : Rat)+1 := by
      have := (Rat.natCast_lt_natCast (a := k) (b := n+1)).mpr hi
      simp only [Rat.natCast_add] at this
      exact this
    have hn := Rat.natCast_nonneg (a := n)
    have hk := Rat.natCast_nonneg (a := k)
    simp only [Rat.natCast_add] at h1 h2 h3
    have h := certificate_algebra ((n : Rat)+1) ((k : Rat)+1)
      (term (n+2) (k+1)) (term (n+1) (k+1)) (term n (k+1)) (term (n+1) k)
    have hh := h (by grind only) (by grind only) (by grind only) (by grind only) (by grind only)
    simp only [certificate, recurrencePolynomial, Rat.natCast_add]
    grind only
  · by_cases he : k = n+1
    · subst k
      have h := term_top (n+1)
      have ho1 := term_outside (n := n+1) (k := n+1+1) (by omega)
      have ho2 := term_outside (n := n) (k := n+1+1) (by omega)
      simp only [certificate, recurrencePolynomial, Rat.natCast_add,
        Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at *
      grind only
    · have ho1 := term_outside (n := n+2) (k := k+1) (by omega)
      have ho2 := term_outside (n := n+1) (k := k+1) (by omega)
      have ho3 := term_outside (n := n) (k := k+1) (by omega)
      have ho4 := term_outside (n := n+1) (k := k) (by omega)
      rw [ho1, ho2, ho3, ho4]
      grind only

private theorem sum_term_telescopes (n N : Nat) :
    ((n : Rat)+2)^3*sumBelow (term (n+2)) (N+1) -
      recurrencePolynomial ((n : Rat)+1)*sumBelow (term (n+1)) (N+1) +
      ((n : Rat)+1)^3*sumBelow (term n) (N+1) =
      certificate (n+1) N*term (n+1) N := by
  induction N with
  | zero =>
    simp only [sumBelow_succ, sumBelow_zero, term_zero, certificate, recurrencePolynomial,
      Rat.natCast_add, Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
    grind only
  | succ N ih =>
    have h := term_telescopes n N
    simp only [sumBelow_succ] at ih ⊢
    simp only [Rat.natCast_add]
    grind only

/-- Apéry's recurrence is a theorem about the finite integer binomial sums. -/
theorem number_recurrence (n : Nat) :
    ((n : Rat)+2)^3*number (n+2) - recurrencePolynomial ((n : Rat)+1)*number (n+1) +
      ((n : Rat)+1)^3*number n = 0 := by
  have h := sum_term_telescopes n (n+2)
  have ho1 := term_outside (n := n+1) (k := n+2) (by omega)
  have ho2 := term_outside (n := n) (k := n+2) (by omega)
  have ho3 := term_outside (n := n) (k := n+1) (by omega)
  change ((n : Rat)+2)^3*sumBelow (term (n+2)) (n+3) -
    recurrencePolynomial ((n : Rat)+1)*sumBelow (term (n+1)) (n+2) +
    ((n : Rat)+1)^3*sumBelow (term n) (n+1) = 0
  rw [show n+2+1=n+3 by omega] at h
  rw [show n+3=(n+2)+1 by omega, sumBelow_succ (term (n+1)),
    sumBelow_succ (term n), sumBelow_succ (term n), ho1, ho2, ho3] at h
  grind only

@[simp] theorem number_zero : number 0 = 1 := by decide +kernel
@[simp] theorem number_one : number 1 = 5 := by decide +kernel

/-- Integrality also supplies positivity without an analytic interpretation. -/
theorem number_nonneg (n : Nat) : 0 ≤ number n := by
  rw [number_integral]
  exact Rat.natCast_nonneg

/-- A deliberately coarse rational majorant suffices for certified evaluation. -/
theorem number_growth (n : Nat) : qabs (number n) ≤ (64 : Rat)^n := by
  rw [qabs_eq_self_of_nonneg (number_nonneg n)]
  have step (n : Nat) (ih : number (n+1) ≤ (64 : Rat)^(n+1)) :
      number (n+2) ≤ (64 : Rat)^(n+2) := by
    have hr := number_recurrence n
    have h0 := number_nonneg n
    have h1 := number_nonneg (n+1)
    have hn := Rat.natCast_nonneg (a := n)
    have hp : recurrencePolynomial ((n : Rat)+1) ≤ 64*((n : Rat)+2)^3 := by
      have hn2 := Rat.pow_nonneg (n := 2) hn
      have hn3 := Rat.pow_nonneg (n := 3) hn
      simp only [recurrencePolynomial, Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at *
      grind only
    have hc : 0 < ((n : Rat)+2)^3 := Rat.pow_pos (by grind)
    have hmul := Rat.mul_le_mul_of_nonneg_right hp h1
    have hm2 := Rat.mul_le_mul_of_nonneg_left ih (Rat.le_of_lt hc)
    have ht := Rat.mul_nonneg (Rat.pow_nonneg (n := 3) (by grind : 0 ≤ (n : Rat)+1)) h0
    have hh : ((n : Rat)+2)^3*number (n+2) ≤ ((n : Rat)+2)^3*(64^(n+1)*64) := by
      grind only
    rw [show n+2=(n+1)+1 by omega, Rat.pow_succ]
    exact Rat.le_of_mul_le_mul_left hh hc
  have both (m : Nat) : number m ≤ (64 : Rat)^m ∧ number (m+1) ≤ (64 : Rat)^(m+1) := by
    induction m with
    | zero => rw [number_zero, number_one]; constructor <;> decide +kernel
    | succ m ih => exact ⟨ih.2, step m ih.2⟩
  exact (both n).1

end ComputableAnalysis.Apery
