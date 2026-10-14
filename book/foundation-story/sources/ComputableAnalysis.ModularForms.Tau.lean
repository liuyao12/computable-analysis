import ComputableAnalysis.Basic

/-!
# Formal discriminant coefficients

Integer coefficients of the finite products defining the discriminant.
No analytic convergence or modular transformation law is asserted here.
-/

namespace ComputableAnalysis.ModularForms

/-- A formal integer coefficient sequence; no convergence is implicit. -/
abbrev Coefficients := Nat → Int

/-- Multiplication by the polynomial `1 - q^m`. -/
def subtractShift (m : Nat) (a : Coefficients) : Coefficients :=
  fun n => if m ≤ n then a n - a (n - m) else a n

/-- Multiplication by `(1 - q^m)^r` by finite recursion. -/
def factorPower (m : Nat) : Nat → Coefficients → Coefficients
  | 0, a => a
  | r + 1, a => subtractShift m (factorPower m r a)

/-- The constant polynomial one. -/
def unitCoefficients : Coefficients := fun n => if n = 0 then 1 else 0

/-- Coefficients of the product of the first `N` factors, each to power 24. -/
def discriminantProduct : Nat → Coefficients
  | 0 => unitCoefficients
  | N + 1 => factorPower (N + 1) 24 (discriminantProduct N)

/-- The coefficient of `q^n` in `q ∏ (1-q^m)^24`; the zero coefficient is zero. -/
def tau : Nat → Int
  | 0 => 0
  | n + 1 => discriminantProduct n n

theorem factorPower_below (m r n : Nat) (a : Coefficients) (h : n < m) :
    factorPower m r a n = a n := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [factorPower, subtractShift, Nat.not_le.mpr h, ih]

/-- Factors of degree above the queried coefficient cannot change it. -/
theorem discriminantProduct_stable (n N : Nat) (h : n ≤ N) :
    discriminantProduct N n = discriminantProduct n n := by
  induction N with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      rfl
  | succ N ih =>
      by_cases hn : n ≤ N
      · rw [discriminantProduct, factorPower_below (N + 1) 24 n _ (by omega)]
        exact ih hn
      · have he : n = N + 1 := by omega
        subst n
        rfl

/-- The infinite formal product has an exact finite computation at each degree. -/
theorem tau_eq_finiteProduct (n N : Nat) (h : n ≤ N) :
    tau (n + 1) = discriminantProduct N n := by
  exact (discriminantProduct_stable n N h).symm

@[simp] theorem tau_zero : tau 0 = 0 := rfl
@[simp] theorem tau_one : tau 1 = 1 := rfl

theorem product_constant (N : Nat) : discriminantProduct N 0 = 1 := by
  exact discriminantProduct_stable 0 N (Nat.zero_le N)

end ComputableAnalysis.ModularForms
