import ComputableAnalysis.AlgebraicODE.Laguerre

namespace ComputableAnalysis.AlgebraicODE.Tests
open FormalPowerSeries Fuchs

/-- Modified Bessel's equation at exponent zero: a repeated indicial root
still has nonzero positive-index recurrence denominators. -/
def besselZero : Frobenius.Equation := ⟨[1], [0, 0, -1]⟩

theorem besselZero_nonresonant : besselZero.Nonresonant 0 := by
  intro n
  have hn : (0 : Rat) < ((n + 1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  have hi : besselZero.indicial (0 + ((n + 1 : Nat) : Rat)) =
      ((n + 1 : Nat) : Rat) * ((n + 1 : Nat) : Rat) := by
    simp [besselZero, Frobenius.Equation.indicial, ofPolynomial]
    grind
  rw [hi]
  exact Rat.ne_of_gt (Rat.mul_pos hn hn)

example : truncation (besselZero.coeff 0 1) 5 = [1, 0, 1 / 4, 0, 1 / 64] := by
  decide +kernel

/-- This asserts all coefficients, not only the displayed numerical prefix. -/
example : besselZero.IsSolution 0 (besselZero.coeff 0 1) :=
  besselZero.coeff_isSolution 0 1 (by decide +kernel) besselZero_nonresonant

/-- For `x²y''+xy=0` and exponent zero, the degree-one equation is `c₀=0`.
Thus resonance really can obstruct the requested nonzero leading term. -/
theorem resonant_no_nonzero_leading (c : Coeffs) (hc0 : c 0 ≠ 0) :
    ¬ (⟨[], [0, 1]⟩ : Frobenius.Equation).IsSolution 0 c := by
  intro h
  have h1 := h 1
  rw [Frobenius.Equation.residual_split] at h1
  simp [Frobenius.Equation.indicial, Frobenius.Equation.lower,
    ofPolynomial, sumBelow, ratListSum] at h1
  grind

example : Laguerre.polynomial 2 1 1 = [1, -2, 1 / 2] := by decide +kernel
example : Laguerre.polynomial 3 2 1 = [1, -3 / 2, 1 / 2, -1 / 24] := by decide +kernel

/-- Both derivative certificates include the singular point of the normalized ODE. -/
def laguerreFirstOnMinusTwoTwo :=
  Laguerre.firstDerivativeCertificate 3 2 1 (-2) 2 2 (by decide) (by decide) (by decide)
def laguerreSecondOnMinusTwoTwo :=
  Laguerre.secondDerivativeCertificate 3 2 1 (-2) 2 2 (by decide) (by decide) (by decide)

example (m : Nat) :
    ofPolynomial (Laguerre.polynomial m 1 1) m ≠ 0 :=
  (Laguerre.polynomial_exact_degree m (by decide) (by decide)).1

end ComputableAnalysis.AlgebraicODE.Tests
