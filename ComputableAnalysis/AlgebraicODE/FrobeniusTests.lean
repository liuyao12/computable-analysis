import ComputableAnalysis.AlgebraicODE.Laguerre
import ComputableAnalysis.AlgebraicODE.FrobeniusConvergence

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

/-- All rational inputs in the certified disk, not just a finite prefix. -/
theorem besselZero_factor_valid (x : Rat) (hx : 3 * qabs x ≤ 1 / 2) :
    (besselZero.factorRaw 0 1 x).Valid := by
  apply besselZero.factorRaw_valid 0 1 x (by decide +kernel) (by decide +kernel)
  have hR : besselZero.growthBound 0 = 3 := by decide +kernel
  rwa [hR]

/-- A genuinely signed nonterminating recurrence exercises absolute tails. -/
def signedSeries : Frobenius.Equation := ⟨[1, 1], [0, 1]⟩

example : truncation (signedSeries.coeff 0 1) 5 = [1, -1, 1/2, -1/6, 1/24] := by
  decide +kernel

theorem signedSeries_factor_valid (x : Rat) (hx : 4 * qabs x ≤ 1 / 2) :
    (signedSeries.factorRaw 0 1 x).Valid := by
  apply signedSeries.factorRaw_valid 0 1 x (by decide +kernel) (by decide +kernel)
  have hR : signedSeries.growthBound 0 = 4 := by decide +kernel
  rwa [hR]

/-- Twelve actual finite terms give width 1/1024, on either side of zero. -/
example : ((besselZero.factorRaw 0 1 (1/8)).compute 12).width = 1/1024 := by
  change ((geometricRaw _ _ _).compute 12).width = _
  rw [geometricRaw_width]
  decide +kernel

example : (signedSeries.factorRaw 0 1 (-1/8)).Valid :=
  signedSeries_factor_valid _ (by decide +kernel)

example : (signedSeries.factorRaw 0 0 0).compute 3 = ⟨0, 0⟩ := by decide +kernel

example : (besselZero.factorRaw 0 1 (1/8)).compute 4 = ⟨225/256, 289/256⟩ := by
  decide +kernel

/-- Nonzero and nonintegral exponents are allowed for the factor only. -/
example : ((⟨[0, 1], [1/4, 1]⟩ : Frobenius.Equation).factorRaw (1/2) (-2) (1/10)).Valid :=
  Frobenius.Equation.factorRaw_valid _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : ((⟨[], [-2, 1]⟩ : Frobenius.Equation).factorRaw 2 1 (1/8)).Valid :=
  Frobenius.Equation.factorRaw_valid _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

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
