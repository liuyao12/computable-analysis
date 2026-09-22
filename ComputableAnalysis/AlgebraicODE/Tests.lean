import ComputableAnalysis.AlgebraicODE
import ComputableAnalysis.AlgebraicODE.FrobeniusTests
import ComputableAnalysis.AlgebraicODE.FuchsGrowthExamples

namespace ComputableAnalysis.AlgebraicODE.Tests
open Painleve

/-- Both signs in the DLMF parameter convention. -/
example (x : Rat) (hx : x ≠ 0) : II 1 x (-1 / x) (-2 / x ^ 3) := by
  have h := (simple_pole_classification 1 (-1)).mpr
    ⟨by decide, Or.inr (Or.inr rfl)⟩ x hx
  have hm : (2 : Rat) * (-1) = -2 := by grind
  simpa [hm] using h

example (x : Rat) (hx : x ≠ 0) : II (-1) x (1 / x) (2 / x ^ 3) := by
  have h := (simple_pole_classification (-1) 1).mpr
    ⟨rfl, Or.inr (Or.inl rfl)⟩ x hx
  simpa using h

/-- Excludes the tempting but false extension to arbitrary residues. -/
example : ¬ (∀ x : Rat, x ≠ 0 → II (-2) x (2 / x) (4 / x ^ 3)) := by
  intro h
  have h1 := h 1 (by decide)
  simp [II, Rat.pow_succ] at h1
  grind

def negativePoleOnOneTwo : AlgebraicSolutionOn 1 1 2 :=
  poleSolution (-1) 1 2 (Or.inr (Or.inr rfl)) (by decide) (by decide)

def positivePoleOnOneTwo : AlgebraicSolutionOn (-1) 1 2 :=
  poleSolution 1 1 2 (Or.inr (Or.inl rfl)) (by decide) (by decide)

/-- The actual raw residual vanishes for every nonzero rational input. -/
theorem negativePole_represented (x : Rat) (hx : x ≠ 0) :
    (second 1).Holds (fun i => ComplexRaw.ofQComplex (QComplex.ofRat
      (if i.val = 0 then x else if i.val = 1 then -1 / x
       else if i.val = 2 then 1 / x ^ 2 else -2 / x ^ 3))) := by
  apply Equation.holds_of_evalRat_zero
  rw [second_eval]
  have h := (simple_pole_classification 1 (-1)).mpr
    ⟨by decide, Or.inr (Or.inr rfl)⟩ x hx
  simp only [II] at h
  grind

example (p : List Rat) (h : Fuchs.PolynomialSolution (1 / 2) p) :
    ∀ k : Nat, p[k]?.getD 0 = 0 := by
  apply Fuchs.nonintegral_polynomial_zero (1 / 2) p ?_ h
  intro k hk
  cases k with
  | zero => simp at hk; grind
  | succ k =>
      have hs : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) :=
        (Rat.natCast_le_natCast (a := 1) (b := k + 1)).2 (Nat.succ_le_succ (Nat.zero_le k))
      rw [hk] at hs
      have hhalf : ¬ (1 : Rat) ≤ 1 / 2 := by decide +kernel
      exact hhalf hs

/-- A non-singleton series evaluator can be used directly as a constant
solution; its precision schedule refines according to the rational step. -/
def besselConstantSolution (R : Rat) :
    LinearODE.LinearSolution (fun _ => (fun _ _ => 0 : LinearODE.RatMatrix 1)) R :=
  LinearODE.LinearSolution.constant (besselZero.factorRaw 0 1 (1/8))
    (besselZero_factor_valid _ (by decide +kernel))
    (RationalMajorant.halfDecayShift 4) (by
      intro eps n hn
      have hv := besselZero_factor_valid (1/8) (by decide +kernel)
      have hnest := hv.2.1 _ n hn
      have hw := QInterval.width_le_of_contains ⟨hnest.1, hnest.2.2⟩
      apply Rat.le_trans hw
      have hp := besselZero.factorRaw_precision 0 1 (1/8) eps
      have he : (4 : Rat)*qabs 1 = 4 := by decide +kernel
      simpa only [he] using hp) R

theorem besselConstant_growth {a : Rat} (ha : 0 < a) (ha1 : a ≤ 1) :
    LinearODE.NormBound ((besselConstantSolution 1).value a)
      (LinearODE.normCeiling ((besselConstantSolution 1).value 1) 0) := by
  have hg := (besselConstantSolution 1).moderate_growth 0
    (by intro t ht htR j; simp [LinearODE.matrixColumnAbsSum, LinearODE.finiteSum, qabs]; grind)
    ha ha1 (Rat.le_refl (a := 1))
  simpa [Rat.div_def, show (1 : Rat)⁻¹ = 1 by decide +kernel] using hg

example : (((besselConstantSolution 1).value (1/2) 0).compute 4).width = 1/4 := by
  decide +kernel

end ComputableAnalysis.AlgebraicODE.Tests
