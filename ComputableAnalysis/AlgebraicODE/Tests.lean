import ComputableAnalysis.AlgebraicODE

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

end ComputableAnalysis.AlgebraicODE.Tests
