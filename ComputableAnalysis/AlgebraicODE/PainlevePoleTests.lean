import ComputableAnalysis.AlgebraicODE.PainlevePole

namespace ComputableAnalysis.AlgebraicODE.Tests
open FormalPowerSeries Painleve

/-- A nonzero resonant parameter survives; the subsequent coefficient is computed. -/
example : Laurent.coeff 10 3 4 = -1 ∧ Laurent.coeff 10 3 5 = -1/6 ∧
    Laurent.coeff 10 3 6 = 3 ∧ Laurent.coeff 10 3 7 = 0 ∧
    Laurent.coeff 10 3 8 = 1/3 := by decide +kernel

/-- The nonlinear resonance test actually excludes equations. -/
theorem quadratic_forcing_obstruction :
    ¬ ∃ c : Coeffs, Laurent.IsSolution (ofPolynomial [0, 0, 1]) c ∧ c 0 ≠ 0 := by
  intro ⟨c, h, hc⟩
  have h0 := Laurent.leading_coefficient h hc
  have hr := (Laurent.resonance_obstruction h h0).2.2.2.2.2
  have hf : ofPolynomial [0, 0, 1] 2 = 1 := by decide +kernel
  rw [hf] at hr
  exact (by decide : (1 : Rat) ≠ 0) hr

/-- Positive and negative local coordinates both have valid computations. -/
example : (Pole.value 10 3 (1/2)).Valid ∧ (Pole.value 10 3 (-1/2)).Valid :=
  ⟨Pole.value_valid 10 3 (by decide +kernel), Pole.value_valid 10 3 (by decide +kernel)⟩

/-- This is an infinite series evaluator, with a non-singleton certified box. -/
example : ((Pole.factor 0 0 (1/2)).compute 12).width = 1/1024 := by
  change ((geometricRaw _ 1 _).compute 12).width = _
  rw [geometricRaw_width]
  decide +kernel

/-- The pole bound applies to actual computed endpoints at negative inputs. -/
example : 1/2 ≤ (Pole.radius 10 3*(-1/2))^2 * ((Pole.value 10 3 (-1/2)).compute 8).lo :=
  (Pole.double_pole_bounds 10 3 (by decide +kernel) (by decide +kernel) (by decide : 2 ≤ 8)).1

/-- A concrete output precision makes every selection of the three boxes
satisfy the regularized nonlinear equation within the requested tolerance. -/
theorem painleve_box_equation {u v w : Rat}
    (hu : InBox u ((Pole.factor 0 0 (1/2)).compute 12))
    (hv : InBox v ((Pole.firstDerivative 0 0 (1/2)).compute 12))
    (hw : InBox w ((Pole.secondDerivative 0 0 (1/2)).compute 12)) :
    qabs ((1/2)^2*w-4*(1/2)*v+6*u-6*u^2-
      (0*Pole.radius 0 0^4*(1/2)^4+Pole.radius 0 0^5*(1/2)^5)) ≤ 1/20 := by
  have h := Pole.equation_error 0 0 (by decide +kernel : qabs ((1 : Rat)/2) ≤ 1) 12 hu hv hw
  exact Rat.le_trans h (by decide +kernel)

end ComputableAnalysis.AlgebraicODE.Tests
