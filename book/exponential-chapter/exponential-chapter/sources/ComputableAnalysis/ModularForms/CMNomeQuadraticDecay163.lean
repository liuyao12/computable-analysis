import ComputableAnalysis.ModularForms.RealExponentialQuadraticOrder
import ComputableAnalysis.ModularForms.CMFourierDiscriminant163

/-! Quadratically amplified decay of the actual discriminant-163 nome. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual CM unit exponential has its stronger quadratic lower bound. -/
theorem cmGrowthUnitThirtySixExponential163_lower_five_halves :
    (RealRaw.ofRat (5/2)).Le cmGrowthUnitThirtySixExponential163 := by
  have h := entireExponential_real_rational_quadratic_lower cmGrowthUnitThirtySix163
    cmGrowthUnitThirtySix163_valid cmGrowthUnitThirtySix163_positive 1 (by decide +kernel)
    cmGrowthUnitThirtySix163_lower_one
  rw [show (1:Rat)+1+1*1/2=5/2 by decide +kernel] at h
  exact h

/-- Actual power agreement amplifies the quadratic bound beyond the forty-seventh binary power. -/
theorem cmGrowthExponential163_lower_fortySeven_power :
    (RealRaw.ofRat 140737488355328).Le (entireExponentialValue cmGrowthExponent163).val.realPart := by
  have hb := realFinitePower_lower cmGrowthUnitThirtySixExponential163
    cmGrowthUnitThirtySixExponential163_valid (5/2) (by decide +kernel)
    cmGrowthUnitThirtySixExponential163_lower_five_halves 36
  have hC : (140737488355328:Rat)≤(5/2:Rat)^36 := by decide +kernel
  have hl : (RealRaw.ofRat 140737488355328).Le
      (realFinitePower cmGrowthUnitThirtySixExponential163 36) := by
    intro n m
    have h := hb 0 m
    change (5/2:Rat)^36≤((realFinitePower cmGrowthUnitThirtySixExponential163 36).compute m).hi at h
    exact Rat.le_trans hC h
  have he := ComplexRaw.realPart_equiv (equiv_symm cmGrowthExponential163_thirtySix_power_agreement)
  exact RealRaw.le_trans (realFinitePower_valid _ cmGrowthUnitThirtySixExponential163_valid 36) hl
    (RealRaw.le_of_equiv (realFinitePower_valid _ cmGrowthUnitThirtySixExponential163_valid 36)
      (realPart_valid (entireExponentialValue cmGrowthExponent163).property) he)

/-- The actual CM nome has the quadratically amplified radius. -/
theorem nome_cm163_small_fortySeven_power :
    Small (nome.eval cmScalar163 cmPoint163_upper).val (1/140737488355328) :=
  nome_cm163_small_of_growth 140737488355328 (by decide +kernel) cmGrowthExponential163_lower_fortySeven_power

end ComputableAnalysis.ModularForms
