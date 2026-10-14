import ComputableAnalysis.ModularForms.RealExponentialOrder
import ComputableAnalysis.ModularForms.RealExponentialCore

/-! The actual entire exponential preserves the represented real axis. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem cmGrowthExponential163_imag_zero :
    (entireExponentialValue cmGrowthExponent163).val.imagPart.Equiv (RealRaw.ofRat 0) := by
  have he := entireExponentialValue_congr cmGrowthExponent163
    ⟨ofRealRaw cmGrowthReal163,ofRealRaw_valid _ cmGrowthReal163_valid⟩ cmGrowthExponent163_real
  exact RealRaw.equiv_trans (imagPart_valid (entireExponentialValue cmGrowthExponent163).property)
    (imagPart_valid (entireExponentialValue _).property) (RealRaw.ofRat_valid _)
    (imagPart_equiv he) (entireExponential_real_imag_zero _ cmGrowthReal163_valid)

theorem cmGrowthExponential163_real_positive :
    (entireExponentialValue cmGrowthExponent163).val.realPart.Pos := by
  have hv := realPart_valid (entireExponentialValue cmGrowthExponent163).property
  obtain ⟨N,hN⟩ := hv.2.2 (⟨1,by decide⟩ : QPos)
  have hw := hN N (Nat.le_refl N)
  have hl := cmGrowthExponential163_lower_twentyFive 0 N
  change (25:Rat) ≤ ((entireExponentialValue cmGrowthExponent163).val.realPart.compute N).hi at hl
  unfold QInterval.width at hw
  refine ⟨N,?_⟩
  change 0 < ((entireExponentialValue cmGrowthExponent163).val.realPart.compute N).lo
  grind only

end ComputableAnalysis.ModularForms
